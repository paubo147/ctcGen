from lxml import etree as ET
import re
import os

from CtcTypes import GroundType, DerivedType, SequenceType, StructType, EnumType, ClassNode, AttrNode
from TagFinder import findTag

import Util
import Annotation_parser

class ParserResult:
    def __init__(self):
        self.classes={}
        self.pc_relations=[]
        self.rootClass=None
        self.paths=[]

        self.stringPresent=False
        self.dataTypes={}
        self.delimiter={}
        
        self.solver_cmd=[]

        self.boundaries={}
        self.solver_tokens={}

        self.paths=[]

        self.implicit_types=[] #those which will be removed from the annotation file
        


    def finish(self):
        for c in self.classes.values():
            if len(c.parents) == 0:
                if self.rootClass==None:
                    self.rootClass = c
                    self.paths=c.paths()
                else:
                    print "MORE ROOT CLASSES FOUND"
        
    def addSolverToken(self, n, v):
        self.solver_tokens[n]=v


    def stringIsPresent(self):
        self.stringPresent=True
        
    def addDelimiter(self, typ, delimiter):
        self.delimiter[typ]=delimiter

    def addDataType(self, name, dt):
        self.dataTypes[name]=dt

    def addClass(self, bb):
        self.classes[bb.name]=bb

    def addPCRelation(self, p, c):
        self.pc_relations.append((p,c))
    
    def addSolverSettings(self, cmd, args):
        self.solver_cmd=[cmd]+args

    def getNumberOfTestCases(self):
        return sum(x.getNumberOfTestCases() for x in self.classes.values())


def checkSettings(attribute, a):
    if a.find("filter") is not None:
        attribute["filter"]=a.find("filter").text
    if a.find("mandatory") is not None:
        attribute["mandatory"]="true"

    if a.find("readOnly") is not None:
        attribute["readOnly"]="true"

    if a.find("restricted") is not None:
        attribute["restricted"]="true"

    if a.find("isNillable") is not None:
        attribute["isNillable"]="true"

    if a.find("key") is not None:
        attribute["key"]="true"
    
    #CLASS ATTRIBUTES
    if a.find("dependenciesScript") is not None:
        attribute["dependenciesScript"]=a.find("dependenciesScript").text
    if a.find("root") is not None:
        attribute["root"]="true"
    if a.find("systemCreated") is not None:
        attribute["systemCreated"]="true"


#buildingBlocks={}
#annotatedTypes={}
#oldNewMapping={}

def registerDataType(annotations, p, typekey, dtName, mimName, name, func_obj):
    dat=p.dataTypes.get(typekey, None)
 
    if typekey in ("string", "boolean") or "int" in typekey:
        if dat is None:
            #            dat=p.xml2SMT[typekey] 
            if "bb_"+typekey in annotations:
                (n,r)=Util.getNameRange(typekey)
                dat=GroundType(n,typekey, r)
                dat.smtType=annotations["bb_"+typekey]["smtType"]
                dat.id_type=annotations["bb_"+typekey]["type"]
                p.addDataType(n, dat)
            if dat is None:
                raise Exception("Parser.registerDataType(): GroundDatatype {0} not found in parse object".format(typekey))
        
        func_obj(name, dat)
        #that is the point for ranges
        if typekey=="string":
            p.stringIsPresent()
    elif typekey == "derivedDataTypeRef":
        dat=p.dataTypes.get(dtName, None)
        if dat is None:
            dat=DerivedType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey =="enumRef":
        dat=p.dataTypes.get(dtName, None)
        if dat is None:
            dat=EnumType(dtName,mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey == "structRef":
        dat=p.dataTypes.get(dtName, None)
        if dat is None:
            dat=StructType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey == "sequence":
        dat=p.dataTypes.get(dtName, None)
        if dat is None:
            dat=SequenceType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey == "moRef":
        dat=p.dataTypes.get("uint8", None)
        if dat is None:
            (n,r)=Util.getNameRange("uint8")
            dat=GroundType(n, "uint8", r)
            dat.smtType="Int"
            dat.id_type="INT"
            p.addDataType(n, dat)
        func_obj(name, dat)
    else:
        raise Exception("Parser.registerDataType(): No source code for datatype {0} {1}".format(typekey, dat))



def parseAttributes(p, bb, xml, annotations):
    for a in xml.findall("attribute"):
        an=AttrNode(a.get("name"))
        if a.find("description") is not None:
            an.description=a.find("description").text

        checkSettings(an, a)
            
        #TYPE CHECKS
        dt=a.find("dataType")
        typekey=list(dt)[0].tag
        dataTypeName=None
        if dt[0] is not None:
            dataTypeName=dt[0].get("name")

        mimName=None
        if dt[0] is not None and dt[0].find("mimName") is not None:
            mimName=dt[0].find("mimName").text

        if "key" not in an:
            registerDataType(annotations, p, typekey, dataTypeName, mimName, None, an.setDataType)
        else:
            registerDataType(annotations, p, "int16", dataTypeName, mimName, None, an.setDataType)

        if dt[0].find("range"):
            print "ADDITIONAL RANGE FOR", a.get("name"), "NOT TAKEN INTO ACCOUNT"

        if dt[0].find("defaultValue") is not None:
            an.defaultValue=dt[0].find("defaultValue").text

        #if dt[0].find("defaultValue") is not None:
        #    an["defaultValue"]=list(dt)[0].find("defaultValue").text

        #if typekey in validValues:
        #    an["validValues"]=validValues[typekey]

        bb.addAttribute(an)
        

def parseClasses(p, mim, annotations):
    for cls in mim.findall("class"):
        bb=ClassNode(cls.get("name"), mim.get("name"))
        parseAttributes(p, bb, cls, annotations)
        checkSettings(bb, cls)
        p.addClass(bb)
        #classes[bb.name]=bb

def parsePCRelationship(mim, p, containment):
    parent = containment.find("parent")
    if parent is not None:
        pclas = parent.find("hasClass")
        
    child = containment.find("child")
    if child is not None:
        cclas = child.find("hasClass")

    assert cclas is not None and pclas is not None
    if pclas.get("name") in p.classes  and cclas.get("name") in p.classes:
        
        parent_bb=p.classes[pclas.get("name")]
        child_bb=p.classes[cclas.get("name")]
        child_bb.addParent(parent_bb)
        parent_bb.addChild(child_bb)
        p.addPCRelation(parent_bb, child_bb)




def parseInterMimRelationships(p, assoc):
    """Parses bidirectional associations
    input:
          -assoc  'biDirectionalAssociation' xml-element
          -p      parse-object
    """
    pass


def parseRelationships(p, model, mim):
    """Parses all kind of relationships. 
    This includes parent-child as well as bidirectional associations.
    Invariant: all classes have to be stored at the parse-object already
    input:
          -model   xml-file
          -p       parse-object
    """
    assert p.classes
    for rel in model.iter("relationship"):
        containment=rel.find("containment")
        if containment is not None:
            parsePCRelationship(mim, p, containment)
        assoc = rel.find("biDirectionalAssociation")
        if assoc is not None:
            parseInterMimRelationships(p, assoc)

    
    

def manageAnnotatedDataTypes(p, annotations, typ, name, bt, ranges):
    
    if "dt_"+typ in annotations:
        if typ in p.dataTypes:
            dt=p.dataTypes[typ]
        else:
            dt=StructType(typ, "annotated", True)
            #print "DT: ADDING {0} TO PARSER".format(typ)
            p.addDataType(typ, dt)
            p.addDelimiter(typ, annotations["dt_"+typ]["delimiter"])
        if name not in bt.content:
            #print "DT: ADDING {0} TO {1}".format(dt.name, bt.name)
            bt.addDataType(name, dt)
        if "fields" in annotations["dt_"+typ]:
            for field in sorted(annotations["dt_"+typ]["fields"]):
                baseType=annotations["dt_"+typ]["fields"][field]["baseType"]
                ranges=annotations["dt_"+typ]["fields"][field]["range"]
                manageAnnotatedDataTypes(p, annotations, baseType, field, dt, ranges) #RECURSION
    elif "exdt_"+typ in annotations:
        #print "ANNOTATED", typ
        if typ in p.dataTypes:
            dt=p.dataTypes[typ]
        else:
            dt=StructType(typ, "annotated", True)
            dt.setExclusive()
            #print "EXDT: ADDING {0} TO PARSER".format(typ)
            p.addDataType(typ, dt)
        if name not in bt.content:
            #print "EXDT: ADDING {0} TO {1}".format(dt.name, bt.name)
            bt.addDataType(name, dt)
        if "options" in annotations["exdt_"+typ]:
            details=annotations["exdt_"+typ]
            for optionName in details["options"]:
                if "fields" in details["options"][optionName]:
                    if optionName in p.dataTypes:
                        dto=p.dataTypes[optionName]
                    else:
                        #print "ADDING ",optionName
                        dto=StructType(optionName, None, False)
                        p.addDataType(optionName, dto)
                        p.addDelimiter(optionName, annotations["exdt_"+typ]["options"][optionName]["delimiter"])
                        #print "EXDT: ADDING {0} TO PARSER".format(optionName)
                    if optionName not in dt.content:
                        #print "EXDT: ADDING {0} TO {1}".format(optionName, dt.name)
                        dt.addDataType(optionName, dto)
                    for field in details["options"][optionName]["fields"]:
                        baseType=annotations["exdt_"+typ]["options"][optionName]["fields"][field]["baseType"]
                        ranges=annotations["exdt_"+typ]["options"][optionName]["fields"][field]["range"]
                        manageAnnotatedDataTypes(p, annotations, baseType, optionName+"_"+field, dto, ranges)
    elif "bb_"+typ in annotations:
        #if "smtType" in annotations["bb_"+typ]:
        #    if typ not in p.xml2SMT:
        #        p.xml2SMT[typ]=annotations["bb_"+typ]["smtType"]
            
        if typ in p.dataTypes:
            dt=p.dataTypes[typ]
        else:
            #rint typ, annotations["bb_"+typ]["type"], [ranges]
            dt=GroundType(typ, annotations["bb_"+typ]["type"], [ranges])
            dt.smtType=annotations["bb_"+typ]["smtType"]
            dt.id_type=annotations["bb_"+typ]["type"]
            p.addDataType(typ, dt)
            
            
            if dt.basetype=="bitvector":
                dt.bits=int(re.findall(r"\d+", annotations["bb_"+typ]["smtType"])[0])/4
            #print "BASIC: ADDING {0} TO PARSER ({1})".format(typ, [ranges])
        if name not in bt.content:
            bt.addDataType(name, dt)
            #print "BASIC: ADDING {0} TO {1} ({2})".format(name, bt.name, dt.name)
    else:
        raise Exception("Parser:manageAnnotatedDataTypes(): {0} is not in annotations.".format(typ))



def checkDerivedDataTypes(p, mim, annotations):
    for dt in mim.xpath("derivedDataType"):
        dt_name=dt.get("name")
        if dt_name in p.dataTypes:
            dat=p.dataTypes[dt_name]
            if "on_"+dt_name in annotations:
                newName=annotations["on_"+dt_name]["newName"]
                dat.setAnnotated()
                manageAnnotatedDataTypes(p, annotations, newName, dt_name, dat, None)
                #MANAGE REMAINING RANGES:
                if "ranges" in annotations["on_"+dt_name]:
                    ranges=annotations["on_"+dt_name]["ranges"]
                    for rng in ranges:
                        #print "RANGE FOUND {0} {1} {2}: {3}".format(dt_name, newName, rng, ranges[rng])
                        p.dataTypes[dt_name].addRange(newName, rng, ranges[rng])
            else:#just a derived Datatype, not annotated
                baseType=dt.find("baseType")
                bt_name=baseType[0].tag
                registerDataType(annotations, p, bt_name, dt_name, None, dt_name, dat.addDataType)
                rng=baseType[0].find("range")
                if rng is not None:
                    dat.hasFixedRanges()
                    dat.addRange(dt_name, bt_name, [[int(rng.find("min").text), int(rng.find("max").text)]])
            
        else:
            print "Parser:checkDerivedDataTypes(): {0} not seen before.".format(dt_name)
        
            
def checkEnumDataTypes(p, mim, annotations):
    for e in mim.xpath("enum"):
        enum_name=e.get("name")
        if enum_name in p.dataTypes:
            et=p.dataTypes[enum_name]
        else:
            et=EnumType(enum_name, None, True)
            p.addDataType(enum_name, et)
        for em in e.xpath("enumMember"):
            if em not in et:
                et.addEnumMember(em.get("name"), em.find("value").text)

def checkStructDataTypes(p, mim, annotations):
    for s in mim.xpath("struct"):
        struct_name=s.get("name")
        if struct_name in p.dataTypes:
            dat=p.dataTypes[struct_name]
            dat.setDescription(s.xpath("description")[0].text)
            if s.find("isExclusive") is not None:
                dat.setExclusive()
            for member in s.xpath("structMember"):
                member_name=member.get("name")
                datatype=member[-1] #TODO careful: really the last child?
                typekey=datatype.tag
                dataTypeName=datatype.get("name")
                mimName=datatype.find("mimName").text if datatype.find("mimName") is not None else None
                registerDataType(annotations, p, typekey, dataTypeName, mimName, member_name, dat.addDataType)


def resolveDataTypes(p, mim, annotations):
    checkStructDataTypes(p, mim, annotations)
    checkDerivedDataTypes(p, mim, annotations)
    checkEnumDataTypes(p, mim, annotations)
    

models=[]

def parseXML(xml_files, annotation_file, debugMode=False, onlyClass=None):
    """
    Stores model (mp) files, parses annotations and parses the whole mp structure.
    """
    p=ParserResult()
    #create element trees out of all the xml files
    for file in xml_files:
        try:
            models.append(ET.ElementTree(file=file))
        except ET.XMLSyntaxError as e:
            print "Parser.parseXML(): error in file {0} : {1}".format(file, e)
            return 

    #Parse annotation file before the classes are parsed
    annotations={}
    if annotation_file:
        annotations=Annotation_parser.parse_annotation_file(annotation_file)

    #PUT SOLVER INFORMATION TO THE PARSER RESULT
    if len([x for x in annotations if "solver" in x]) > 0:
                    p.addSolverSettings(annotations["solver_path"], [annotations[x] for x in annotations if "solver_arg" in x])
    #else:
    #    p.addSolverSettings("/home/ebopaul/Documents/smt/z3-4.3.2.8ef4ec7009ab-x64-debian-7.4/bin/z3", ["-smt2"])

    for x in annotations:
        if "token_" in x:
            p.addSolverToken(x[6:], annotations[x])
            
    
    #parse all classes 
    for mim in findTag(models, "mim"):
        if onlyClass is None or onlyClass in [c.get("name") for c in mim.findall("class")]:
            parseClasses(p, mim, annotations)

    for mim in findTag(models, "mim"):
        resolveDataTypes(p, mim, annotations)

    if not onlyClass:
        for model in models:
            parseRelationships(p, model, model.findall("mim")[0].get("name"))

    p.finish()

    #print "ROOT", p.rootClass.name
    print "TESTCASES", p.getNumberOfTestCases()
    return p


def findFileOfClass(folder, clas):
    files=[]
    for foldFile in os.listdir(folder):
        if "_mp.xml"==foldFile[-7:] and foldFile[0]!=".":
            with open(folder+"/"+foldFile, "r") as fl:
                el =ET.ElementTree(file=fl)
                for e in el.iter("class"):
                    if clas==e.get("name"):
                        files.append(foldFile)

    if files:
        return " ".join(files)

    return "NOT_FOUND"

def findConvexHull(folder, fl):
    mimsToFind=set()
    files=[fl]
    res=set()
    for foldFile in os.listdir(folder):
        if "_mp.xml" == foldFile[-7:]:
            files.append(foldFile)

    
    for f in files:
        with open(folder+"/"+f, "r") as file:
            try:
                element=ET.ElementTree(file=file)
            except Exception as e:
                print f
                raise e
            for e in element.iter("mimName"):
                mimsToFind.add(e.text)

    for f in files:
        with open(folder+"/"+f, "r") as file:
            element=ET.ElementTree(file=file)
            for mim in element.iter("mim"):
                if mim.get("name") in mimsToFind:
                    res.add(f)
                    mimsToFind.remove(mim.get("name"))
        
    return (res, mimsToFind)
