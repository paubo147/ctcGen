from lxml import etree as ET
import re

from Parsing_bb import GroundType, DerivedType, StructType, EnumType, ClassNode, AttrNode
from TagFinder import findTag

import Util
import Annotation_parser

class ParserResult:
    def __init__(self):
        self.classes={}
        self.pc_relations=[]
        

        self.stringPresent=False
        self.dataTypes={}
        self.delimiter={}

        #self.derivedTypes={}
        #self.enumTypes={}
        #self.structTypes={}
        #self.oldNewTranslations={}
        #self.annotatedTypes={}
        #self.buildingBlocks={}
        #self.exclusiveTypes={}
        
        self.solver_cmd=[]

        self.xml2SMT={}

        self.boundaries={}
        self.solver_tokens={}

        
    def addSolverToken(self, n, v):
        self.solver_tokens[n]=v


    def stringIsPresent(self):
        self.stringPresent=True
        
    def addDelimiter(self, typ, delimiter):
        self.delimiter[typ]=delimiter

    def addDataType(self, name, dt):
        self.dataTypes[name]=dt

    #def __contains__(self, name):
    #    return name in self.dataTypes



    def addMapping(self, old, new):
        self.xml2SMT[old]=new

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
    if a.find("noNotification") is not None:
        attribute["noModification"]="true"
    if a.find("readOnly") is not None:
        attribute["readOnly"]="true"
    if a.find("nonPersistent") is not None:
        attribute["nonPersistent"]="true"
    if a.find("restricted") is not None:
        attribute["restricted"]="true"
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

def registerDataType(p, typekey, dtName, mimName, name, func_obj):
    dat=p.dataTypes.get(typekey, None)

    if typekey in ("string", "boolean") or "int" in typekey:
        if dat is None:
            print"GROUND DATATYPE {0} NOT FOUND IN PARSER RESULT".format(typekey) 
            return
        func_obj(name, dat)
        #that is the point for ranges
        if typekey=="string":
            p.stringIsPresent()
    elif typekey == "derivedDataTypeRef":
        if dat is None:
            dat=DerivedType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey =="enumRef":
        if dat is None:
            dat=EnumType(dtName,mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey == "structRef":
        if dat is None:
            dat=StructType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    elif typekey == "sequence": #NOT DEFINED YET
        if dat is None:
            dat=SequenceType(dtName, mimName, True)
            p.addDataType(dtName, dat)
        func_obj(name, dat)
    else:
        print("NO SOURCE_CODE YET: ",typekey)


def parseAttributes(p, bb, xml, annotations):
    for a in xml.findall("attribute"):
        an=AttrNode(a.get("name"))

        #TYPE CHECKS
        dt=a.find("dataType")
        typekey=list(dt)[0].tag
        dataTypeName=dt[0].get("name") if dt[0] is not None else None
        mimName=dt[0].find("mimName").text if dt[0] is not None and dt[0].find("mimName") is not None else None
        registerDataType(p, typekey, dataTypeName, mimName, None, an.setDataType)

        if dt[0].find("range"):
            print "ADDITIONAL RANGE FOR", a.get("name"), "NOT TAKEN INTO ACCOUNT"

        #if dt[0].find("defaultValue") is not None:
        #    an["defaultValue"]=list(dt)[0].find("defaultValue").text

        #if typekey in validValues:
        #    an["validValues"]=validValues[typekey]

        checkSettings(an, a)
        bb.addAttribute(an)
        

def parseClasses(p, mim, annotations):
    for cls in mim.findall("class"):
        bb=ClassNode(cls.get("name"), mim.get("name"))
        parseAttributes(p, bb, cls, annotations)
        checkSettings(bb, cls)
        p.addClass(bb)
        #classes[bb.name]=bb

def parsePCRelationship(p, containment):
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




def parseInterMimRelationships(assoc):
    client=assoc.findall("associationEnd")[0].find("hasClass")
    server=assoc.findall("associationEnd")[1].find("hasClass")
    classes[client.get("name")].addServing(classes[server.get("name")])
    attr = assoc.findall("associationEnd")[0].get("name")
    morefkey = "%s::%s" % (client.get("name"), attr)
    associations[morefkey]=server.get("name")

def parseRelationships(p, model):
    for rel in model.iter("relationship"):
        containment=rel.find("containment")
        if containment is not None:
            parsePCRelationship(p, containment)
        assoc = rel.find("biDirectionalAssociation")
        if assoc is not None:
            pass
            #parseInterMimRelationships(assoc)

def getMissingClasses(models):
    moRefs=[]
    for model in models:
        for moref in model.iter("moRef"):
            if moref.get("name") == "ManagedObject":
                moRefs.append("ManagedObject")
            else:
                moRefs.append(moref.find("mimName").text+"::"+moref.get("name"))
                
        for tst in model.findall(".//hasClass"):
            moRefs.append(tst.find("mimName").text+"::"+tst.get("name"))
                    
        for mim in model.findall("mim"):
            for cls in mim.findall("class"):
                moRefs = [value for value in moRefs if value != mim.get("name")+"::"+cls.get("name")]
    return set(moRefs)


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
        if "smtType" in annotations["bb_"+typ]:
            if typ not in p.xml2SMT:
                p.xml2SMT[typ]=annotations["bb_"+typ]["smtType"]
            
        if typ in p.dataTypes:
            dt=p.dataTypes[typ]
        else:
            #rint typ, annotations["bb_"+typ]["type"], [ranges]
            dt=GroundType(typ, annotations["bb_"+typ]["type"], [ranges])
            p.addDataType(typ, dt)
            if dt.basetype=="bitvector":
                dt.bits=int(re.findall(r"\d+", annotations["bb_"+typ]["smtType"])[0])/4
            #print "BASIC: ADDING {0} TO PARSER ({1})".format(typ, [ranges])
        if name not in bt.content:
            bt.addDataType(name, dt)
            #print "BASIC: ADDING {0} TO {1} ({2})".format(name, bt.name, dt.name)
    else:
        print "NEVER SEEN {0} BEFORE".format(name)


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
                registerDataType(p, bt_name, dt_name, None, dt_name, dat.addDataType)
                rng=baseType[0].find("range")
                if rng is not None:
                    dat.hasFixedRanges()
                    dat.addRange(dt_name, bt_name, [[int(rng.find("min").text), int(rng.find("max").text)]])
            
        else:
            print "DATATYPE NOT USED:", dt_name
        
            
def checkEnumDataTypes(p, mim, annotations):
    for e in mim.xpath("enum"):
        enum_name=e.get("name")
        if enum_name in p.dataTypes:
            et=p.dataTypes[enum_name]
        else:
            et=EnumType(enum_name, None)
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
                registerDataType(p, typekey, dataTypeName, mimName, member_name, dat.addDataType)


def resolveDataTypes(p, mim, annotations):
    checkStructDataTypes(p, mim, annotations)
    checkDerivedDataTypes(p, mim, annotations)
    checkEnumDataTypes(p, mim, annotations)
    

"""
Parses the xml files as well as the annotation file. Has the option to create parse-tree with only one class

"""
models=[]

def parseXML(xml_files, annotation_file, debugMode=False, onlyClass=None):
    p=ParserResult()
    #create element trees out of all the xml files
    for file in xml_files:
        models.append(ET.ElementTree(file=file))

    #if not debugMode:
    #check if classes are missing
    #    moRefs=getMissingClasses(models)

    #    if moRefs:
    #        print "ERROR: the following classes are missing (mim::class): "
    #        for mo in moRefs:
    #            print "\t", mo
    #            exit(-2)

    #Parse annotation file before the classes are parsed
    annotations={}
    if annotation_file:
        annotations=Annotation_parser.parse_annotation_file(annotation_file)

    #XML 2 SMTLIB datatypes
    for m in [x for x in annotations if "mapping" in x]:
        p.addMapping(m[8:], annotations[m])
        (n,r)=Util.getNameRange(m[8:])
        dt=GroundType(n,annotations[m], r)
        p.addDataType(n, dt)

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
            parseRelationships(p, model)

    
 #GOALS
    #maxCov=annotations["strategy_maxCoverage"]
    #if maxCov["unit"].upper() in ("%", "PERC", "PERCENT", "PERCENTAGE"):
    #    p.setGoalCoverage(p.getCoverage()*int(maxCov["value"]) / 100)
    #else:
    #    p.setGoalCoverage(int(maxCov["value"]))
                       
    
    #p=ParserResult(derivedTypes, enumTypes, classes, structs, annotations, pc_list)
    print "OVERALL TESTCASES", p.getNumberOfTestCases()
    return p
