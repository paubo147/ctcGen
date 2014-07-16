from lxml import etree as ET
from Parsing_bb import *
from TagFinder import *
from Annotation_parser import *
from Coverage import computeCoverage

import math
import Util

class ParserResult:
    def __init__(self):
        self.derivedTypes={}
        self.enumTypes={}

        self.classes={}
        self.pc_relations=[]
        
        self.derivedTypes={}
        self.enumTypes={}
        self.structTypes={}
        self.oldNewTranslations={}
        self.annotatedTypes={}
        self.buildingBlocks={}
        self.exclusiveTypes={}
        
        self.solver_cmd=[]

        self.xml2SMT={}

        self.coverage=0
        self.goalCoverage=0

    def addMapping(self, old, new):
        self.xml2SMT[old]=new

    def addClass(self, bb):
        self.classes[bb.name]=bb

    def addPCRelation(self, p, c):
        self.pc_relations.append((p,c))
    
    def addOldNewTranslation(self, k, v):
        self.oldNewTranslations[k]=v

    def addAnnotatedType(self, k, v):
        self.annotatedTypes[k]=v

    def addExclusiveType(self, k, v):
        self.exclusiveTypes[k]=v

    def addBuildingBlock(self, k, v):
        self.buildingBlocks[k]=v

    def addDerivedType(self, k, v):
        self.derivedTypes[k]=v

    def addEnumType(self, k, v):
        self.enumTypes[k]=v

    def addStructType(self, k, exclusive, v):
        self.structTypes[k]=(exclusive, v)

    def addSolverSettings(self, cmd, args):
        self.solver_cmd=[cmd]+args

    def setGoalCoverage(self, i):
        self.goalCoverage=i

    def getCoverage(self):
        self.coverage=1
        for c in self.classes.values():
            for a in c.attributes:
                self.coverage *= computeCoverage(a["dataType"], self.derivedTypes, self.oldNewTranslations, self.annotatedTypes, self.exclusiveTypes, self.enumTypes, self.structTypes)

        self.coverage=math.log(self.coverage)
        return self.coverage

#annotations={}

#enumsToResolve=[]
#datatypesToResolve=[]
#structsToResolve=[]

#derivedTypes={}
#enumTypes={}

#classes={}
#structs={}
#associations={}
validValues={}
#pc_list=[]


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

def parseAttributes(p, bb, annotations):
    for a in bb.definition.findall("attribute"):
        attribute={}
        attribute["name"]=a.get("name")

        #TYPE CHECKS
        dt=a.find("dataType")
        typekey=list(dt)[0].tag
        if typekey == "derivedDataTypeRef":
            attribute["dataType"]=dt[0].get("name")
            p.addDerivedType(dt[0].get("name"), None)
        elif typekey in ("string", "boolean") or "int" in typekey:
            attribute["dataType"]=typekey
            if typekey=="string":
                p.addBuildingBlock("String", annotations["bb_String"]) #UGLY!!!
        elif typekey =="enumRef":
            res_name=dt[0].find("mimName").text+"::"+dt[0].get("name")
            attribute["dataType"]=dt[0].get("name")
            p.addEnumType(dt[0].get("name"), None)
        elif typekey == "structRef":
            attribute["dataType"]=dt[0].get("name")
            p.addStructType(dt[0].get("name"), False, None)
        elif typekey == "sequence":
            attribute["dataType"]=typekey
            #TODO decide what to do?
        elif typekey=="moRef":
            attribute["dataType"]="string"
            #TODO maybe it is enough! Check if key-attributes are always of type string!

        else:
            print("NO SOURCE_CODE YET: ",typekey)


        if dt[0].find("defaultValue") is not None:
            attribute["defaultValue"]=list(dt)[0].find("defaultValue").text

        if typekey in validValues:
            attribute["validValues"]=validValues[typekey]

        checkSettings(attribute, a)
        bb.addAttribute(attribute)
        

def parseClasses(p, mim, annotations):
    for cls in mim.findall("class"):
        bb=ClassNode(cls, mim.get("name"))
        parseAttributes(p, bb, annotations)
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

def checkDerivedDataTypes(p, mim, annotations):
    for dt in mim.xpath("derivedDataType"):
        dt_name=dt.get("name")
        if dt_name in p.derivedTypes:
            #is it a special type?
            if "on_"+dt_name in annotations and dt_name not in p.oldNewTranslations:
                del p.derivedTypes[dt_name]
                oldName=dt_name
                newName=annotations["on_"+dt_name]["newName"]
                p.addOldNewTranslation(dt_name, annotations["on_"+dt_name])
                if "dt_"+newName in annotations and newName not in p.annotatedTypes:
                    p.addAnnotatedType(newName, annotations["dt_"+newName])
                    for bt in set(x["baseType"] for x in annotations["dt_"+newName].values() if "baseType" in x):
                        if  bt not in p.buildingBlocks and "bb_"+bt in annotations:
                            p.addBuildingBlock(bt, annotations["bb_"+bt])
                if "exdt_"+newName in annotations and newName not in p.exclusiveTypes:
                    p.addExclusiveType(newName, annotations["exdt_"+newName])
                    for optionName in annotations["exdt_"+newName]:
                        for field in annotations["exdt_"+newName][optionName]["fields"]:
                            baseType = annotations["exdt_"+newName][optionName]["fields"][field]["baseType"]
                            if baseType not in p.buildingBlocks and "bb_"+baseType in annotations:
                                p.addBuildingBlock(baseType, annotations["bb_"+baseType])
            else:
                ddt_value={}
                baseType=dt.find("baseType")
                bt_name=baseType[0].tag
                ddt_value["baseType"]=bt_name

                translation=[]
                rnge=[]
                if bt_name == "string":
                    for s in baseType.iter("lengthRange"):
                        rnge.append([int(s.find("min").text), int(s.find("max").text)])
                 #if baseType.find("string").find("validValues") is not None:
                 #    validValues[ddt_name]=baseType.find("string").find("validValues").text
                else:
                    for r in baseType.iter("range"):
                        rnge.append([int(r.find("min").text), int(r.find("max").text)])
                if not rnge:
                    rnge=Util.get_name_range(bt_name)[1]

                if rnge:
                    ddt_value["range"]=rnge
                    #boundaries=Util.getBoundaries(rnge)
                
                p.addDerivedType(dt_name, ddt_value)
            
def checkEnumDataTypes(p, mim, annotations):
    for e in mim.xpath("enum"):
        enum_name=e.get("name")
        if enum_name in p.enumTypes:
            enum_members={}
            for em in e.xpath("enumMember"):
                enum_members[em.get("name")]=em.find("value").text
            p.addEnumType(enum_name, enum_members)


def checkStructDataTypes(p, mim, annotations):
    for s in mim.xpath("struct"):
        struct_name=s.get("name")
        if struct_name in p.structTypes:
            struct_members=[]
            exclusive=(s.find("isExclusive") is not None)
                
            for member in s.xpath("structMember"):
                #TODO default values?
                sm={}
                sm["name"]=member.get("name")
                datatype=member[-1] #TODO careful: really the last child?
                typekey=datatype.tag
                if typekey=="derivedDataTypeRef":
                    sm["dataType"]=datatype.get("name")
                    p.addDerivedType(datatype.get("name"), None)
                elif typekey=="enumRef":
                    sm["dataType"]=datatype.get("name")
                    p.addEnum(datatype.get("name"), None)
                elif typekey in ("string", "boolean") or "int" in typekey:
                    sm["dataType"]=typekey
                    rnge=[]
                    if typekey == "string":
                        for s in datatype.iter("lengthRange"):
                            rnge.append([int(s.find("min").text), int(s.find("max").text)])
                    #valid values!
                    else:
                        for r in datatype.iter("range"):
                            rnge.append([int(r.find("min").text), int(s.find("max").text)])
                    if rnge:
                        sm["range"]=rnge
                elif typekey == "moRef":
                    sm["dataType"]="string"
                else:
                    print "TYPE MISMATCH ON STRUCT MEMBER",sm["name"] 
                struct_members.append(sm)
            p.addStructType(struct_name, exclusive, struct_members)

def checkForMissingDataTypes(p, mim, annotations):
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

    if not debugMode:
    #check if classes are missing
        moRefs=getMissingClasses(models)

        if moRefs:
            print "ERROR: the following classes are missing (mim::class): "
            for mo in moRefs:
                print "\t", mo
                exit(-2)

    #Parse annotation file before the classes are parsed
    annotations={}
    if annotation_file:
        annotations=parse_annotation_file(annotation_file)

    #XML 2 SMTLIB datatypes
    for m in [x for x in annotations if "mapping" in x]:
        p.addMapping(m[8:], annotations[m])

    #PUT SOLVER INFORMATION TO THE PARSER RESULT
    if len([x for x in annotations if "solver" in x]) > 0:
        p.addSolverSettings(annotations["solver_path"], [annotations[x] for x in annotations if "solver_arg" in x])
    else:
        p.addSolverSettings("/home/ebopaul/Documents/smt/z3-4.3.2.8ef4ec7009ab-x64-debian-7.4/bin/z3", ["-smt2"])

    
    #parse all classes 
    for mim in findTag(models, "mim"):
        if onlyClass is None or onlyClass in [c.get("name") for c in mim.findall("class")]:
            parseClasses(p, mim, annotations)

    for mim in findTag(models, "mim"):
        checkForMissingDataTypes(p, mim, annotations)

    if not onlyClass:
        for model in models:
            parseRelationships(p, model)
 #GOALS
    maxCov=annotations["strategy_maxCoverage"]
    if maxCov["unit"].upper() in ("%", "PERC", "PERCENT", "PERCENTAGE"):
        p.setGoalCoverage(p.getCoverage()*int(maxCov["value"]) / 100)
    else:
        p.setGoalCoverage(int(maxCov["value"]))
                       
    
    #p=ParserResult(derivedTypes, enumTypes, classes, structs, annotations, pc_list)
    return p
