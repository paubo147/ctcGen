from lxml import etree as ET
from Parsing_bb import *
from Annotation_parser import *


class ParserResult:
    #def __init__(self):
    #    self.derivedTypes=derivedTypes
    #    self.enumTypes=enumTypes
    #    self.classes=classes
    #    self.structs=structs
    #    self.annotations=annotations
    #    self.pc_relations=pc_relations
                
    def __init__(self):
        self.derivedTypes={}
        self.enumTypes={}

        self.classes={}
        self.pc_relations=[]
        
        self.oldNewTranslations={}
        self.annotatedTypes={}
        self.buildingBlocks={}
        
        self.solver_cmd=[]


    def addClass(self, bb):
        self.classes[bb.name]=bb

    def addPCRelation(self, p, c):
        self.pc_relations.append((p,c))
    
    def addOldNewTranslation(self, k, v):
        self.oldNewTranslations[k]=v

    def addAnnotatedType(self, k, v):
        self.annotatedTypes[k]=v

    def addBuildingBlock(self, k, v):
        self.buildingBlocks[k]=v

    def addDerivedType(self, k, v):
        self.derivedTypes[k]=v

    def addEnumType(self, k, v):
        self.enumTypes[k]=v

    def addSolverSettings(self, cmd, args):
        self.solver_cmd=[cmd]+args

annotations={}

enumsToResolve=[]
datatypesToResolve=[]
structsToResolve=[]

derivedTypes={}
enumTypes={}

classes={}
structs={}
associations={}
validValues={}
pc_list=[]

def checkSettings(node, a):
    if a.find("filter") is not None:
        node.setFilter(a.find("filter").text)
    if a.find("mandatory") is not None:
        node.setMandatory()
    if a.find("noNotification") is not None:
        node.setNoNotification()

    if a.find("readOnly") is not None:
        node.setReadOnly()
    if a.find("nonPersistent") is not None:
        node.setNonPersistent()
    if a.find("restricted") is not None:
        node.setRestricted()
    if a.find("key") is not None:
        node.setKey()
    
    #CLASS ATTRIBUTES
    if a.find("dependenciesScript") is not None:
        node.setDependency(a.find("dependenciesScript").text)
        
    if a.find("root") is not None:
        node.setRoot()
        
    if a.find("systemCreated") is not None:
        node.setSystemCreated()




buildingBlocks={}
annotatedTypes={}
oldNewMapping={}

#NOT REALLY A PERFORMANCE ISSUE, UNLESS ANNOTATION FILE IS FULL OF THINGS
def isAnnotatedDatatype(p, annotations, dtName):
    ret=False
    for k,v in annotations.iteritems(): 
        if k=="on_"+dtName:                       #CHECKING FOR OLD_NEW TRANSLATION
            p.addOldNewTranslation(k[3:], v)
            for k1,v1 in annotations.iteritems(): #CHECKING FOR DATATYPE DEFINITION
                if k1=="dt_"+v["newName"]:
                    p.addAnnotatedType(k[3:], v1)
                    for k2,v2 in annotations.iteritems():
                        bbtypes=set(x["basetype"] for x in v1.values() if "basetype" in x)
                        if k2[3:] in bbtypes:     #CHECKING FOR BUILDING BLOCKS
                            p.addBuildingBlock(k2[3:], v2)
                            ret=True
            
    return ret

#CHECK CODE COVERAGE
def resolveDerivedDatatype(p, ddt):
    baseType=ddt.find("baseType")
    bt_name=list(baseType)[0].tag
    ddt_name=ddt.get("name")
    
    
    ddt_value=bt_name
             
    translation=[]
    if bt_name == "string":
        for s in ddt.iter("lengthRange"):
            translation.append([s.find("min").text,s.find("max").text])
        if baseType.find("string").find("validValues") is not None:
            validValues[ddt_name]=baseType.find("string").find("validValues").text
    else:
        for range in ddt.iter("range"):
            translation.append([range.find("min").text,range.find("max").text])

    ddt_value=bt_name+(str(translation) if len(translation) != 0 else "")
    p.addDerivedType(ddt_name, ddt_value)

def resolveDatatype(p, annotations, mimName, dtName):
    for model in models:
        e=model.xpath("mim[@name='{0}']/derivedDataType[@name='{1}']".format(mimName, dtName))
        if len(e) >= 1:
            if not isAnnotatedDatatype(p, annotations, dtName):
                resolveDerivedDatatype(p, e[0])
        else:
            print "".join([mimName,"::",dtName," could not be found!"])
        
def resolveEnum(p, mimName, dtName):
    for model in models:
        enum=model.xpath("mim[@name='{0}']/enum[@name='{1}']".format(mimName, dtName))
        if len(enum) >= 1:
            if enum[0].get("name") not in enumTypes:
                p.addEnumType(enum[0].get("name"), enum[0].xpath("enumMember/@name"))


def resolveStringType(p, annotations):
    for k,v in annotations.iteritems():
        if k=="bb_String":
            p.addBuildingBlock(k[3:], v)

def parseAttributes(p, bb, annotations):
    for a in bb.definition.findall("attribute"):
        att_n=AttrNode()
        an=a.get("name")
        
        att_n.setName(an)

        #TYPE CHECKS
        dt=a.find("dataType")
        typekey=list(dt)[0].tag

        if typekey == "derivedDataTypeRef":
            att_n.setType(list(dt)[0].get("name"))
            resolveDatatype(p, annotations, list(dt)[0].find("mimName").text, list(dt)[0].get("name"))
            #datatypesToResolve.append(list(dt)[0].find("mimName").text+"::"+list(dt)[0].get("name"))
        elif typekey in ("string", "boolean") or "int" in typekey:
            att_n.setType(typekey)
            resolveStringType(p, annotations)
        elif typekey in ("enumRef", "structRef"):#TODO check if safe to use it like that
            att_n.setType(list(dt)[0].get("name"))
            res_name=list(dt)[0].find("mimName").text+"::"+list(dt)[0].get("name")
            if typekey[0] == "e":
                resolveEnum(p, list(dt)[0].find("mimName").text, list(dt)[0].get("name"))
                #enumsToResolve.append(res_name)
            elif typekey[1]=="s":
                print "STRUCT!!!"
                #structsToResolve.append(res_name)
        elif typekey == "sequence":#TODO check if it is safe to use
            seq_dt=list(dt.find(typekey))[0]
            typekey=seq_dt.tag
            att_n.setType(typekey)
        elif typekey=="moRef":
            att_n.setType("Int") #TODO could even work, since moRef is an int to a key-attribute of some other class
        else:
            print("NO SOURCE_CODE YET: ",typekey)

        #print att_n.type, annotations, att_n.type in annotations
        #if att_n.type in annotations:
        #    att_n.setType(annotations[att_n.type][0])

        if list(dt)[0].find("defaultValue") is not None:
            att_n.setDefaultValue(list(dt)[0].find("defaultValue").text)

        if typekey in validValues:
            att_n.setValidvalues(validValues[typekey])

        #used_types.add(att_n.type)
        checkSettings(att_n, a)
        bb.addAttribute(att_n)
        


#def getStructMemberDataType(structMember):
#    if structMember.find("derivedDataTypeRef") is not None:
#        derdt=structMember.find("derivedDataTypeRef")
#        ret=derdt.find("mimName").text+"::"+derdt.get("name")
#        if derdt.get("name") not in derivedTypes:
#            print ("ERROR: derived type of struct missing")
#            return None
#        return derdt.get("name")
#    if structMember.find("moRef") is not None:
#        return structMember.find("moRef").get("name")

#def checkStructs(mim):
#    for struct in mim.findall("struct"):
#        if mim.get("name")+"::"+struct.get("name") not in structsToResolve:
#            continue
#        structname=struct.get("name")
#        structs[structname]=list()
#        for sm in struct.findall("structMember"):
#            if getStructMemberDataType(sm) is not None:
#                structs[structname].append([sm.get("name"),getStructMemberDataType(sm)])

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

"""
Parses the xml files as well as the annotation file. Has the option to create parse-tree with only one class

"""
models=[]

def parseXML(xml_files,annotation_file, output_types=False, debugMode=False, onlyClass=None):
    p=ParserResult()
    #create element trees out of all the xml files
    for file in xml_files:
        models.append(ET.ElementTree(file=file))

    #check if classes are missing
    moRefs=getMissingClasses(models)

    if moRefs:
        print "ERROR: the following classes are missing (mim::class): "
        for mo in moRefs:
            print "\t", mo
        if not debugMode:
            exit(-2)

    #Parse annotation file before the classes are parsed
    annotations={}
    if annotation_file:
        annotations=parse_annotation_file(annotation_file)
    
    #PUT SOLVER INFORMATION TO THE PARSER RESULT
    if len([x for x in annotations if "solver" in x]) > 0:
        p.addSolverSettings(annotations["solver_path"], [annotations[x] for x in annotations if "solver_arg" in x])
    else:
        p.addSolverSettings("/home/ebopaul/Documents/smt/z3-4.3.2.8ef4ec7009ab-x64-debian-7.4/bin/z3", ["-smt2"])

    
    #parse all classes 
    for model in models:
        for mim in model.findall("mim"):
            if onlyClass is None or onlyClass in [c.get("name") for c in mim.findall("class")]:
                parseClasses(p, mim, annotations)

    if not onlyClass:
        for model in models:
            parseRelationships(p, model)


    #p=ParserResult(derivedTypes, enumTypes, classes, structs, annotations, pc_list)
    return p
