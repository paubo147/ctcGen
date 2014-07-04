#from lxml import etree as ET
from Parsing_bb import *
from Annotation_parser import *


class ParserResult:
    def __init__(self, derivedTypes, enumTypes, classes, structs, annotations, pc_relations):
        self.derivedTypes=derivedTypes
        self.enumTypes=enumTypes
        self.classes=classes
        self.structs=structs
        self.annotations=annotations
        self.pc_relations=pc_relations
        

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

    
def parseAttributes(bb, annotations):
    for a in bb.definition.findall("attribute"):
        att_n=AttrNode()
        an=a.get("name")
        
        att_n.setName(an)

        #TYPE CHECKS
        dt=a.find("dataType")
        typekey=list(dt)[0].tag

        if typekey == "derivedDataTypeRef":
            att_n.setType(list(dt)[0].get("name"))
            datatypesToResolve.append(list(dt)[0].find("mimName").text+"::"+list(dt)[0].get("name"))
        elif typekey in ("string", "boolean") or "int" in typekey:
            att_n.setType(typekey)
        elif typekey in ("enumRef", "structRef"):#TODO check if safe to use it like that
            att_n.setType(list(dt)[0].get("name"))
            res_name=list(dt)[0].find("mimName").text+"::"+list(dt)[0].get("name")
            if typekey[0] == "e":
                enumsToResolve.append(res_name)
            elif typekey[1]=="s":
                structsToResolve.append(res_name)
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
        checkSettings(att_n, a)
        bb.addAttribute(att_n)
        


def checkDerivedDataTypes(mim):
    for ddt in mim.findall("derivedDataType"):
        if mim.get("name")+"::"+ddt.get("name") not in datatypesToResolve:
            continue
        baseType=ddt.find("baseType")
        bt_name=list(baseType)[0].tag
        ddt_name=ddt.get("name")
        
        derivedTypes[ddt_name]=bt_name
             
        translation=[]
        if bt_name == "string":
            #if "ipv4address" in ddt_name.lower():
            #    bt_name="IPV4"
            #if "macaddress" in ddt_name.lower():
            #    bt_name="MAC"
            for s in ddt.iter("lengthRange"):
                translation.append([s.find("min").text,s.find("max").text])
            if baseType.find("string").find("validValues") is not None:
                validValues[ddt_name]=baseType.find("string").find("validValues").text
        else:
            for range in ddt.iter("range"):
                translation.append([range.find("min").text,range.find("max").text])

        derivedTypes[ddt_name]=bt_name+(str(translation) if len(translation) != 0 else "")
        
def checkEnums(mim):
    for enum in mim.findall("enum"):
        if mim.get("name")+"::"+enum.get("name") not in enumsToResolve:
            continue
        enum_key ="%s::%s" % (mim.get("name"), enum.get("name"))
        enum_members=enum.findall("enumMember")
        temp_enum_key=""
        if enum_key.find("::")==-1:
            temp_enum_key=enum_key
        else:
            temp_enum_key=enum_key[enum_key.find("::")+2:]
        if temp_enum_key not in enumTypes:
            enumTypes[temp_enum_key]=[x.get("name") for x in enum_members]

def getStructMemberDataType(structMember):
    if structMember.find("derivedDataTypeRef") is not None:
        derdt=structMember.find("derivedDataTypeRef")
        ret=derdt.find("mimName").text+"::"+derdt.get("name")
        if derdt.get("name") not in derivedTypes:
            print ("ERROR: derived type of struct missing")
            return None
        return derdt.get("name")
    if structMember.find("moRef") is not None:
        return structMember.find("moRef").get("name")

def checkStructs(mim):
    for struct in mim.findall("struct"):
        if mim.get("name")+"::"+struct.get("name") not in structsToResolve:
            continue
        structname=struct.get("name")
        structs[structname]=list()
        for sm in struct.findall("structMember"):
            if getStructMemberDataType(sm) is not None:
                structs[structname].append([sm.get("name"),getStructMemberDataType(sm)])

def insert_dummy_elements(lst):
    for e in lst:
        name=""
        if e.find("::")==-1:
            name=e
        else:
            name=e[e.find("::")+2:]

        et_el=ET.Element(name.lower())
        et_el.set("name", name)
        bb=ClassNode(et_el)
        
        classes[name]=bb
    
def extractClassSettings(cls, bb):
    if cls.find("dependenciesScript") is not None:
        bb.setDependency(cls.find("dependenciesScript").text)
        
    if cls.find("root") is not None:
        bb.setRoot()
        
    if cls.find("systemCreated") is not None:
        bb.setSystemCreated()

def parseClasses(mim, annotations):
    for cls in mim.findall("class"):
        bb=ClassNode(cls, mim.get("name"))
        parseAttributes(bb, annotations)
        extractClassSettings(cls, bb)
        classes[bb.name]=bb

def parsePCRelationship(containment):
    parent = containment.find("parent")
    if parent is not None:
        pclas = parent.find("hasClass")
        
    child = containment.find("child")
    if child is not None:
        cclas = child.find("hasClass")

    if cclas is None or pclas is None:
        raise Exception("Relationship-inconsistency found")

    
    if pclas.get("name") not in classes:
        name=""
        e=pclas.get("name")
        if e.find("::")==-1:
            name=e
        else:
            name=e[e.find("::")+2:]

        et_el=ET.Element(name.lower())
        et_el.set("name", name)
        bb=ClassNode(et_el)
        
        classes[name]=bb

    parent_bb=classes[pclas.get("name")]
    child_bb=classes[cclas.get("name")]
    child_bb.addParent(parent_bb)
    parent_bb.addChild(child_bb)
    pc_list.append((parent_bb, child_bb))
    #pc_list.append(parent_bb)
    #pc_list.append(child_bb)


def parseInterMimRelationships(assoc):
    client=assoc.findall("associationEnd")[0].find("hasClass")
    server=assoc.findall("associationEnd")[1].find("hasClass")
    classes[client.get("name")].addServing(classes[server.get("name")])
    attr = assoc.findall("associationEnd")[0].get("name")
    morefkey = "%s::%s" % (client.get("name"), attr)
    associations[morefkey]=server.get("name")

def parseRelationships(model):
    for rel in model.iter("relationship"):
        containment=rel.find("containment")
        if containment is not None:
            parsePCRelationship(containment)
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

def dewey_decorator(bb_class, deweynr=0, deweycode=""):
    if not deweycode:
        deweycode_t=str(deweynr)
    else:
        deweycode_t=deweycode+"."+str(deweynr)
    bb_class.setDewey(deweycode_t)
    i=deweynr
    for c in bb_class.children:
        dewey_decorator(c, i, deweycode_t)
        i+=1
    

"""
Parses the xml files as well as the annotation file. Has the option to create parse-tree with only one class

"""
def parseXML(xml_files,annotation_file, output_types=False, debugMode=False, onlyClass=None):
    models=[]
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
           
    #parse all classes 
    for model in models:
        for mim in model.findall("mim"):
            if onlyClass is None or onlyClass in [c.get("name") for c in mim.findall("class")]:
                parseClasses(mim, annotations)

    #resolve all datatypes, enums and structs
    for model in models:
        for mim in model.findall("mim"):
            checkDerivedDataTypes(mim)
            checkEnums(mim)
            checkStructs(mim)

    #resolve relationships
    if not onlyClass:
        for model in models:
            parseRelationships(model)

    #dummy one-leaf node
    parents=[]
    for bb in classes.iterkeys():
        for parent in classes[bb].parents:
            if parent not in parents:
                parents.append(parent)

    dummy_leaf = ET.Element("leaf")
    dummy_leaf.set("name", "Leaf")
    dummy_leaf_bb = ClassNode(dummy_leaf)

    for bb in classes.iterkeys():
        if classes[bb] not in parents:
            dummy_leaf_bb.addParent(classes[bb])

    #check for cyclic references and put root of the tree at position 0
    resolved=[]
    if hasCyclicReferences(dummy_leaf_bb, resolved, []):
        print "Fatal error: model contains cyclic references"
        exit(-1)


    bb_root=resolved[0]
    
    dewey_decorator(bb_root)

    if debugMode:
        print "TREE:"
        text_outputter(bb_root)
        

    if output_types: 
        print "TREE:"
        text_outputter(bb_root)
        print "DERIVEDTYPES:"
        print derivedTypes
        print "ENUMS"
        print enumTypes
        print "STRUCTS"
        print structs


    return ParserResult(derivedTypes, enumTypes, classes, structs, annotations, pc_list)

