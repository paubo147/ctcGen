class StructDef:
    def __init__(self, name):
        self.name=name
        self.exclusive=False
        #keep going

class AttrNode:
    def __init__(self):
        self.filter=""
        self.mandatory=False
        self.notification=True
        self.readOnly=False
        self.persistent=True
        self.restricted=False
        self.key=False
        self.validValues=""
        self.type=""
        self.defaultValue=""

    def setDefaultValue(self, s):
        self.defaultValue=s

    def setValidValues(self, re):
        self.validValues=re
        
    def setType(self, t):
        self.type=t
        
    def setName(self, val):
        self.name=val

    def setFilter(self, s):
        self.filter=s

    def setMandatory(self):
        self.mandatory=True

    def setNoNotification(self):
        self.notification=False

    def setReadOnly(self):
        self.readOnly=True

    def setNonPersistent(self):
        self.persistent=False

    def setRestricted(self):
        self.restricted=True

    def setKey(self):
        self.key=True

    def __str__(self):
        s = self.type + " " + self.name +"["
        if self.mandatory:
            s += "mandatory"
        if not self.notification:
            s += ",noNotification"
        if self.readOnly:
            s += ",readOnly"
        if not self.persistent:
            s += ",nonPersistent"
        if self.restricted:
            s += ",restricted"
        if self.key:
            s += ",key"
        s += "]"

        if self.filter:
            s+= ", filter: "+self.filter

        if self.validValues:
            s+= ", regexp"


        return s


class ClassNode:
    def __init__(self, definition, mim=""):
        self.definition=definition
        self.name=self.definition.get("name")
        self.mim= mim
        self.parents= []
        self.children= []
        self.servers= []
        self.attributes= []
        self.dependency=""
        self.isRoot=False
        self.isSystemCreated=False
        self.dewey_code=""
        
    def __str__(self):
        return name

    def setDewey(self, s):
        self.dewey_code=s
        
    def setSystemCreated(self):
        self.isSystemCreated=True

    def setRoot(self):
        self.isRoot=True

    def setDependency(self, s):
        self.dependency=s

    def addParent(self, parent):
        self.parents.append(parent)

    def addChild(self, child):
        self.children.append(child)

    def addAttribute(self, att):
        self.attributes.append(att)

    def addServing(self, server):
        self.servers.append(server)
    
 
def hasCyclicReferences(bb, resolved, seen):
    seen.append(bb)
    for after in bb.parents + bb.servers:
        if after not in resolved:
            if after in seen:
                return True
            hasCyclicReferences(after, resolved, seen)
        resolved.append(after)
    return False

def text_outputter(moc, tabs=0):
    s=tabs*" " +"[C]" + moc.dewey_code + " "+ moc.name +"["

    if moc.isRoot:
        s+= "root"
    if moc.isSystemCreated:
        s+= ",systemCreated"
    if moc.dependency:
        s+= ",dependency"
    s += "]\n"
    for attr in moc.attributes:
        s += (tabs+1)*" " + "[A]" + str(attr) + "\n"
    for enc in moc.servers:
        s+= (tabs+1)*" " + "[E]" + enc + "\n"
    print s,
    for child in moc.children:
        text_outputter(child, tabs+2)
