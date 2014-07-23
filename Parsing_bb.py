import Util
import itertools

class DataType(object):
    """
    The baseclass of all dataTypes. Contains:
     name : string representation of the name
    """
    def __init__(self, name, typ):
        self.name=name
        self.description=""
        self.ranges={}
        self.type=typ
        self.basetype=self.name
        self.level=0

    def setDescription(self, descr):
        self.description=descr

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self)

    def getRanges(self):
        pass

    def getAssertableRanges(self):
        pass

    def getNumberOfTestCases(self):
        pass
    
        

class GroundType(DataType):
    """
    Ground datatypes are not defined in any mim. They represent the basic building blocks inside the model
    Examples could be int16, uint32, boolean, string, ...
    This type is the only one with direct mappings to SMTLIB code
    """
    def __init__(self, name, basetype, ranges):
        super(GroundType, self).__init__(name, "GROUND")
        self.ranges=ranges
        self.level+=10
        self.basetype=basetype
        if ranges!=[]:
            self.boundaries=Util.getBoundaries(name, ranges)
          
    def getRanges(self):
        return {self.name: self.ranges}

    def getAssertableRanges(self):
        if self.name in ("boolean", "string"):
            return {"NOT_DEFINED": []}
        else:
            return {self.type: self.ranges}
  
    def getNumberOfTestCases(self):
        return len(self.ranges)*3

    def __iter__(self):
        return iter([])

    def __str__(self):
        return super(GroundType, self).__str__()

    def __repr__(self):
        return str(self)


class EnumType(DataType):
    """
    An enum type is on the edge between ground type and container type. It does not contain one or more other types
    but members with values. It also contains information about the mim it is stored in.
    """
    def __init__(self, name, mim):
        super(EnumType, self).__init__(name, "ENUM")
        self.mim=mim
        self.members={}
        self.level+=10
        self.basetype="NOT_DEFINED"
        

    def addEnumMember(self, name, value):
        self.members[name]=value

    def getRanges(self):
        self.ranges=[[m] for m in self.members]
        return {self.name : self.ranges}

    def getAssertableRanges(self):
        return {self.basetype :[]}


    def getNumberOfTestCases(self):
        return len(self.ranges)

    def __contains__(self, key):
        return key in self.members



class ContainerType(DataType):
    """ 
    Every type containing one or more other types in form of a sequence, struct, set, etc. is a container type.
    Contains also the mim.
    """
    def __iter__(self):
        for c in self.content.values():
            yield c
            #iter(c)
            for c1 in c:
                yield c1
            


    def __init__(self, name, mim, typ):
        super(ContainerType, self).__init__(name, typ)
        self.mim=mim
        self.content={}
        self.level+=1
        self.basetype="NOT_DEFINED"

    def addDataType(self, name, dataType):
        self.content[name]=dataType
        dataType.level+=self.level
        self.basetype=dataType.basetype

    def __str__(self):
        return str(self.level)+" "+super(ContainerType, self).__str__()


class StructType(ContainerType):
    """
    A struct is a fixed, ordered collection of other types of any kind. 
    The types are either exclusive (comparable with union in C) or not. 
    """
    def __init__(self, name, mim):
        super(StructType, self).__init__(name, mim, "STRUCT")
        self.isExclusive=False

    
    def setExclusive(self):
        self.isExclusive=True

    def getRanges(self):
        self.ranges={x: self.content[x].getRanges() for x in self.content}
        return {self.name : self.ranges}

    def getAssertableRanges(self):
        return self.getRanges()

    def getNumberOfTestCases(self):
        if self.isExclusive:
            return sum(self.content[x].getNumberOfTestCases() for x in self.content)
        else:
            return reduce(lambda x,y: x*y, [self.content[x].getNumberOfTestCases() for x in self.content])
            

    def __str__(self):
        s=["STRUCT"]
        if self.isExclusive:
            s.append("(X)")
        s.append("[")
        s.append(super(StructType, self).__str__())
        s.append("]")
        return " ".join(s)
    
class SequenceType(ContainerType):
    pass

class DerivedType(ContainerType):
    """
    Placeholder for one other DataType. Might be replaced.
    """
    def __init__(self, name, mim):
        super(DerivedType, self).__init__(name, mim, "DERIVED")
        self.annotated=False
        self.additionalRanges={}
        self.fixedRanges=False

    def hasFixedRanges(self):
        self.fixedRanges=True
        
    def addDataType(self, name, dataType):
        super(DerivedType, self).addDataType(0, dataType)
        

    def addRange(self, name, ranges):
        self.additionalRanges[name]=ranges

    def getRanges(self):
        if not self.fixedRanges:
            self.ranges=self.content[0].getRanges()
            if self.additionalRanges:
                for r in self.additionalRanges:
                    self.ranges[r]=self.additionalRanges[r]
        return self.ranges

    def getAssertableRanges(self):
        return self.content[0].getAssertableRanges()

    def setAnnotated(self):
        self.annotated=True

    def getNumberOfTestCases(self):
        return self.content[0].getNumberOfTestCases()


class AttrNode:
    def __init__(self, name):
        self.name=name
        self.dataType=None
        self.defaultValue=""
        self.settings={}

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
        self.coverage=1

    def getNumberOfTestCases(self):
        return self.dataType.getNumberOfTestCases()

    def __setitem__(self, key, value):
        self.settings[key]=value

    def __getitem__(self, key):
        return self.settings[key]

    def setDefaultValue(self, s):
        self.defaultValue=s

    def setValidValues(self, re):
        self.validValues=re
        
    def setDataType(self, name, t):
        self.dataType=t
        

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
    def __init__(self, clsName, mimName=""):
        self.name=clsName
        self.mim= mimName
        self.parents=[]
        self.children= []
        #self.servers= []
        self.attributes=[]
        #self.isRoot=False
        #self.isSystemCreated=False
        self.settings={}
        
    def __getitem__(self, key):
        return self.settings[key]

    def __setitem__(self, key, val):
        self.settings[key]=val

    def __delitem__(self, key):
        del self.settings[key]

    def __contains__(self, key):
        return key in self.settings

    def getNumberOfTestCases(self):
        m=1
        for x in self.attributes:
            m*=x.getNumberOfTestCases()
        return m
        
    #def setSystemCreated(self):
    #    self.isSystemCreated=True

    #def setRoot(self):
    #    self.isRoot=True

    #def setDependency(self, s):
    #    self.dependency=s

    def addParent(self, parent):
        self.parents.append(parent)

    def addChild(self, child):
        self.children.append(child)

    def addAttribute(self, att):
        self.attributes.append(att)

    #def addServing(self, server):
    #    self.servers.append(server)

    def __str__(self):
        s=[self.name, ":"]
        for a in self.attributes:
            s.append(str(a))
        return " ".join(s)
 
