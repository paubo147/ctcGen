import Util
import itertools

class DataType(object):
    """
    The baseclass of all dataTypes. Contains:
     name : string representation of the name
    """
    def __init__(self, name, typ, isHead):
        self.name=name
        self.description=""
        self.ranges={}
        self.type=typ
        self.basetype=self.name
        self.level=0
        self.isHead=isHead

    def setDescription(self, descr):
        self.description=descr

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self)

    #def getRanges(self):
    #    pass

    def getAssertableRanges(self):
        pass

    def getNumberOfTestCases(self):
        pass

    def increaseLevel(self, value=1):
        #print "BASIC", self.name, "increased by ", value, "=", self.level+value
        self.level+=value
    
        

class GroundType(DataType):
    """
    Ground datatypes are not defined in any mim. They represent the basic building blocks inside the model
    Examples could be int16, uint32, boolean, string, ...
    This type is the only one with direct mappings to SMTLIB code
    """
    def __init__(self, name, basetype, ranges):
        super(GroundType, self).__init__(name, "GROUND", True)
        self.ranges=ranges
        self.basetype=basetype
        self.boundaries=[]
        #print self.name, self.basetype, self.type, id(self)
        if ranges!=[]:
            self.boundaries=Util.getBoundaries(name, ranges)
          
    #def getRanges(self):
    #    return {self.name: self.ranges}

    def getAssertableRanges(self):
        if self.name in ("boolean", "string"):
            return {"NOT_DEFINED": []}
        else:
            return {self.name: self.ranges}
  
    def getBoundaries(self):
        return {self.name : self.boundaries}

    def getNumberOfTestCases(self):
        #print self.name, len(self.boundaries)
        if len(self.boundaries):
            return len(self.boundaries)
        else:
            return 1

    def __str__(self):
        return super(GroundType, self).__str__()

    def __repr__(self):
        return str(self)


class EnumType(DataType):
    """
    An enum type is on the edge between ground type and container type. It does not contain one or more other types
    but members with values. It also contains information about the mim it is stored in.
    """
    def __init__(self, name, mim, isHead):
        super(EnumType, self).__init__(name, "ENUM", isHead)
        self.mim=mim
        self.members={}
        self.basetype="ENUM"
        self.boundaries=[]

    def addEnumMember(self, name, value):
        self.members["{0}_{1}".format(self.name, name)]=value
        self.boundaries.append([name])

    #def getRanges(self):
    #    self.ranges=[[m] for m in self.members]
    #    return {self.name : self.ranges}

    def getAssertableRanges(self):
        return {self.basetype :[]}
    
    def getBoundaries(self):
        return {self.name:self.boundaries}

    def getNumberOfTestCases(self):
        #print self.name, len(self.boundaries)
        #print "ENUM", len(self.boundaries)
        return len(self.boundaries)

    def __contains__(self, key):
        return key in self.members



class ContainerType(DataType):
    """ 
    Every type containing one or more other types in form of a sequence, struct, set, etc. is a container type.
    Contains also the mim.
    """

    def __init__(self, name, mim, typ, isHead):
        super(ContainerType, self).__init__(name, typ, isHead)
        self.mim=mim
        self.content={}
        self.basetype="NOT_DEFINED"
        self.sortkey=[]

    def addDataType(self, name, dataType):
        self.sortkey.append(name)
        self.content[name]=dataType
        #print "ADDED", name
        dataType.increaseLevel(2)
        
    def increaseLevel(self, val=1):
        #print "CONTAINER", self.name, "increased by", val, "=", self.level+val
        self.level+=val
        for c in self.content:
            #print "CONTAINER", self.name, "increasing child", c
            self.content[c].increaseLevel(2)
            

    def __str__(self):
        return super(ContainerType, self).__str__()


class StructType(ContainerType):
    """
    A struct is a fixed, ordered collection of other types of any kind. 
    The types are either exclusive (comparable with union in C) or not. 
    """
    def __init__(self, name, mim, isHead):
        super(StructType, self).__init__(name, mim, "STRUCT", isHead)
        self.isExclusive=False
        self.isTop=False

    
    def setExclusive(self):
        self.isExclusive=True


    def addDataType(self, n, t):
        super(StructType, self).addDataType(n, t)
        if t.type=="STRUCT":
            t.isTop=False

    #def getRanges(self):
    #    self.ranges={x:self.content[x].getRanges() for x in self.content}
    #    return self.ranges

    def getAssertableRanges(self):
        return {x:self.content[x].getAssertableRanges() for x in self.content}

    def getNumberOfTestCases(self):
        #if self.isExclusive:
            #print self.name, sum(self.content[x].getNumberOfTestCases() for x in self.content)
        #    return sum(self.content[x].getNumberOfTestCases() for x in self.content)
        #else:
            #print self.name, reduce(lambda x,y: x*y, [self.content[x].getNumberOfTestCases() for x in self.content])
            #return sum(self.content[x].getNumberOfTestCases() for x in self.content)

        return reduce(lambda x,y: x*y, [self.content[x].getNumberOfTestCases() for x in self.content])
            
    def getBoundaries(self):
        self.boundaries={x: self.content[x].getBoundaries() for x in sorted(self.content)}
        return self.boundaries


class DerivedType(ContainerType):
    """
    Placeholder for one other DataType. Might be replaced.
    """
    def __init__(self, name, mim, isHead):
        super(DerivedType, self).__init__(name, mim, "DERIVED", isHead)
        self.annotated=False
        self.additionalRanges={}
        self.fixedRanges=False
        self.boundaries={}

    def hasFixedRanges(self):
        self.fixedRanges=True
        
    def addDataType(self, name, dataType):
        super(DerivedType, self).addDataType(0, dataType)
        self.basetype=dataType.basetype
        

    def addRange(self, name, accessor, ranges):
        self.additionalRanges[name]={accessor:ranges}
        if self.fixedRanges:
            self.fixedRanges=False
            self.getBoundaries()
            self.fixedRanges=True

    def getAssertableRanges(self):
        if not self.fixedRanges:
            self.ranges=self.content[0].getAssertableRanges()
            if self.additionalRanges:
                for r in self.additionalRanges:
                    for a in self.additionalRanges[r]:
                        #print "HELLO", r, a, self.additionalRanges[r][a]
                        temptyp=self.ranges[a].keys()[0] #HACK. Not sure if this will always work
                        self.ranges[a]={temptyp:self.additionalRanges[r][a]}
                        #print "ADDRANGES: replace ", self.ranges[r][a], "with", self.additionalRanges[r][a],"ENDADDRANGES"
                    #self.ranges[r]=self.ranges[self.additionalRanges[r]
        return self.ranges
    
    def getBoundaries(self):
        if not self.fixedRanges:
            if not self.content or 0 not in self.content:
                raise Exception("FATAL: DerivedType.getBoundaries(): {0} has no content".format(self.name))
            self.boundaries=self.content[0].getBoundaries()
            if self.additionalRanges:
                for r in self.additionalRanges:
                    for a in self.additionalRanges[r]:
                        if self.content[0].type=="GROUND": #CHECK FOR ENUMS
                            temptyp=a
                        else:
                            temptyp=self.boundaries[a].keys()[0]
                        #print "DERIVED", temptyp, self.content[0].type, self.boundaries[a]
                        self.boundaries[a]={temptyp:Util.getBoundaries(r, self.additionalRanges[r][a])}
                        #print "ADDRANGES: replace ", self.ranges[r][a], "with", self.additionalRanges[r][a],"ENDADDRANGES"
                    #self.ranges[r]=self.ranges[self.additionalRanges[r]
        return self.boundaries
        

    def setAnnotated(self):
        self.annotated=True

    def getNumberOfTestCases(self):
        #print "DERVIED", self.name, self.content[0].getNumberOfTestCases()
        #print self.name, self.content[0].getNumberOfTestCases()
        return self.content[0].getNumberOfTestCases()


class SequenceType(DerivedType):
    pass

#    def __init__(self, name, mim, isHead):
#        super(SequenceType, self).__init__(name, mim, "SEQUENCE", isHead)
#        self.unique=False
#        self.ordered=False
#        self.lengthRanges=[]

#    def setLengthConstraints(self, rng):
#        if self.lengthRanges:
#            self.lengthRanges=rng
        

#    def getAssertableRanges(self):
#        return self.content[0].getAssertableRanges()

#    def getBoundaries(self):
#        return self.content[0].getBoundaries()

    
    

class AttrNode(object):
    def __init__(self, name):
        self._name=name
        self._dataType=None
        self._description=""
        self._defaultValue=None

        self.settings={}

        
    @property
    def description(self):
        return self._description

    @description.setter
    def description(self, value):
        self._description=value

    @property
    def name(self):
        return self._name

    @property
    def dataType(self):
        return self._dataType

    @dataType.setter
    def dataType(self, dt):
        self._dataType=dt

    @property
    def defaultValue(self):
        return self._defaultValue

    @defaultValue.setter
    def defaultValue(self, value):
        self._defaultValue=value


    def __init__(self, name):
        self._name=name
        self._dataType=None
        self._description=""

        self.settings={}


    def getNumberOfTestCases(self):
        #print self.name, self.dataType.getNumberOfTestCases()
        return self.dataType.getNumberOfTestCases()

    def __setitem__(self, key, value):
        self.settings[key]=value

    def __contains__(self, key):
        return key in self.settings

    def __getitem__(self, key):
        return self.settings[key]

         
    def setDataType(self, name, t):
        #print "SET DATATYPE", t.name, "increase", t.level
        self.dataType=t
        self.dataType.increaseLevel()
        


class ClassNode:
    
    @property
    def name(self):
        return self.name

    @name.setter
    def name(self, value):
        self.name=value
        
   

    def __init__(self, clsName, mimName=""):
        self.name=clsName
        self.mim= mimName
        self.parents=[]
        self.children= []
        self.attributes=[]
        self.settings={}
   
    def paths(self):
        result=[]
        current_list=[self]
        old_list=[]
        i=0
        while len(current_list) > 0:#sum([len(c.children) for c in current_list]) > 0:
            result.append(old_list+[x.name for x in current_list])
            old_list.extend([x.name for x in current_list])
            tempList=list(current_list)
            current_list=[]
            for t in tempList:
                for c in t.children:
                    current_list.append(c)
        return result
            
            
     
    def __getitem__(self, key):
        return self.settings[key]

    def __setitem__(self, key, val):
        self.settings[key]=val

    def __delitem__(self, key):
        del self.settings[key]

    def __contains__(self, key):
        return key in self.settings

    def getNumberOfTestCases(self):
        #print self.name, sum(a.getNumberOfTestCases() for a in self.attributes)
        return sum(a.getNumberOfTestCases() for a in self.attributes)

        #return {self.name: sum(a.getNumberOfTestCases() for a in self.attributes)}
        #return reduce(lambda x,y:x*y.getNumberOfTestCases(), self.attributes, 1)

    
    def addParent(self, parent):
        self.parents.append(parent)

    def addChild(self, child):
        self.children.append(child)

    def addAttribute(self, att):
        self.attributes.append(att)


 
