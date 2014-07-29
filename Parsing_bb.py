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

    def increaseLevel(self):
        self.level+=2
    
        

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
        return len(self.boundaries)

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
        dataType.increaseLevel()
        
    def increaseLevel(self):
        self.level+=1
        for c in self.content.values():
            c.increaseLevel()

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
        if self.isExclusive:
            return sum(self.content[x].getNumberOfTestCases() for x in self.content)
        else:
            return reduce(lambda x,y: x*y, [self.content[x].getNumberOfTestCases() for x in self.content])
            
    def getBoundaries(self):
        self.boundaries={x: self.content[x].getBoundaries() for x in sorted(self.content)}
        return self.boundaries

    
class SequenceType(ContainerType):
    pass

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

    #def getRanges(self):
        #self.ranges=self.content[0].getRanges()
    #    if not self.fixedRanges:
    #        self.ranges=self.content[0].getRanges()
    #        if self.additionalRanges:
    #            for r in self.additionalRanges:
    #                for a in self.additionalRanges[r]:
    #                    temptyp=self.ranges[a].keys()[0]
    #                    self.ranges[a]={temptyp:self.additionalRanges[r][a]}
                        #print "ADDRANGES: replace ", self.ranges[r][a], "with", self.additionalRanges[r][a],"ENDADDRANGES"
                    #self.ranges[r]=self.ranges[self.additionalRanges[r]
    #    return self.ranges

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
        return self.content[0].getNumberOfTestCases()


class AttrNode:
    def __init__(self, name):
        self.name=name
        self.dataType=None
        self.settings={}


    def getNumberOfTestCases(self):
        return self.dataType.getNumberOfTestCases()

    def __setitem__(self, key, value):
        self.settings[key]=value

         
    def setDataType(self, name, t):
        self.dataType=t
        self.dataType.increaseLevel()
        


class ClassNode:
    
    @property
    def name(self):
        return self.name

    @name.setter
    def name(self, value):
        self.name=value
        
    @name.deleter
    def name(self):
        del self.name

    def __init__(self, clsName, mimName=""):
        self.name=clsName
        self.mim= mimName
        self.parents=[]
        self.children= []
        self.attributes=[]
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
        return reduce(lambda x,y:x*y.getNumberOfTestCases(), self.attributes, 1)

    
    def addParent(self, parent):
        self.parents.append(parent)

    def addChild(self, child):
        self.children.append(child)

    def addAttribute(self, att):
        self.attributes.append(att)


 
