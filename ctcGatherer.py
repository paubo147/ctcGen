import re
import time

from lxml import etree as ET

import Util
import SMTController
import SMTLIBParser
import math
import string
import SMTLIBAssertionHandler

"""
A class instance is a possible instantiation of a configuration class. 
It consists of the name and the name-value pairs of the attributes on it.
"""
class ClassInstance:
    def __init__(self, cls):
        self.clss=cls
        self.vals={}

    def addValue(self, name, val):
        self.vals[name]=val

    def getXML(self, root):
        clel=ET.SubElement(root, "class")
        clel.set("name", self.name)
        for at in self.vals:
            atel=ET.SubElement(clel, "attribute")
            atel.set("name", at)
            atel.text=self.vals[at]
        return clel

    def __eq__(self, other):
        if isinstance(other, ClassInstance):
            return self.name==other.name and self.vals == other.vals
        return False

"""
A generic test case consists of an identifier as well 
as a list of class instances.
"""
class GenericTestCase:
    def __init__(self, id):
        self.id=str(id)
        self.clsses=list()
    
    def addClass(self, c):
        self.clsses.append(c)
        

    def getXML(self, root):
        tcel=ET.SubElement(root, "testcase")
        tcel.set("id", self.id)
        for cl in self.clsses:
            clel=cl.getXML(tcel)
        return tcel

    #Wrong! Should exclude the number of already tested cases
    def getCoverage(self):
        ret=0
        for c in self.clsses:
            ret+=len(c.vals)
        return ret

    def __eq__(self, other):
        if isinstance(other, GenericTestCase):
            for c in self.clsses:
                if c not in other.clsses:
                    return False
            return True
        return False


testCases=[]
oldConditions=[]
oldAssertions=[]


def runnable():
    return len(testCases) < overallTestCases

def process(p, res, number):
    gtc=GenericTestCase(number)
    for cls in res:
        ctc=ClassInstance(p.classes[cls])
        att_val_pairs=dict(zip(p.classes[cls].attributes, res[cls][1:]))
        for a, v in att_val_pairs.iteritems():
            #print a.dataType, v
            #a.dataType.transform(v)
            ctc.addValue(a, v)
        gtc.addClass(ctc)
    SMTLIBAssertionHandler.checkTestCase(gtc, p)

"""
method to be called from outside. Handles the whole generation process
"""
def processSMTLIBFacts(facts, smt_cmd, smtlib_gen, testCases):
    runNumber=0
    coverage=0
    while True:
        runNumber+=1
        plain_result=SMTController.runSMT(facts, smt_cmd)
        if plain_result is not None:
            res=SMTLIBParser.parse(plain_result)
            coverage+=store(facts, res, runNumber, smtlib_gen)
            (add, remove)=getNewAssertions(facts, res, smtlib_gen)
            for a in add:
                facts.addTesterAssertion(a)
            for r in remove:
                facts.removeTesterAssertion(r)
        else:
            raise Exception("CTCGatherer: SMT Solver result undefined!")

    print runNumber+1, " TESTCASES PRODUCED. Reached coverage: ", math.log(coverage)
    return testCases
    

"""
sets the condition of the main loop
"""
def toRun(runNumber, c, maxCoverage):
    if c>0:
        perc=(100*math.log(c))/maxCoverage
        print runNumber, ":", math.log(c), "vs", maxCoverage, "(", perc, "%)"
        return math.log(c)<maxCoverage
    else:
        return c<maxCoverage

        
"""
Returns the SMT value into a xml-compatible type
"""
def getRealValue(facts, value, typ):
    if typ in facts.specialDatatypes:
        temp=facts.specialDatatypes[typ]["produce_string"]
        i=0
        for e in range(len(temp)):
           if temp[e]=="field":
               temp[e]="{"+str(i)+"}"
               i+=1
        #maybe put q1.q2.q3.q4 inside produce_string
        
        temp="".join(temp)
        temp=temp.format(*[str(int(x[2:], 16)) for x in value[1:]])
        return temp
    if typ in facts.specialExclusiveDatatypes:
        temp=facts.specialExclusiveDatatypes[typ]["options"][value[0]]["produce_string"]
        i=0
        for e in range(len(temp)):
           if temp[e]=="field":
               temp[e]="{"+str(i)+"}"
               i+=1
        #maybe put q1.q2.q3.q4 inside produce_string
        
        temp="".join(temp)
        temp=temp.format(*[str(int(x[2:], 16)) for x in value[1:]])
        return temp
    if typ in facts.structDatatypes:
        #TODO check what to produce if structs
        return " ".join(value[1:])
    if typ == "String":
        return Util.get_random_string()
    else:
        return value
    
"""
This function reads a string extracted from the solver-result and stores it internally
Example:
(define-fun vRF_instance () (VRF Int (_ BitVec 32) (IPV4_dt (_ BitVec 8)))    (mk_VRF #x00000000 1 0 (mk_IPV4_dt #x80 #x00 #x00 #x00)))
    
this function takes the definition of the VRF-datatype and stores name-value pairs of this resulting test-instance
"""
def store(facts, result, runNumber,smtlib_gen):
    gtc=GenericTestCase(runNumber)
    for c in result:
        my_class=(x for x in facts.classDatatypes if x.name==c).next()
        attributes=my_class.attribute_name_order
        
        types=my_class.attribute_type_order
        values=[getRealValue(facts, result[c][i+1], facts.derivedSorts.get(types[i], types[i])) for i in range(len(attributes))]
        gtc.addClass(ClassInstance(c, dict(zip(attributes, values))))
    idealCoverage=gtc.getCoverage()

    #TODO check if gtc is inside the other test-cases
    cov=0
    if gtc not in testCases:
        cov=gtc.getCoverage()
    testCases.append(gtc)
    return cov
    

        
       
def valueHelper(facts, val, typ):
    if typ in facts.specialDatatypes or typ in facts.structDatatypes or typ in facts.specialExclusiveDatatypes:
        return "("+(" ".join(val))+")"
    return val
 

def deduceType(typ, facts, res):
    if typ == "Int":
        return (True, int(res))
    elif typ == "Bool":
        return (True, (res.upper()=="TRUE"))
    elif typ in facts.specialBuildingBlocks:
        if facts.specialBuildingBlocks[typ]["type"]=="bitvector":
            return (True, int("0"+res[1:], 16))
        else:
            print "NEVER HAD THIS SITUATION", typ, res
    elif typ in facts.derivedSorts:
        return deduceType(facts.derivedSorts[typ], facts, res)
    elif typ in facts.enumDatatypes:
        return (True, res[res.find("_")+1:])
    elif typ in facts.structDatatypes:
        types=[x["dataType"] for x in facts.structDatatypes[typ][1]]
        names=[x["name"] for x in facts.structDatatypes[typ][1]]
        return (False,  {names[i]: deduceType(types[i], facts, res[1:][i])[1] for i in range(len(types))})
    elif typ in facts.specialExclusiveDatatypes:
        field=facts.specialExclusiveDatatypes[typ]["options"][res[0]]["fields"].keys()
        types=[x["baseType"] for x in facts.specialExclusiveDatatypes[typ]["options"][res[0]]["fields"].values()]
        return (False, {(res[0],field[i]) : deduceType(types[i], facts, res[1:][i])[1] for i in range(len(types))})
    elif typ in facts.specialDatatypes:
        fields=sorted(facts.specialDatatypes[typ]["fields"])
        types=[facts.specialDatatypes[typ]["fields"][x]["baseType"] for x in sorted(facts.specialDatatypes[typ]["fields"])]
        return (False, {fields[i] : deduceType(types[i], facts, res[1:][i])[1] for i in range(len(types))})
    else:
        print "NOTYPE", typ, res
        return (False, None)



def removeBoundary(facts, my_class, result):
    #print "BEGIN BOUNDARY"
    ret={}
    for i in range(len(result[1:])):
        typ=my_class.attribute_type_order[i]
        boundary=my_class.attribute_boundaries[typ]
        attribute_name=my_class.attribute_name_order[i]
        if boundary:
            #typ=my_class.attribute_type_order[i]
            simple,value=deduceType(typ, facts, result[i+1])
            removed_boundary=None
            accessor=None
            if simple:
                for b in boundary:
                    if len(b)==1: #SINGLE VALUES IN LISTS (ENUMS; STIRNG)
                        #delete direct
                        if value in b:
                            ret["({0} {1})".format(attribute_name, my_class.instance_function)]={"type":typ, "boundaries":b}
                            boundary.remove(b)
                            
                            if len(boundary)==0:
                                print "NOTHING MORE TO TEST: ({0} {1})".format(attribute_name, my_class.instance_function)
                            
                            #HOOK TO RETURN THE BOUNDARY
                            
                    else:
                        if min(b) <= value <= max(b):
                            ret["({0} {1})".format(attribute_name, my_class.instance_function)]={"type":typ, "boundaries":b}
                            boundary.remove(b)
                            if len(boundary)==0:
                                print "NOTHING MORE TO TEST: ({0} {1})".format(attribute_name, my_class.instance_function)
                            #HOOK TO RETURN THE BOUNDARY
            else:
                for v in value:
                    if v in boundary or "_".join(v) in boundary:
                        field_accessor = v if v in boundary else "_".join(v)
                        pattern="({0} ({1} {2}))".format(field_accessor, attribute_name, my_class.instance_function)
                        if v not in boundary:
                            num=re.findall(r"\d+", field_accessor)[0]
                            acc1=field_accessor[0:field_accessor.find("_")]+"_"+num
                            acc2=field_accessor[field_accessor.find("_",len(acc1))+1:]+"_"+num
                            pattern="({0} ({1} ({2} {3})))".format(acc1, acc2, attribute_name, my_class.instance_function)
                        singleVal=value[v]
                        for b in boundary[field_accessor]:
                            if min(b) <= singleVal <= max(b):
                                removed_boundary=b
                                boundary[field_accessor].remove(b)
                                if "({0} ({1} {2}))".format(v, attribute_name, my_class.instance_function) in ret:
                                    print "OLD VALUE FOUND ({0} ({1} {2}))".format(field_accessor, attribute_name, my_class.instance_function)
                                ret[pattern]={"type":typ, "boundaries":b}
                                #HOOK TO RETURN THE BOUNDARY
                                if len(boundary)==0:
                                    print "NOTHING MORE TO TEST: ({0} ({1} {2}))".format(field_accessor, attribute_name, my_class.instance_function)
                        
                    else:
                        print "ERROR", v, "not in ", boundary
        else:
            print "NO BOUNDARY", typ

    #print "VALUES", my_class.name, ret
    return ret
    #print "END BOUNDARY"


"""
Identifies the assertions to be added/removed and returns them as a tuple
"""
def getNewAssertions(facts, result, smtlib_gen):
    add=[]
    remove=[]
    for c in result:
        try:
            my_class=(x for x in facts.classDatatypes if x.name==c).next()
        except StopIteration:
            print "ctcGatherer: Could not identify class {0}".format(c)
            exit(-1)
           
        types=["x"]+my_class.attribute_type_order
        #for each index in the types from the attributes of the class, translate it (specialDatatypes) and create a parenthesized string for the assertion
        prnt=False
        if prnt:
            print "CLASS:", my_class.name
            print "\tTYPES\t\t", types
            print "\tATTRIBUTES\t", my_class.attribute_name_order
            print "\tRESULTS\t\t", result[c]
            print "\tREMOVED", 
            for att, b in removeBoundary(facts, my_class, result[c]).iteritems():
                print "\t\t\t", att, "->", b
        
        #removedBoundaries
        for att, b in removeBoundary(facts, my_class, result[c]).iteritems():
            bound=b["boundaries"]
            typ=b["type"]
            if typ in facts.derivedSorts:
                if len(bound)==1:
                    print smtlib_gen.get_smt_assertion(smtlib_gen.get_smt_negation(att, bound[0]))
                else:
                    #TODO check for other assertions
                    #general_bounds=facts.rangeAssertions[att]["ranges"]
                    print smtlib_gen.get_smt_assertion(smtlib_gen.get_smt_not(smtlib_gen.get_smt_range_single(att, facts.derivedSorts[typ], min(bound), max(bound))))
                #print "DERIVED:", att, typ, facts.derivedSorts[typ], bound
            elif typ in facts.enumDatatypes:
                realValue=typ+"_"+bound[0]
                print smtlib_gen.get_smt_assertion(smtlib_gen.get_smt_negation(att, realValue))
            elif typ in facts.structDatatypes:
                print "STRUCT", att, typ, facts.structDatatypes[typ], bound
            else:
                print "???", att, typ

        res_string=" ".join(["("]+[valueHelper(facts, result[c][i], types[i]) for i in range(len(types))]+[")"])
        assertion=smtlib_gen.get_smt_assertion(smtlib_gen.get_smt_negation(my_class.instance_function, res_string))
        add.append(assertion)
            
    return (add, remove)

"""
returns the XML representation of the test-case-set
""" 
def getXML(deltaTime, tcs):
    root=ET.Element("testcases")
    stats=ET.SubElement(root, "statistics")
    date=ET.SubElement(stats, "creationDate")
    date.text=time.strftime("%c")

    timee=ET.SubElement(stats, "timeDelta")
    timee.text=str(deltaTime)
    for tc in tcs:
        tcel=tc.getXML(root)
    return Util.get_pretty_XML(root)
