import re
from SMTLIB_code_snippets import *
from TestStrategy import *
from Util import *
import xml.etree.cElementTree as ET
import time

#RE_MODEL=r"\(model *(?P<model>.*) \)"
#RE_FUN_MATCHER=r"\(define\-fun *(?P<func_name>.+) *\(\) *\((?P<func_signature>.+)\) *\((?P<mk_func>.+)\)\)"

class SMTInterpreter:
    def __init__(self, classes, strategy):
        self.classes=classes
        self.strategy=strategy#check if we can get this as argument
        self.testCases=list()
        self.testedValues=dict()

        
    def getRealValue(self, value, typ):
        if typ == "String":
            # converts #xdeadbeef to a string
            return str(int(value[2:], 16))
        elif typ=="IPV4":
            # converts (mk_IPV4_dt #x80 #x00 #x00 #x00) to "128.0.0.0"
            return ".".join([str(int(x[2:], 16)) for x in value[1:][:-1].split()[1:]]) 
        else:
            return value

    """
    This function reads a string extracted from the solver-result and stores it internally
    Example:
    (define-fun vRF_instance () (VRF Int (_ BitVec 32) (IPV4_dt (_ BitVec 8)))    (mk_VRF #x00000000 1 0 (mk_IPV4_dt #x80 #x00 #x00 #x00)))
    
    this function takes the definition of the VRF-datatype and stores name-value pairs of this resulting test-instance
    """
    def interpretAndStore(self, s):
        m=re.match(RE_DEF_FUN, s)
        md=m.groupdict()
        val_string=" ".join(md["mk_func"].split())+" "
        
        vals=[x.strip() for x in re.findall(RE_ACCESSOR_LIST, val_string)]
        my_class=(x for x in self.classes if x.constructor==vals[0]).next()
        vals=vals[1:]
        if my_class is None:
            raise Exception("SMTInterpreter: Could not find class: "+my_class+" inside local class-instances") #TODO error handling
        attributes=my_class.attribute_name_order
        types=my_class.attribute_type_order
        #print attributes
        #print vals
        #print types
        for i in range(len(attributes)):
            vals[i]=self.getRealValue(vals[i], types[i])
            if attributes[i] in self.testedValues:
                self.testedValues[attributes[i]].add(vals[i])
            else:
                self.testedValues[attributes[i]]=set([vals[i]])

        #NOW STORE CLASS, VARIABLE and VALUE into a triple and a list
        #TODO handle multiple classes
        self.testCases.append({my_class: dict(zip(attributes, vals))})
        self.strategy.addTestCase({my_class: dict(zip(attributes, vals))})
        
        #print "ALREADY TESTED:", self.testedValues
        
            
              
    """
    Takes a raw string, interprets and stores it and returns the negated 
    """
    def storeAndReturn(self, answer,facts):
        #TODO handle multiple classes, maybe re.match is to be replaced with re.findall
        work_string=re.match(RE_MODEL, answer).groupdict()["model"]
        self.interpretAndStore(work_string)
        #both add and remove are lists with strings to be added/removed from the facts
        (add,remove)=self.strategy.getNegated(work_string)
        
        #TODO getNegated should return a tuple with assertions to be removed and 
        #print (add, remove)
        return (add, remove)


    def getXML(self):
        root=ET.Element("testcases")
        i=0
        date=ET.SubElement(root, "creationDate")
        date.text=time.strftime("%c")
        for tc in self.testCases:
            tcel=ET.SubElement(root, "testcase")
            tcel.set("id", str(i))
            for cl in tc:
                clel=ET.SubElement(tcel, "class")
                clel.set("name",cl.name)
                for at in tc[cl]:
                    atel=ET.SubElement(clel, "attribute")
                    atel.set("name", at)
                    atel.text=tc[cl][at]
            

            i+=1
        return getPrettyXML(root)
