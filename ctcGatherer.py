from lxml import etree as ET
import time

import Util
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
        clel.set("name", self.clss.name)
        for at in self.vals:
            #realVal=at.dataType.transform(self.vals[at])
            #print at.name, self.vals[at], at.dataType.transform(self.vals[at])
            atel=ET.SubElement(clel, "attribute")
            atel.set("name", at.name)
            atel.text=str(at.dataType.transform(self.vals[at]))
        return clel

    def __eq__(self, other):
        if isinstance(other, ClassInstance):
            return self.clss==other.clss and self.vals == other.vals
        return False

class GenericTestCase:
    def __init__(self, mid):
        self.id=mid
        self.clsses=list()
    
    def addClass(self, c):
        self.clsses.append(c)
        

    def getXML(self, root):
        tcel=ET.SubElement(root, "testcase")
        tcel.set("id", str(self.id))
        for cl in self.clsses:
            clel=cl.getXML(tcel)
        return tcel

    def __eq__(self, other):
        if isinstance(other, GenericTestCase):
            for c in self.clsses:
                if c not in other.clsses:
                    return False
            return True
        return False


testCases=[]


def runnable():
    return SMTLIBAssertionHandler.runnable()

def process(p, res, number):
    """processes a parsed result from a SMT solver.
    Stores it into an own object.
    
    Keyword arguments:
    p -- the parse-object
    res -- the parsed result
    number -- the number of SMT-run (acts as an identifier

    Calls also the SMTLIBAssertionHandler to add assertions for the next run.
    """
    gtc=GenericTestCase(number)
    for cls in res:
        ctc=ClassInstance(p.classes[cls])
        att_val_pairs=dict(zip(p.classes[cls].attributes, res[cls][1:]))
        for a, v in att_val_pairs.iteritems():
            #print a.dataType, v
            #a.dataType.transform(v)
            ctc.addValue(a, v)
        gtc.addClass(ctc)
    testCases.append(gtc)
    SMTLIBAssertionHandler.checkTestCase(gtc, p)


def getXML(deltaTime, tcs):
    """returns the gathered test-cases in XML format"""
    root=ET.Element("testcases")
    stats=ET.SubElement(root, "statistics")
    date=ET.SubElement(stats, "creationDate")
    date.text=time.strftime("%c")

    timee=ET.SubElement(stats, "timeDelta")
    timee.text=str(deltaTime)
    for tc in tcs:
        tcel=tc.getXML(root)
    return Util.get_pretty_XML(root)
