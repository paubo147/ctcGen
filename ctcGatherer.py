from lxml import etree as ET
import time

import Util
import SMTLIBAssertionHandler

"""
A class instance is a possible instantiation of a configuration class. 
It consists of the name and the name-value pairs of the attributes on it.
"""
class ClassInstance:
    def __init__(self, cls, sk):
        self.clss=cls
        self.vals={}
        self.sortkey=sk

    def addValue(self, name, val):
        self.vals[name]=val

    def getXML(self, root):
        clel=ET.SubElement(root, "class")
        clel.set("name", self.clss.name)
        clel.set("sortkey", self.sortkey)
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

    def __str__(self):
        return self.clss.name+" "+ self.sortkey+" "+ str({k.name :v for k,v in self.vals.iteritems()})

class GenericTestCase:
    def __init__(self, mid):
        self.id=mid
        self.clsses=list()
    
    def addClass(self, c):
        self.clsses.append(c)
        

    def getXML(self, root):
        tcel=ET.SubElement(root, "testcase")
        tcel.set("id", str(self.id))
        for cl in sorted(self.clsses, key=lambda x: int(x.sortkey)):
            clel=cl.getXML(tcel)
        return tcel

    def __str__(self):
        return str(self.id)+":"+"\n".join([str(c) for c in self.clsses])

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
    #print res
    gtc=GenericTestCase(number)
    skeys={}
    clsses={}
    print "PATHS", p.paths
    print "RESULT", res.keys()
    for cls in res:
        clsname=cls[:cls.find("_")]
        if "sortkey" in cls:
            skeys[clsname]=res[cls]
        if "instance" in cls:
            if clsname in p.classes:
                #ctc=ClassInstance(p.classes[cls])
                att_val_pairs=dict(zip(p.classes[clsname].attributes, res[cls][1:]))
                clsses[clsname]=att_val_pairs
                #for a, v in att_val_pairs.iteritems():
                #    ctc.addValue(a, v)
            else: 
                raise Exception("Not possible: {0} not found in parse_result".format(cls[:cls.find("_")]))
        #gtc.addClass(ctc)

    
    for c in clsses:
        if skeys and c in skeys:
            ctc=ClassInstance(p.classes[c], skeys[c])
        else:
            ctc=ClassInstance(p.classes[c], "0")
        #print clsses[c]
        for a,v in clsses[c].iteritems():
            ctc.addValue(a,v)
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

    testCases=ET.SubElement(stats, "testCases")
    testCases.text=str(len(tcs))
    for tc in tcs:
        tcel=tc.getXML(root)
    return Util.get_pretty_XML(root)
