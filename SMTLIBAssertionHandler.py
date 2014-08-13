import string





boundaries={}
removedBoundaries={}
results="P" #or "N"
strategy=1 #1: each boundary once, 2: exponential blowup

class AssertionSet(list):
    def __init__(self):
        super(AssertionSet, self).__init__()

    def add(self, ass):
        if ass in self:
            self.remove(ass)
        self.append(ass)

class Assertion:
    def __init__(self, field, lst, typ, neg=False):
        self.field=field
        self.lst=lst
        self.neg=neg
        self.typ=typ

    def __eq__(self, other):
        return self.field==other.field

    def __repr__(self):
        return self.field+", "+str(self.lst)

constantAssertions={}
testerAssertions=AssertionSet()

def runnable():
    #TODO should switch to negative tests, i.e., results="N" if testerAssertions ==0
    return len(testerAssertions)!=0
    

def addBoundary(n, b):
    boundaries[n]=b

def addConstantAssertion(cls, func, attr, name, rang, parse_obj, isNullable):
    if cls not in constantAssertions:
        constantAssertions[cls]={}
    if "NOT_DEFINED" not in rang:
        for x in rang:
            if x in parse_obj.dataTypes and parse_obj.dataTypes[name].type=="GROUND":
                constantAssertions[cls]["({0} {1})".format(attr, func)]={
                    "type": parse_obj.dataTypes[name].id_type.upper(),
                    "ranges": rang[x]
                    }
            else:
                if x in parse_obj.dataTypes and parse_obj.dataTypes[x].type=="GROUND":
                    addConstantAssertion(cls, func, attr, x, rang, parse_obj, isNullable)
                elif x in parse_obj.dataTypes:
                    addConstantAssertion(cls, func, attr, x, rang[x], parse_obj, isNullable)
                else:
                    for y in rang[x]:
                        addConstantAssertion(cls, "({0} {1})".format(attr, func), x, y, {y:rang[x][y]}, parse_obj, isNullable)
                        
def handleBoundary(tcid, s, t, value, boundary, bt):
    typ=bt.upper()
    #print "BND", tcid, bt.upper(), s, value, boundary
    if not boundary:
        return 
    if s not in boundaries:
        boundaries[s]=list(boundary)
    to_remove=[]
    for b in boundaries[s]:
        if len(b) != 0:
            #print b[0], "<=", t.transform(value), "<=", b[-1]
            if b[0] <= t.transform(value) <= b[-1]:
                #print s, "tested", b, "with", t.transform(value)
                to_remove=b

    if s not in removedBoundaries:
        removedBoundaries[s]=[]
   
    if to_remove and to_remove in boundaries[s]:
        boundaries[s].remove(to_remove)
        removedBoundaries[s].append(to_remove)
    else:
        #print "DONE WITH", s, boundaries[s]
        return
    
    #if "routeDistinguisher" in s:
    #    print s, boundaries[s]

    #TODO here is the point where we have to change values
    #print "CHANGE BOUNDARIES", t.type, t.name, t.basetype, t.getSMTBoundaries(removedBoundaries[s]), removedBoundaries[s]
    if len(boundaries[s])==0:
        for ta in testerAssertions:
            if ta.field==s:
                break

        testerAssertions.remove(ta)        
        #print ta, "REMOVED", 
        del ta
        boundaries[s]=[]
        #print testerAssertions
    else:
        if len(boundaries[s]) < len(removedBoundaries[s]):
            a=Assertion(s, t.getSMTBoundaries(boundaries[s]), typ)
        else:
            a=Assertion(s, t.getSMTBoundaries(removedBoundaries[s]), typ, True)
        testerAssertions.add(a)

def identifyBoundary(tcid, prefix, vals, a, dt, tempBound):
     #print dt.type
    if dt.type in ("GROUND", "ENUM"):
        #print tcid, prefix, dt, vals[dt.name] if dt.name in vals else vals, tempBound[dt.name] if dt.name in tempBound else tempBound, dt.basetype
        handleBoundary(tcid, prefix, 
                       dt, 
                       vals[dt.name] if dt.name in vals else vals, 
                       tempBound[dt.name] if dt.name in tempBound 
                       else tempBound,
                       dt.basetype)
    else:
        if dt.type=="STRUCT" and dt.isExclusive:
            if vals.keys()[0] in dt.content:
                #print "EX_STRUCT", prefix, vals.keys()[0], vals.values(), dt.content[vals.keys()[0]].type
                oldPrefix="({0} {1})".format(vals.keys()[0], prefix)
                identifyBoundary(tcid, prefix, vals.values()[0], a, dt.content[vals.keys()[0]], tempBound[vals.keys()[0]])
                
        else:
            if len(dt.content)==1:
                #print "VAL(DE)", lvl, a.name, vals
                tb=tempBound
                if dt.content[0].name in tempBound:
                    tb=tempBound[dt.content[0].name]
                identifyBoundary(tcid, prefix, vals, a, dt.content[0], tb)
            else:
                for b, l in tempBound.iteritems():
                    #print tempBound.keys(), b
                    #print b, dt.name, dt.mk_name, vals
                    if dt.name in vals:
                        newVals=vals[dt.name][b]#tempBound.keys().index(b)]
                    elif dt.mk_name in vals:
                        newVals=vals[dt.mk_name][b]#tempBound.keys().index(b)]
                    else:
                        newVals=vals[b]
                    #print "VAL(OT)", lvl, a.name, newVals
                    identifyBoundary(tcid, "({0} {1})".format(b, prefix), newVals, a, dt.content[b], tempBound[b])
                
def checkTestCase(gtc, p):
    for c in gtc.clsses:
        for a, v in c.vals.iteritems():
            plain_values=a.dataType.transform(v)
            #print a.dataType.annotatedValue, v
            #WE NEED A PARAMETER WHICH GUIDES THE ATTRIBUTE TESTING PROCESS
            #1 stands for "exactly-once" semantic (each boundary once)
            #2 stands for "at-most-once" semantic (one test for each class)
            #3 stands for "at-least-once" semantic (each combinatory boundary)

            #case for exactly-once
            identifyBoundary(gtc.id, "({0} {1})".format(a.name, c.clss.instance_function), a.dataType.annotatedValue, a, a.dataType, a.dataType.getBoundaries())

            #case for 2
            #instance-bursting or coverage arrays

    #for ta in testerAssertions:
    #    print "\t", ta

