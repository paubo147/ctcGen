import string

constantAssertions={}
testerAssertions={}
boundaries={}

def addBoundary(n, b):
    boundaries[n]=b

def addConstantAssertion(cls, func, attr, name, rang, parse_obj):
    if cls not in constantAssertions:
        constantAssertions[cls]={}
    if "NOT_DEFINED" not in rang:
        for x in rang:
            #print x
            if x in parse_obj.xml2SMT:
                constantAssertions[cls]["({0} {1})".format(attr, func)]={
                    "type": parse_obj.dataTypes[name].basetype.upper(),
                    "ranges": rang[x]
                    }
            else:
                if x in parse_obj.dataTypes:
                    addConstantAssertion(cls, func, attr, name, rang[x], parse_obj)
                    #print "\tCALL_RECURSIVE", func, attr, name, rang[x]
                else:
                    for y in rang[x]:
                        #if attr=="routeDistinguisher":
                        #    print "HERE", "({0} {1})".format(attr, func), x, y, rang[x][y], "parse_obj"
                        addConstantAssertion(cls, "({0} {1})".format(attr, func), x, y, {y:rang[x][y]}, parse_obj)
                        #print "\tCALL_RECURSIVE", x, "({0} {1})".format(attr, func), y, rang[x][y], "parse_obj"


def handleBoundary():
    #1. for 
    pass


def identifyBoundary(prefix, vals, a, dt, tempBound):
    #print dt.type
    if dt.type in ("GROUND", "ENUM"):
        handleBoundary()
        pass
        #print "BOUNDARYBNDS:", dt.name, dt.basetype, tempBound
        print "BOUNDARY:", dt.type, prefix, dt.name, vals, tempBound[dt.name]
    else:
        if dt.type=="STRUCT" and dt.isExclusive:
            if vals[0] in dt.content:
                #print "RECURSIVE", "({0} {1})".format(choice, prefix), vals[1:], a, dt.content[choice], tempBound[choice]
                identifyBoundary("({0} {1})".format(vals[0], prefix), vals[1:], a, dt.content[vals[0]], tempBound[vals[0]])
                
        else:
            if len(dt.content)==1:
                identifyBoundary(prefix, vals, a, dt.content[0], tempBound)
            else:
                for b, l in tempBound.iteritems():
                    if dt.mk_name==vals[0]:
                        newVals=vals[1:][tempBound.keys().index(b)]
                    else:
                        newVals=vals
                    
                    identifyBoundary("({0} {1})".format(b, prefix), newVals, a, dt.content[b], tempBound[b])
                
def checkTestCase(gtc, p):
    for c in gtc.clsses:
        for a, v in c.vals.iteritems():
            #identifyBoundary("({0} {1})".format(a.name, c.clss.instance_function), v, a, a.dataType, boundaries[a.name])


            print a.name, a.dataType.transform(v)
