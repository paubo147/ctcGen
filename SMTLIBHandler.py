import Parsing_bb
import SMTLIBAssertionHandler

settings={
    Parsing_bb.GroundType : { "sortkey" : 4, "name" : "BASIC SORTS"},
    Parsing_bb.DerivedType : {"sortkey" : 3, "name" : "DERIVED TYPES"},
    Parsing_bb.EnumType : {"sortkey" : 2, "name" : "ENUM TYPES"},
    Parsing_bb.StructType : {"sortkey": 1, "name" : "STRUCTS"},
}

def sortkey(t):
    return settings[t]["sortkey"]

def name(t):
    return settings[t]["name"]


def initClassNodeSMT(t, parse_obj):
    print "SETTING UP CLASS NODE {0}".format(t.name)
    t.constructor="mk_{0}".format(t.name)
    t.instance_function="{0}_instance".format(t.name)
    t.attr_type_set=set()
    t.attribute_string=[]

    for a in t.attributes:
        
        t.attr_type_set.add(a.dataType.name)
        t.attribute_string.append("({0} {1})".format(a.name, a.dataType.name))
        #SMTLIBAssertionHandler.addBoundary(a.name, a.dataType.getBoundaries())
        SMTLIBAssertionHandler.addConstantAssertion(t.name, 
                                                    t.instance_function, 
                                                    a.name, 
                                                    a.dataType.name, 
                                                    a.dataType.getAssertableRanges(), 
                                                    parse_obj)
    t.attribute_string="".join(t.attribute_string)


def initGroundTypeSMT(t, p):
    print "SETTING UP GROUND TYPE {0}".format(t.name)
    #print "WAS HERE", t.name
    def transformDirect(x):
        t.annotatedValue=x
        return x

    def transformHex(x):
        #print id(t), t.name, "transforming", x, "to", str(int("0"+x[1:], 16))
        t.annotatedValue=str(int("0"+x[1:], 16))
        return int("0"+x[1:], 16)

    def transformNum(x):
        t.annotatedValue=x
        return int(x)

    def intToHex(i, n):
        plain_string=str(hex(i))[2:]
        ps=plain_string.zfill(n)
        return "#x{0}".format(ps)
    
    #boundaries
    def getSMTBoundaries(llst):
        if t.basetype=="bitvector":
            return [[intToHex(x[0], t.bits), intToHex(x[1], t.bits)] for x in llst]
        else:
            return llst

    t.getSMTBoundaries=getSMTBoundaries

    if t.basetype =="Int":
        t.transform=transformNum
    elif "bitvector"==t.basetype:#only workaround
        t.transform=transformHex
    else:
        t.transform=transformDirect
        

def initDerivedTypeSMT(t, p):
    print "SETTING UP DERIVED TYPE {0}".format(t.name)
    def transformDerivedType(x):
        temp=t.content[0].transform(x)
        t.annotatedValue=t.content[0].annotatedValue
        return temp

    t.transform=transformDerivedType
    #t.annotatedValue=t.content[0].annotatedValue

def initEnumTypeSMT(t, p):
    print "SETTING UP ENUM TYPE {0}".format(t.name)
    def transformEnum(x):
        t.annotatedValue={t.name:x}
        return x[x.find("_")+1:]


    def getSMTBoundaries(llst):
        if t.basetype=="ENUM":
            return [[t.name+"_"+x[0]] for x in llst]

    t.getSMTBoundaries=getSMTBoundaries
    #t.smtMembers=[t.name+"_"+x for x in t.members.keys()]
    t.transform=transformEnum

def initStructTypeSMT(t, p):
    print "SETTING UP STRUCT TYPE {0}".format(t.name)
    def transformStructExclusive(x):
        temp=t.content[x[0]].transform(x)
        t.annotatedValue=t.content[x[0]].annotatedValue
        return temp

    def transformStruct(x):
        if t.name in p.delimiter:
            delim=p.delimiter[t.name]
        else:
            delim="   "#FOR GENERAL STRUCTS (default value) 
        tmp=[]
        annVal=[]
        i=1
        for c in t.sortkey:
            tmp.append((t.content[c], x[i]))
            annVal.append((c, x[i]))
            i+=1
        t.annotatedValue={t.name:dict(annVal)}
        ret=delim.join(str(s[0].transform(s[1])) for s in tmp)
        return ret
            
        
    t.mk_name="mk_{0}".format(t.name)
    t.pseudo_name="{0}_dt".format(t.name)
    t.accessors=[]
    #print t.name
    if t.isExclusive:
        for x in t.content:
            #print "\t", x
            tmp=["(", x]
            for y in t.content[x].content:
                
                #print "\t\t", y, t.content[x].content[y].name
                tmp.append("(")
                tmp.append(y)
                tmp.append(t.content[x].content[y].name)
                tmp.append(")")
            tmp.append(")")
            #print "\t", tmp
            t.accessors.append(tmp)
        t.transform=transformStructExclusive
    else:
        i=1
        for x in sorted(t.content):
            t.accessors.append((x, t.content[x].name))
            i+=1
        t.transform=transformStruct

def getGroundTypeSMT(t, smtgen, parse_obj):
    return smtgen.get_smt_sort(t.name, parse_obj.xml2SMT[t.name])

def getDerivedTypeSMT(t, smtgen, parse_obj):
    return smtgen.get_smt_sort(t.name, t.content[0].name)

def getEnumTypeSMT(t, smtgen, parse_obj):
    return smtgen.get_smt_datatypes("", t.name+" "+(" ".join(t.members.keys())))

def getStructTypeSMT(t, smtgen, parse_obj):
    if not t.isHead:
        return ""

    if t.isExclusive:
        definition=[smtgen.get_smt_n_accessor(len(t.accessors)+1, onlyOuterPar=True)
                    .format(t.pseudo_name, *[" ".join(x) for x in t.accessors])[1:-1]]
        datatypes=""
        return_value=t.pseudo_name
    else:
        definition=[t.pseudo_name, "(", t.mk_name]+[smtgen.get_smt_n_accessor(2).format(*x) for x in t.accessors]+[")"]
        datatypes=" ".join(set([x[1] for x in t.accessors]))
        return_value="({0} {1})".format(t.pseudo_name, datatypes)
    return "\n".join([smtgen.get_smt_datatypes(datatypes, " ".join(definition)), smtgen.get_smt_sort(t.name, return_value)])




def getClassNodeSMT(t, smtgen):
    ret=[smtgen.get_smt_datatypes(" ".join(t.attr_type_set), 
                                  "".join([t.name,
                                           " (", 
                                           t.constructor, 
                                           " ", 
                                           t.attribute_string,
                                           ")"]
                                          )
                                  ),
         smtgen.get_smt_declare_fun(t.instance_function, 
                                    "", 
                                    t.name, 
                                    " ".join(t.attr_type_set)),
         "\n"]
    for a in sorted(SMTLIBAssertionHandler.constantAssertions[t.name]):
        ca=SMTLIBAssertionHandler.constantAssertions[t.name][a]
        ret.append(smtgen.get_smt_range_assertion(a, ca["type"], ca["ranges"]))
    ret.append("\n")
    return "".join(ret)


def getAssertion(a, smtgen):
    yesNo="_not" if a.neg else ""
    howmanyType="_value" 
    if a.typ in ("INT", "BITVECTOR"):
            howmanyType="_range"
    st="get_smt{0}{1}_assertion".format(yesNo, howmanyType)
    func=getattr(smtgen, st)
    #print func(a.field, a.typ, a.lst)
    return func(a.field, a.typ, a.lst)


def testerAssertionsIter():
    for a in SMTLIBAssertionHandler.testerAssertions:
        setattr(a.__class__, "getSMT", getAssertion)
        yield a
