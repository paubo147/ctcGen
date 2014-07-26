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
    t.constructor="mk_{0}".format(t.name)
    t.instance_function="{0}_instance".format(t.name)
    t.attr_type_set=set()
    t.attribute_string=[]
    #t.getBoundaries()
    for a in t.attributes:
        if a.name=="ttl":
            print a, a.dataType.name, a.dataType.content[0].name, a.dataType.fixedRanges, a.dataType.getBoundaries()

        t.attr_type_set.add(a.dataType.name)
        t.attribute_string.append("({0} {1})".format(a.name, a.dataType.name))
        #print "RANGES", a.name, a.dataType.getRanges()
        #print "BOUNDARIES", a.name, a.dataType.getBoundaries()
        SMTLIBAssertionHandler.addBoundary(a.name, a.dataType.getBoundaries())
        SMTLIBAssertionHandler.addConstantAssertion(t.name, 
                                                    t.instance_function, 
                                                    a.name, 
                                                    a.dataType.name, 
                                                    a.dataType.getAssertableRanges(), 
                                                    parse_obj)
    t.attribute_string="".join(t.attribute_string)


def initGroundTypeSMT(t, p):
    #print "WAS HERE", t.name
    def transformDirect(x):
        return x

    def transformHex(x):
        return str(int("0"+x[1:], 16))

    if t.basetype in ("Bool", "Int"):
        t.transform=transformDirect
    elif "BitVec" in t.basetype or "bitvector"==t.basetype:#only workaround
        t.transform=transformHex
    else:
        raise Exception("No function definition for ", t.basetype, t.name, t.type)


def initDerivedTypeSMT(t, p):
    t.transform={t.name:t.content[0].transform}

def initEnumTypeSMT(t, p):
    def transformEnum(x):
        return {t.name:x[x.find("_")+1:]}


    t.smtMembers=[t.name+"_"+x for x in t.members.keys()]
    t.transform=transformEnum

def initStructTypeSMT(t, p):
    def transformStructExclusive(x):
        return t.content[x[0]].transform(x)

    def transformStruct(x):
        if t.name in p.delimiter:
            delim=p.delimiter[t.name]
        else:
            delim="   "#FOR GENERAL STRUCTS (default value)
        tmp= zip(t.content.values(), x[1:])
        
        #return delim.join(s[0].transform(s[1]) for s in tmp)
            
        
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
    if t.level > 1:
        return smtgen.get_smt_sort(t.name, parse_obj.xml2SMT[t.name])
    return ""

def getDerivedTypeSMT(t, smtgen, parse_obj):
    return smtgen.get_smt_sort(t.name, t.content[0].name)

def getEnumTypeSMT(t, smtgen, parse_obj):
    return smtgen.get_smt_datatypes("", t.name+" "+(" ".join(t.smtMembers)))

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
    for a in SMTLIBAssertionHandler.constantAssertions[t.name]:
        ca=SMTLIBAssertionHandler.constantAssertions[t.name][a]
        ret.append(smtgen.get_smt_range_assertion(a, ca["type"], ca["ranges"]))
    ret.append("\n")
    return "".join(ret)
