from time import strftime

import CtcTypes
import SMTLIBAssertionHandler

import Util

def get_preface(smtlib_gen, files):
    return [smtlib_gen.get_smt_comment("mp_files:\t{0}".format(",".join(files))),
            smtlib_gen.get_smt_comment("creation-date:\t{0}".format(strftime("%c"))),
            smtlib_gen.get_smt_comment("created by:\tctcGen-tool v 1.0"),
            smtlib_gen.get_smt_comment("author:\tPaul Borek"),
            "\n",
            smtlib_gen.get_smt_datatypes("T", "Attribute null (data (value T) (key Bool))"),
            "\n"]

settings={
    CtcTypes.GroundType : { "sortkey" : 4, "name" : "BASIC SORTS"},
    CtcTypes.DerivedType : {"sortkey" : 3, "name" : "DERIVED TYPES"},
    CtcTypes.EnumType : {"sortkey" : 2, "name" : "ENUM TYPES"},
    CtcTypes.StructType : {"sortkey": 1, "name" : "STRUCTS"},
    }

def sortkey(t):
    return settings[t]["sortkey"]

def name(t):
    return settings[t]["name"]


def initClassNodeSMT(t, smtgen, parse_obj):
    t.constructor="mk_{0}".format(t.name)
    t.instance_function="{0}_instance".format(t.name)
    t.key_function="{0}_key".format(t.name)
    t.attr_type_set=set()
    t.attribute_string=[]

    for a in t.attributes:
        if "key" in a.settings:
            t.key_attribute=a

        #t.attr_type_set.add("(Attribute {0})".format(a.dataType.name))
        #t.attribute_string.append("({0} (Attribute {1}))".format(a.name, a.dataType.name))
        t.attr_type_set.add(a.dataType.name)
        t.attribute_string.append("({0} {1})".format(a.name, a.dataType.name))
        t.nillable=False
        if "isNillable" in a:
            t.nillable=True
        
        SMTLIBAssertionHandler.addConstantAssertion(t.name, 
                                                    t.instance_function, 
                                                    a.name, 
                                                    a.dataType.name, 
                                                    a.dataType.getAssertableRanges(), 
                                                    parse_obj, 
                                                    t.nillable)
    t.attribute_string="".join(t.attribute_string)
    #SMT
    if "dependenciesScript" in t:
        print "DEPENDENCY-SCRIPT", t["dependenciesScript"]
    ret=[smtgen.get_smt_comment(t.name),
         smtgen.get_smt_datatypes(" ".join(t.attr_type_set), #"",
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
                                    " ".join(t.attr_type_set)), #""),
         smtgen.get_smt_declare_fun(t.name+"_sortkey",
                                    "",
                                    "Int",
                                    ""),
         "\n",
         "\n"]

    
    for a in sorted(SMTLIBAssertionHandler.constantAssertions[t.name]):
        ca=SMTLIBAssertionHandler.constantAssertions[t.name][a]

        ret.append(smtgen.get_smt_range_assertion(a, ca["type"], ca["ranges"]))
    ret.append("\n")
    t.smt="".join(ret)

def initGroundTypeSMT(t, smtgen, p):
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
    elif "string"==t.name:
        t.annotatedValue="BLAH"
        t.transform=Util.get_random_string
    else:
        t.transform=transformDirect

    if t.name in p.dataTypes:
        smt_type=p.dataTypes[t.name].smtType
    else:
        raise Exception("FATAL: could not get smt_type for {0}".format(t.name))
    t.smt=smtgen.get_smt_sort(t.name, smt_type)
        

def initDerivedTypeSMT(t, smtgen, p):
    def transformDerivedType(x):
        temp=t.content[0].transform(x)
        t.annotatedValue=t.content[0].annotatedValue
        return temp

    t.transform=transformDerivedType
    t.smt=smtgen.get_smt_sort(t.name, t.content[0].name)

def initEnumTypeSMT(t, smtgen, p):
    def transformEnum(x):
        t.annotatedValue={t.name:x}
        return x[x.find("_")+1:]


    def getSMTBoundaries(llst):
        if t.basetype=="ENUM":
            return [[t.name+"_"+x[0]] for x in llst]

    t.getSMTBoundaries=getSMTBoundaries
    t.transform=transformEnum
    t.smt=smtgen.get_smt_datatypes("", t.name+" "+(" ".join(t.members.keys())))

def initStructTypeSMT(t, smtgen, p):
        #print "SETTING UP STRUCT TYPE {0}".format(t.name)

    def transformStructExclusive(x):
        temp=t.content[x[0]].transform(x)
        t.annotatedValue=t.content[x[0]].annotatedValue
        return temp

    def transformStruct(x):
        delim=None
        if t.name in p.delimiter:
            delim=p.delimiter[t.name]

        tmp=[]
        annVal=[]
        i=1
        #IN CASE OF ATTRIBUTE TYPE WE HAVE ALSO NULL     
        if len(x) == len(t.sortkey)+1:
            i=1
            for c in t.sortkey:
                tmp.append((t.content[c], x[i]))
                annVal.append((c, x[i]))
                i+=1
        else:
            #ATTRIBUTE TYPE IS NULL
            print "NO SOLUTION YET, FILL ANNOTATION_VALUE IN ANOTHER WAY"
        t.annotatedValue={t.name:dict(annVal)}
        if delim:
            ret=delim.join(str(s[0].transform(s[1])) for s in tmp)
        else:
            #ret={el[0].name: el[0].transform(el[1]) for el in tmp}
            ret= "   ".join(str(s[0].transform(s[1])) for s in tmp)
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
        
    if t.isHead:
        if t.isExclusive:
            definition=[smtgen.get_smt_n_accessor(len(t.accessors)+1, 
                                                  onlyOuterPar=True
                                                  ).format(t.pseudo_name, 
                                                           *[" ".join(x) for x in t.accessors])[1:-1]]
            datatypes=""
            return_value=t.pseudo_name
        else:
            definition=[t.pseudo_name, "(", t.mk_name]+[smtgen.get_smt_n_accessor(2).format(*x) for x in t.accessors]+[")"]
            datatypes=" ".join(set([x[1] for x in t.accessors]))
            return_value="({0} {1})".format(t.pseudo_name, datatypes)
        t.smt="\n".join([smtgen.get_smt_datatypes(datatypes, " ".join(definition)), 
                         smtgen.get_smt_sort(t.name, return_value)])    
    else:
        t.smt=""


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
