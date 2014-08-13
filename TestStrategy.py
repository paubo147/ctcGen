import re
import metacomm.combinatorics.all_pairs2
all_pairs=metacomm.combinatorics.all_pairs2.all_pairs2

from SMTLIB_code_snippets import *
import Util

class StrategyObject(object):
    def __init__(self):
        self._instances={}

    def __call__(self, att):
        return iter(self.__dict__[att])

    def __setattr__(self, a, n):
        if a!="_instances":
            if hasattr(self, a):
                getattr(self,a).append(n)
            else:
                self.__dict__[a]=[n]
        else:
            self.__dict__[a]=n

    def __setitem__(self, key, value):
        self._instances[key]=value

        
    
#modify and delete to include
lifecycle=["create"]
oracle_joinpoint=["", "after"]

def compute(parse_object):
    so=StrategyObject()
    #1st: create structs and sequences
    for dt in filter(lambda x: x.type=="STRUCT" and x.isHead, parse_object.dataTypes.values()):
        dt.smt_mk_name="mk_{0}".format(dt.name)
        dt.smt_name_dt="{0}_dt".format(dt.name)
        dt.smt_accessors=[]
        
        if not dt.isExclusive:
            dt.smt_accessors=["({} {})".format(x, "Int") for x in sorted(dt.content)]
            dt.smt_datatype_set="Int"
            dt.smt_body=[dt.smt_name_dt, " ( ", dt.smt_mk_name, " "]+dt.smt_accessors
            dt.smt_old_sort="({} {})".format(dt.smt_name_dt, dt.smt_datatype_set)
        else:
            dt.smt_datatype_set=""
            for x in dt.content:
                dt.smt_accessors.append("".join([" ( ", x]+["({0} {1})".format(y, "Int") for y in dt.content[x].content]+[")"]))
            dt.smt_body=[dt.smt_name_dt]+dt.smt_accessors
            dt.smt_old_sort=dt.smt_name_dt
        so.structs=dt
            
    for cl in parse_object.classes.values():
        cl.smt_functions=[]
        cl.smt_oracles=[]
        cl.smt_oracle_assertion=[]
        cl.smt_temp_assertion_part=[]
        cl.smt_mk_name="mk_{}".format(cl.name)
        cl.smt_body=[cl.name, " ( ", cl.smt_mk_name, " "]


        temp={}
        temp["oracle{}_create".format(cl.name.title())]=[]
        temp["oracle{}_afterCreate".format(cl.name.title())]=[]
        for a in cl.attributes:
            a.smt_oracles=[]
            #TODO ugly work-around. Change structure of dataTypes
            dt=a.dataType
            if dt.type=="STRUCT":
                a.smt_datatype="(Attribute {})".format(dt.name)
            elif dt.type=="DERIVED" and dt.content[0].type=="STRUCT":
                dt=dt.content[0]
                a.smt_datatype="(Attribute {})".format(dt.name)
            else:
                a.smt_datatype="(Attribute Int)"

            #attribute-oracle function:
            a.smt_oracles.append({"type":"attribute", 
                                  "name":"oracle{}_create".format(a.name.title()),
                                  "param":"(x {})".format(a.smt_datatype),
                                  "returntype": "Bool",
                                  "body":getValidityConditionCreate(a)
                                  })
            temp["oracle{}_create".format(cl.name.title())].append("(oracle{0}_create ({1} {2}_create))".format(a.name.title(), a.name, cl.name))
            a.smt_oracles.append({"type":"attribute",
                                  "name":"oracle{}_afterCreate".format(a.name.title()),
                                  "param":"(x {})".format(a.smt_datatype),
                                  "returntype": "Bool",
                                  "body":getValidityConditionAfterCreate(a),
                                  "verify": "(oracle{0}_afterCreate ({1} {2}_afterCreate))".format(a.name.title(), a.name, cl.name)
                                  })
            temp["oracle{}_afterCreate".format(cl.name.title())].append("(oracle{0}_afterCreate ({1} {2}_afterCreate))".format(a.name.title(), a.name, cl.name))

            so.oracles=a.smt_oracles
            cl.smt_body.append("({} {})".format(a.name, a.smt_datatype))

        
        cl.smt_oracles.append({"type":"class",
                               "name":"oracle{}_create".format(cl.name.title()),
                               "param": cl.name,
                               "returntype": "Bool",
                               "body": "",
                               "assertion":"(oracle{0}_create {0}_create)".format(cl.name.title()),
                               "attr_parts":temp["oracle{}_create".format(cl.name.title())]
                               })
        cl.smt_oracles.append({"type":"class",
                               "name":"oracle{}_afterCreate".format(cl.name.title()),
                               "param": cl.name,
                               "returntype": "Bool",
                               "body": "",
                               "assertion":"(oracle{0}_afterCreate {0}_afterCreate)".format(cl.name.title()),
                               "attr_parts":temp["oracle{}_afterCreate".format(cl.name.title())]
                               })
        
        so.oracles=cl.smt_oracles
        so.classes=cl
        
        #NOW TO THE ALLPAIRS. First, print all the legal and illegal boundaries 
    print "START WITH NEW EXPERIMENT"
    for c in parse_object.classes.values():
        if len(c.attributes)==1:
            pw=c.attributes[0].dataType.partitions
        else:
            agg=[]
            for a in c.attributes: 
                agg.extend(a.dataType.partitions)
            pw =all_pairs(agg)
            
        so[c.name]=pw
        #print c.name, len(list(pw))
        
    print "FINISHED WITH NEW EXPERIMENT"
    return so


def getValidityConditionCreate(a):
    return "\ntrue"

def getValidityConditionAfterCreate(a):
    return "\ntrue"


