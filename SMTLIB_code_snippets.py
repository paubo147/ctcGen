from Util import *

SMTLIB_FUN="(declare-fun {0} ({1}) ({2}))"
ENUM_TYPE_TEMPLATE_STRING="(declare-datatypes () (({0} {1})))"
BASE_TYPE_TEMPLATE_STRING="(define-sort {0} () {1})"
CLASS_TYPE_TEMPLATE_STRING="(declare-datatypes ({0}) (({1} )))"
CLASS_INSTANCE_TEMPLATE_STRING="(declare-fun {0} () ({1} {2}))"
ASSERTION_TEMPLATE_STRING="(assert {0})"
#ASSERTION_FUN_TEMPLATE_STRING="(define-fun {0} () Bool (let ({1}) {2} ))"
ASSERTION_BV_FUN="(define-fun {0} () (_ BitVec {1}))"
BINARY_EXPRESSION_TEMPLATE_STRING="({0} {1} {2})"
EQ=BINARY_EXPRESSION_TEMPLATE_STRING.format("=", "{0}", "{1}")
NEG_EQ="(not {0})".format(EQ)
ASSERTION_NEG_EQ=ASSERTION_TEMPLATE_STRING.format(NEG_EQ)


RE_MODEL=r"\(model *(?P<model>.*) *\)"
RE_DEF_FUN=r"\(define\-fun *(?P<func_name>.+) *\(\) *\((?P<func_signature>.+)\) *\((?P<mk_func>.+)\)\)"

RE_ACCESSOR_LIST=r"(\(.*?\)\s?|.*?\s)"


#TODO hardcoded! maybe replace this part with an own configuration file
class SMTCoder:
    @staticmethod
    def get_smt_comment(s1):
        return ";"+s1+"\n"

    @staticmethod
    def get_smt_commented_section(s2):
        return SMTCoder.get_smt_comment(len(s2)*"-")+SMTCoder.get_smt_comment(s2)+SMTCoder.get_smt_comment(len(s2)*"-")+"\n"

    @staticmethod
    def get_int_smt_ranges(name, ranges):
        low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format(">=", name, min(ranges))
        high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("<=",name, max(ranges))
        return BINARY_EXPRESSION_TEMPLATE_STRING.format("and", low_str, high_str)
    
    @staticmethod
    def get_ipv4_smt_ranges(name, ranges):
        big_or="(or "
        for l in ranges:
            low=min(l)
            high=max(l)
            low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvuge", name, low)
            high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvule", name, high)
            big_or+="(and {0} {1}) ".format(low_str, high_str)
        big_or+=")"
        return big_or

    @staticmethod
    def get_smt_key_assertion(key_fun, instance_fun, key):
        return ASSERTION_TEMPLATE_STRING.format(BINARY_EXPRESSION_TEMPLATE_STRING.format("=", "("+key_fun+" "+instance_fun+")", "("+key+" "+instance_fun+")"))+"\n"
