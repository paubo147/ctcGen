from Util import *


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
    def get_string_sort():
        return BASE_TYPE_TEMPLATE_STRING.format("String", "(_ BitVec 32)")+"\n"

    @staticmethod
    def get_8bit_base_block():
        return BASE_TYPE_TEMPLATE_STRING.format("a8bit", "(_ BitVec 8)")+"\n"

    @staticmethod
    def get_ipv4_datatype():
        return CLASS_TYPE_TEMPLATE_STRING.format("a8bit", "IPV4_dt(mk_IPV4_dt(q1 a8bit) (q2 a8bit) (q3 a8bit) (q4 a8bit))")+"\n"

    @staticmethod
    def get_ipv4_declaration():
        return BASE_TYPE_TEMPLATE_STRING.format("IPV4", "(IPV4_dt a8bit)")+"\n"

    @staticmethod
    def get_ipv4_prefix_datatype():
        return CLASS_TYPE_TEMPLATE_STRING.format("a8bit", "IPV4_PREFIX_dt(mk_IPV4_PREFIX_dt(q1 a8bit) (q2 a8bit) (q3 a8bit) (q4 a8bit) (prefix a8bit))")+"\n"

    @staticmethod
    def get_ipv4_prefix_declaration():
        return BASE_TYPE_TEMPLATE_STRING.format("IPV4_PREFIX", "(IPV4_PREFIX_dt a8bit)")+"\n"

    @staticmethod
    def get_mac_datatype():
        return CLASS_TYPE_TEMPLATE_STRING.format("a8bit", "MAC_dt(mk_MAC_dt (s1 a8bit) (s2 a8bit) (s3 a8bit) (s4 a8bit) (s5 a8bit) (s6 a8bit))")+"\n"
    
    @staticmethod
    def get_mac_declaration():
        return BASE_TYPE_TEMPLATE_STRING.format("MAC", "(MAC_dt a8bit)")

    @staticmethod
    def get_int_smt_ranges(name, ranges):
        low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format(">=", name, min(ranges))
        high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("<=",name, max(ranges))
        return BINARY_EXPRESSION_TEMPLATE_STRING.format("and", low_str, high_str)
    
    @staticmethod
    def get_ipv4_smt_ranges(name, ranges):
        big_or="(or "
        for l in ranges:
            low=getSMThex(min(l))#"#"+hex(int(min(l)))[1:]
            high=getSMThex(max(l))#"#"+hex(int(max(l)))[1:]
            low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvuge", name, low)
            high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvule", name, high)
            big_or+="(and {0} {1}) ".format(low_str, high_str)
        big_or+=")"
        return big_or

special_types={
"IPV4": {
        "base_block": SMTCoder.get_8bit_base_block,
        "datatype": SMTCoder.get_ipv4_datatype,
        "declaration": SMTCoder.get_ipv4_declaration
        },
}
