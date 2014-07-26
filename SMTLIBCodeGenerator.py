class SMTLIBCodeGenerator:
    def __init__(self, token_list):
        self.token_list=token_list

    

    def get_smt_comment(self, s1):
        return "".join([self.token_list["COMMENT_CHAR"],s1,"\n"])

    def get_smt_commented_section(self, s2):
        return "".join([self.get_smt_comment(len(s2)*"-"),self.get_smt_comment(s2),self.get_smt_comment(len(s2)*"-"),"\n"])
    def get_smt_assertion(self, arg1):
        return self.token_list["ASSERTION"].format(arg1)

    def get_smt_range_single(self, name, typ, minV, maxV):
        le=self.token_list["LE_"+typ.upper()]
        ge=self.token_list["GE_"+typ.upper()]
       
        low_str=self.token_list["BINARY_EXPRESSION"].format(ge, name, minV)
        high_str=self.token_list["BINARY_EXPRESSION"].format(le, name, maxV)
        return self.token_list["BINARY_EXPRESSION"].format(self.token_list["AND"], low_str, high_str)

    def get_smt_range(self, name, typ, ranges):
        le=self.token_list["LE_"+typ.upper()]
        ge=self.token_list["GE_"+typ.upper()]
        big_or=["(or "] if len(ranges) > 1 else []
        for l in ranges:
            low_str=self.token_list["BINARY_EXPRESSION"].format(ge, name, min(l))
            high_str=self.token_list["BINARY_EXPRESSION"].format(le, name, max(l))
            big_or.append(self.token_list["BINARY_EXPRESSION"].format(self.token_list["AND"], low_str, high_str))
        big_or.append(")" if len(big_or) > 1 else "")
        return "".join(big_or)


    def get_smt_n_accessor(self, n, onlyOuterPar=False):
        l=["{"+str(i)+"}" for i in range(n)]
        if onlyOuterPar:
            l.insert(0,"(")
            l.append(")")
        else:
            for i in range(n-1):
                l.insert(i*2, "(")
            l.append(")"*(n-1))
        return " ".join(l)

        
    def get_smt_range_assertion(self, name, typ, ranges):
        return "".join([self.get_smt_assertion(self.get_smt_range(name, typ, ranges)),"\n"])

    def get_smt_assertion(self, arg1):
        return self.token_list["ASSERTION"].format(arg1)

    def get_smt_sort(self, arg1, arg2):
        return "".join([self.token_list["DEFINE_SORT"].format(arg1, arg2), "\n"])

    def get_smt_datatypes(self, arg1, arg2):
        return "".join([self.token_list["DECLARE_DATATYPES"].format(arg1, arg2), "\n"])

    def get_smt_declare_fun(self, arg1, arg2, arg3, arg4):
        return "".join([self.token_list["DECLARE_FUN"].format(arg1, arg2, arg3, arg4), "\n"])

    def get_smt_negation(self, arg1, arg2):
        return self.token_list["UNARY_EXPRESSION"].format(self.token_list["NOT"],
            self.token_list["BINARY_EXPRESSION"].format(self.token_list["EQ"], arg1, arg2))

    def get_smt_not(self, arg1):
        return "("+self.token_list["NOT"]+arg1+")"

    def get_smt_and(self, lst):
        temp=" ".join(["{"+str(i)+"}" for i in range(len(lst))])
        return "("+self.token_list["AND"]+temp.format(*lst)+")"

    def get_smt_or(self, lst):
        temp=" ".join(["{"+str(i)+"}" for i in range(len(lst))])
        return "("+self.token_list["OR"]+temp.format(*lst)+")"
