from time import strftime
import TestStrategy

class SMTLIBEncoder(object):
    def __init__(self):
        self._fixed_smt_lib_str=""

    def _get_preface(self, smtlibgen, files):
        return [smtlibgen.get_smt_comment("mp_files:\t{0}".format(",".join(files))),
                smtlibgen.get_smt_comment("creation-date:\t{0}".format(strftime("%c"))),
                smtlibgen.get_smt_comment("created by:\tctcGen-tool v 1.0"),
                smtlibgen.get_smt_comment("author:\tPaul Borek"),
                "\n"]

    def encode(self, smtlibgen, files, parse_obj):
        """
        1. preface (comment section with author, date, files)
        2. create attribute-type
        3. create struct-types
        4. create classes
        5. call TestStrategy class to get a strategy object
        6. encode some things from the strategy object
        """ 
        if not self._fixed_smt_lib_str:
            helper_lst=self._get_preface(smtlibgen, files)
            helper_lst.append(smtlibgen.get_smt_datatypes("T", "Attribute null (data (value T))"))
            helper_lst.append("\n")
            strategy_object=TestStrategy.compute(parse_obj)
            
            helper_lst.append(smtlibgen.get_smt_commented_section("STRUCTS"))
            for struct in strategy_object("structs"):
                helper_lst.append(smtlibgen.get_smt_datatypes(struct.smt_datatype_set, "".join(struct.smt_body)))
                helper_lst.append(smtlibgen.get_smt_sort(struct.name, struct.smt_old_sort))

            #helper_lst.append("\n")
            #helper_lst.append(smtlibgen.get_smt_commented_section("SEQUENCES"))
            #for sequence in strategy_object("sequences"):
            #    pass

            helper_lst.append("\n")
            helper_lst.append(smtlibgen.get_smt_commented_section("CLASSES"))
            for cls in strategy_object("classes"):
                helper_lst.append(smtlibgen.get_smt_datatypes("", "".join(cls.smt_body)))
                for f in cls.smt_functions:
                    helper_lst.append(smtlibgen.get_smt_declare_fun(f, "", cls.name, ""))

            helper_lst.append("\n")
            helper_lst.append(smtlibgen.get_smt_commented_section("ORACLE-FUNCTIONS"))
            for oracle_function in strategy_object("oracles"):
                for o in oracle_function:
                    if o["type"]=="attribute":
                        helper_lst.append(smtlibgen.get_smt_define_fun(o["name"], o["param"], o["returntype"], o["body"]))
                    elif o["type"]=="class":
                        helper_lst.append(smtlibgen.get_smt_declare_fun(o["name"], o["param"], o["returntype"], o["body"]))
                        helper_lst.append(smtlibgen.get_smt_assertion(smtlibgen.get_smt_eq(o["assertion"],
                                                                               smtlibgen.get_smt_and(o["attr_parts"], True), True), True))


            #TODO hierarchies and bidirectional references
            #helper_lst.append("\n")
            #helper_lst.append(smtlibgen.get_smt_commented_section("CLASS INSTANTIATIONS"))
            #for class_order in strategy_object("instantiations"):
            #    pass
            
            self._fixed_smt_lib_str="".join(helper_lst)

        #TODO what about generated assertions?
            
        #print self._fixed_smt_lib_str
        return {"smt":self._fixed_smt_lib_str,"so":strategy_object}


    
