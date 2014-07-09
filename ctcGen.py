import argparse
import time
import os
import profile

from ComponentSearcher import searchComponent

from Parser import parseXML
from SMTLIBBuilder import buildSMTLIBFacts
from ctcGatherer import processSMTLIBFacts, getXML

from SMTLIBCodeGenerator import *

from Util import *


"""
Search command: used to search for mim and/or classname and directory
"""
def search(args):
    assert args.cls and args.mim

    
    xml_files=[]
    for (dirpath, dirnames, filenames) in os.walk(args.directory):
        xml_files.extend([dirpath+x for x in filenames if x[-4:] == ".xml" and x[0] != "."])

    return searchComponent(xml_files, args.cls, args.mim)

"""
Create command: used to create test-cases
"""
def create(args):
    start=time.time()
    parse_obj=parseXML([open(s, "r") for s in args.files], args.annotation, args.prnt, args.debug, args.cls)
    tokens={
        "COMMENT_CHAR": ";",
        "LE_BITVECTOR": "bvule",
        "GE_BITVECTOR": "bvuge",
        "LE_INT": "<=",
        "GE_INT": ">=",
        "EQ": "=",
        "NOT": "not",
        "BINARY_EXPRESSION": "({0} {1} {2})",
        "UNARY_EXPRESSION": "({0} {1})",
        "ASSERTION": "(assert {0})",
        "AND": "and",
        "OR":"or",
        "DEFINE_SORT": "(define-sort {0} () {1})",
        "DECLARE_DATATYPES": "(declare-datatypes ({0}) (({1})))",
        "DECLARE_FUN":"(declare-fun {0} ({1}) ({2} {3}))",
        }
    smtlib_gen=SMTLIBCodeGenerator(tokens)

    
    smt_facts=buildSMTLIBFacts(args.files, parse_obj, smtlib_gen)
    
    if args.output:
        with open(args.output, "wb") as f:
            f.write(smt_facts.toSMTLIB())

    #process the SMTLIBFacts with the extracted SMT Solver command
    generic_testcases=processSMTLIBFacts(smt_facts, parse_obj.solver_cmd, smtlib_gen)
    
    end =time.time()
    if args.generic:
        with open(args.generic, "w+") as f:
            f.write(getXML(end-start, generic_testcases))
        print "TESTCASES WRITTEN TO "+args.generic






if __name__=="__main__":
    start=time.time()

    aparser=argparse.ArgumentParser()
    aparser.add_argument("--profiling", action="store_true", help="prints profiling information")
    subparsers=aparser.add_subparsers(help="sub-command help")
    
    parser_create=subparsers.add_parser("create", help="create testcases")
    parser_create.add_argument("files", help="list of xml-files containing mim-definitions", nargs="+")
    parser_create.add_argument("-d", "--debug", action="store_true", help="debug output")
    parser_create.add_argument("-p", "--print", dest="prnt", action="store_true", help="print_output")
    parser_create.add_argument("-g", "--generic", dest="generic", type=str, help="print generic test-cases to file")
    parser_create.add_argument("-c", "--class", dest="cls", type=str, help="only class to be parsed")
    parser_create.add_argument("-a", "--annotation", type=str, help="annotation-file")
    parser_create.add_argument("-o", "--output-file", dest="output", type=str, help="output-file for smt code")
    parser_create.set_defaults(func=create)
    
    parser_search=subparsers.add_parser("search", help="finds a class-file")
    parser_search.add_argument("-m", "--mim", dest="mim", help="mim name")
    parser_search.add_argument("-c", "--class", dest="cls", help="class name")
    parser_search.add_argument("directory", help="folder containing model files")
    parser_search.set_defaults(func=search)
                           

    args=aparser.parse_args()

    #CALLS THE FUNCTION ACCORDING TO THE func-default
    if args.profiling:
        profile.run("args.func(args)")
    else:
        args.func(args)
            
    end =time.time()
    
    print "Timediff: ", end-start, "sec"
    
