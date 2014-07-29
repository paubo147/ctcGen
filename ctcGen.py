#!/usr/bin/python

import argparse
import time
import os
import profile

from ComponentSearcher import searchComponent

from Parser import parseXML
import SMTLIBBuilder
#import ctcGatherer
import SMTController

from SMTLIBCodeGenerator import *

import math

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
    parse_obj=parseXML([open(s, "r") for s in args.files], args.annotation, args.debug, args.cls)
    #for dt in sorted(parse_obj.dataTypes.values(), key=lambda x: x.level):
    #    print dt.level, dt.type, dt.basetype, dt.name, dt.content if hasattr(dt, "content") else "NONE"

    smtlib_gen=SMTLIBCodeGenerator(parse_obj.solver_tokens)

    SMTLIBBuilder.init(args.files, parse_obj)
    smt_facts=SMTLIBBuilder.buildSMTLIBFacts(args.files, parse_obj, smtlib_gen)
    
    
    if args.output:
        with open(args.output, "wb") as f:
            f.write(smt_facts)
    #setattr(ctcGatherer, "overallTestCases", parse_obj.getNumberOfTestCases())
    #print smt_facts
    

    generic_testcases=SMTController.run(parse_obj, smt_facts, smtlib_gen, parse_obj.solver_cmd)
    #process the SMTLIBFacts with the extracted SMT Solver command
    #generic_testcases=processSMTLIBFacts(smt_facts, parse_obj.solver_cmd, smtlib_gen)
    
    end =time.time()
    if args.generic:
        with open(args.generic, "w+") as f:
            f.write(generic_testcases[1](end-start, generic_testcases[0]))
    #w    print "TESTCASES WRITTEN TO "+args.generic






if __name__=="__main__":
    start=time.time()

    aparser=argparse.ArgumentParser()
    aparser.add_argument("--profiling", action="store_true", help="prints profiling information")
    subparsers=aparser.add_subparsers(help="sub-command help")
    
    parser_create=subparsers.add_parser("create", help="create testcases")
    parser_create.add_argument("files", help="list of xml-files containing mim-definitions", nargs="+")
    parser_create.add_argument("-d", "--debug", action="store_true", help="ignores missing classes")
    parser_create.add_argument("-g", "--generic", dest="generic", type=str, help="write generic test-cases to file")
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
    
