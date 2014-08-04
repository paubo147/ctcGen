#!/usr/bin/python

import argparse
import time
import os
import profile

from ComponentSearcher import searchComponent

from Parser import parseXML, findConvexHull, findFileOfClass
import SMTLIBBuilder
import SMTLIBHandler
import SMTController

from SMTLIBCodeGenerator import *

import math

"""
Search command: used to search for mim and/or classname and directory
"""
def summarize(args):
    parse_obj=parseXML([open(s, "r") for s in args.files], args.annotation, args.debug, args.cls)
    rootElements=[]
    for cl in parse_obj.classes.values():
        if not cl.parents:
            rootElements.append(cl)

    seen=[]
    treeWalk(0, rootElements, seen)

def treeWalk(lvl, l, seen):
    for e in l:
        print " "*lvl, id(e), e.name
        if e in seen:
            return
        seen.append(e)
        treeWalk(lvl+1, e.children, seen)
    
def findClass(args):
    print findFileOfClass(args.folder, args.classname)


"""
Create command: used to create test-cases
"""
def create(args):
    start=time.time()
    parse_obj=parseXML([open(s, "r") for s in args.files], args.annotation, args.debug, args.cls)
    #for dt in sorted(parse_obj.dataTypes.values(), key=lambda x: x.level):
    #    print dt.level, dt.type, dt.basetype, dt.name, dt.content if hasattr(dt, "content") else "NONE"

    smtlib_gen=SMTLIBCodeGenerator(parse_obj.solver_tokens)

    #smtlib_handler=SMTLIBHandler.SMTLIBHandler1()
    SMTLIBBuilder.init(smtlib_gen, parse_obj)
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


def finder(args):
    l=findConvexHull(args.folder, args.file)
    if l[1]:
        print "NOT ALL MIMS FOUND:", ",".join(l[1])
    print "CONVEX HULL:", " ".join(sorted(l[0]))


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
    
    parser_summarize=subparsers.add_parser("summarize", help="finds a class-file")
    parser_summarize.add_argument("files", help="list of xml-files containing mim-definitions", nargs="+")
    parser_summarize.add_argument("-a", "--annotation", type=str, help="annotation-file")
    parser_summarize.add_argument("-c", "--class", dest="cls", type=str, help="only class to be parsed")
    parser_summarize.add_argument("-d", "--debug", action="store_true", help="ignores missing classes")
    parser_summarize.set_defaults(func=summarize)

    parser_finder=subparsers.add_parser("finder", help="finds the 'convex-hull' of all mp-files")
    parser_finder.add_argument("folder", help="folder to search in")
    parser_finder.add_argument("file", help="starting-file")
    parser_finder.set_defaults(func=finder)


    parser_find_class=subparsers.add_parser("findclass", help="finds the 'convex-hull' of all mp-files")
    parser_find_class.add_argument("folder", help="folder to search in")
    parser_find_class.add_argument("classname", help="classname")
    parser_find_class.set_defaults(func=findClass)
                           

    args=aparser.parse_args()

    #CALLS THE FUNCTION ACCORDING TO THE func-default
    if args.profiling:
        profile.run("args.func(args)")
    else:
        args.func(args)
            
    end =time.time()
    
    print "Timediff: ", end-start, "sec"
    
