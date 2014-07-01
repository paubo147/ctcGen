#from SMTLIB_transformer import *
#from SMT_test_master import *
import argparse
import time

import Parser

import SMTLIBBuilder
import ctcGatherer

from Util import *

def extractSMTSolverCmd(parse_obj):
    smt_cmd=[]
    if not parse_obj.annotations:
        print "USING DEFAULT SOLVER PARAMS"
        smt_cmd=["/home/ebopaul/Documents/smt/z3-4.3.2.8wef4ec7009ab-x64-debian-7.4/bin/z3", "-smt2"]
    else:
        smt_cmd=[parse_obj.annotations["solver_path"]]+[parse_obj.annotations[x] for x in parse_obj.annotations if "solver_arg" in x]

    return smt_cmd

if __name__=="__main__":
    start=time.time()

    aparser=argparse.ArgumentParser()
    aparser.add_argument("files", help="list of xml-files containing mim-definitions", nargs="+")
    aparser.add_argument("-d", "--debug", action="store_true", help="debug output")
    aparser.add_argument("-p", "--print", dest="prnt", action="store_true", help="print_output")
    aparser.add_argument("-g", "--generic", dest="generic", type=str, help="print generic test-cases to file")
    aparser.add_argument("-c", "--class", dest="cls", type=str, help="only class to be parsed")
    aparser.add_argument("-a", "--annotation", type=str, help="annotation-file")
    aparser.add_argument("-o", "--output-file", dest="output", type=str, help="output-file for smt code")
    
    args=aparser.parse_args()

    #PARSE THE XML FILE; STORE EVERYTHING IN AN OBJECT
    parse_obj=Parser.parse([open(s, "r") for s in args.files], args.annotation, args.prnt, args.debug, args.cls)

    smt_facts=SMTLIBBuilder.build(args.files, parse_obj)
    print smt_facts.toSMTLIB()
    
    if args.output:
        with open(args.output, "wb") as f:
            f.write(str(smt_facts))

    #GATHER SMT SOLVER COMMAND FROM THE ANNOTATIONS
    smt_cmd=extractSMTSolverCmd(parse_obj)
    
        
    generic_testcases=ctcGatherer.process(smt_facts, smt_cmd)
    


    #testGen=SMT_TestGuide(smt_creator.facts, parse_obj.annotations, smt_creator.facts.classDatatypes)
    #generic_tc_xml=testGen.run(False)
    if args.generic:
        with open(args.generic, "w+") as f:
            f.write(ctcGatherer.getXML(generic_testcases))


            
    end =time.time()
    
    print "Timediff: ", end-start, "sec"
    
