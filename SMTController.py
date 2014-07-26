import subprocess
import ctcGatherer
import SMTLIBParser

from Util import *

SMT_INPUT_FILE="_temp_smt_facts.smt2"

runNumbers=0

def run(parse_obj, facts, solver_cmd):
    global runNumbers
    with open(SMT_INPUT_FILE, "w+") as smt_input_file:
        smt_input_file.seek(0)
        smt_input_file.truncate()
        smt_input_file.write(facts) #CHANGE IF FACTS GETS AN OBJECT
        smt_input_file.write("(check-sat)\n(get-model)\n")
    while runNumbers == 0:
        runNumbers+=1
        p=subprocess.Popen(solver_cmd+[SMT_INPUT_FILE], stdout=subprocess.PIPE)
        out,err = p.communicate()
        if not err:
            l=out.split("\n", 1)
            if l[0] == "sat":
                to_parse=l[1]
            elif l[0] == "unsat":
                raise Exception("Model is unsatisfiable! Check file '"+SMT_INPUT_FILE+"' manually")
            else:
                raise Exception("Model: "+out)
        else:
            raise Exception("SMTSOLVER: "+err)  
        if to_parse is not None:
            parser_result=SMTLIBParser.parse(to_parse)
            ctcGatherer.process(parse_obj, parser_result, runNumbers)
