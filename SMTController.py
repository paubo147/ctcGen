from subprocess import Popen, PIPE

import SMTLIBBuilder
import SMTLIBParser
import ctcGatherer

SMT_INPUT_FILE="_temp_smt_facts.smt2"

runNumbers=0

def run(parse_obj, facts, smtgen, solver_cmd):
    global runNumbers

    while runNumbers==0 or ctcGatherer.runnable():
        with open(SMT_INPUT_FILE, "w+") as smt_input_file:
            smt_input_file.seek(0)
            smt_input_file.truncate()
            print runNumbers
            #print facts
            smt_input_file.write(facts) #CHANGE IF FACTS GETS AN OBJECT
            smt_input_file.write("(check-sat)\n(get-model)\n")
        runNumbers+=1
        p=Popen(solver_cmd+[SMT_INPUT_FILE], stdout=PIPE)
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
            #print to_parse
            parser_result=SMTLIBParser.parse(to_parse)
            ctcGatherer.process(parse_obj, parser_result, runNumbers)
        facts=SMTLIBBuilder.update(smtgen)

    getXML=ctcGatherer.getXML
    return (ctcGatherer.testCases, ctcGatherer.getXML)
        
