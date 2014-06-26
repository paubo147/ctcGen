import subprocess
from SMTInterpreter import *

SMT_INPUT_FILE="_temp_smt_facts.smt2"
SMT_OUTPUT_FILE="_temp_smt_result.smt2"

class SMT_TestGuide:
    

    def __init__(self, facts, annotations, classes, strategy):
        self.facts=facts
        
        print annotations
        if not annotations:
            print "USING DEFAULT SOLVER PARAMS"
            self.smt_solver_path="/home/ebopaul/Documents/smt/z3-4.3.2.8ef4ec7009ab-x64-debian-7.4/bin/z3"
            self.smt_solver_flags=["-smt2"]
        else:
            self.smt_solver_path=annotations["solver_path"]
            self.smt_solver_flags=[annotations[x] for x in annotations if "solver_arg" in x]
        self.smtInterpreter=SMTInterpreter(classes, strategy)


    def writeFooter(self, f):
        f.write("(check-sat)\n(get-model)\n")


    def process_result(self, out, err):
        ret=None
        if not err:
            l=out.split("\n",1)
            if l[0] == "sat":
                (add,remove)=self.smtInterpreter.storeAndReturn(l[1].replace('\n', ''), self.facts)
                for r in remove:
                    self.facts.replace(r, "")
                for a in add:
                    self.facts+=a+"\n"
            elif l[0] == "unsat":
                raise Exception("Model is not satisfiable")
        #else:
        #    ret=err


    """
    Function which 
    """
    def run(self, stopCondition):
        arg=[self.smt_solver_path]+self.smt_solver_flags+[SMT_INPUT_FILE]

        with  open(SMT_INPUT_FILE, "w+") as smt_input_file:
            smt_input_file.seek(0)
            smt_input_file.truncate()
            smt_input_file.write(self.facts)
            self.writeFooter(smt_input_file)

        for i in range(20):#TODO stop condition should come from the stat-module
            print "SMT RUN NUMBER ",i
 
            p=subprocess.Popen(arg, stdout=subprocess.PIPE)
            out,err = p.communicate()
            
            self.process_result(out, err)
            
            #if result:
            #    self.facts+=result+"\n"
            #else:
            #    raise Exception("Model is not satisfiable")
            
            with open(SMT_INPUT_FILE, "w+") as smt_input_file:
                #2 clear input file
                smt_input_file.seek(0)
                smt_input_file.truncate()

            #4 write facts to the input file
                smt_input_file.write(self.facts)
                self.writeFooter(smt_input_file)

        
        #return the XML object from the smtInterpreter
        return self.smtInterpreter.getXML()
        
