import re
from SMTLIB_code_snippets import *
from Util import *

TEST_STRATEGY_ENUM=enum(EXPLORATORY=1, BOUNDARY=2)


class TestStrategy:

    

    def __init__(self, ranges):
        self.latestAssertions=[]
        self.testStrategy=TEST_STRATEGY_ENUM.EXPLORATORY
        self.globalRanges=ranges
        self.pendingTestCase=dict()
        print ranges
        #TODO split into real ranges according to boundary

    def addTestCase(self, tc):
        self.pendingTestCase=tc

    def getNegated(self, s):
        add=[]
        remove=[]
        m=re.match(RE_DEF_FUN, s)
        if m is None:
            raise Exception("TestStrategy: instance: "+s+" does not match regular expression: "+RE_DEF_FUN)
        md=m.groupdict()
        if self.testStrategy==TEST_STRATEGY_ENUM.EXPLORATORY:
            #fill remove list here!
            add.append("(assert (not (= {0} {1})))".format(md["func_name"], "("+md["mk_func"]+")"))
            self.latestAssertions.append(add)
        elif self.testStrategy==TEST_STRATEGY_ENUM.BOUNDARY:
           #TODO 1. iterate over pendingTestCase. For each of the classes, 
            if not self.pendingTestCase:
                raise Exception("TestStrategy: pendingTestCase is empty")
            #for c in self.pendingTestCase:
                
            #for each of the attr:value pairs get the corresponding range, negate it and append it to the add
            #remove the same previously created assertion (TODO still to store the old add value) 
            # clear pendingTestCase
        return (add,remove)
