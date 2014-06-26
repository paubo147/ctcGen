from SMTLIB_code_snippets import *
import Util

class AssertionHandler:
	def __init__(self, annotations):
                self.rangeAssertions=dict()
                self.specialAssertions=dict()
		self.annotations=annotations #TODO remove from here
		
	"""
        adds a range assertion for :
        input:
              instantiation_function_name 
              attribute
              ranges list of lists
	"""
	def addRangeAssertion(self, name, attr, low, high):
            self.rangeAssertions["("+attr+" "+name+")"]=[low,high]
         
        def addSpecialAssertion(self, name, attr, lst):
            s="({0} ({1} {2}))"
            for field, ranges in lst.iteritems():
                ss=s.format(field, attr, name)
                self.specialAssertions[s.format(field, attr, name)]=ranges                       

        def get_int_smt_ranges(self, name, ranges):
            low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format(">=", name, min(ranges))
            high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("<=",name, max(ranges))
            return BINARY_EXPRESSION_TEMPLATE_STRING.format("and", low_str, high_str)
            
        def get_ipv4_smt_ranges(self, name, ranges):
            big_or="(or "
            for l in ranges:
                low=Util.getSMThex(min(l))#"#"+hex(int(min(l)))[1:]
                high=Util.getSMThex(min(l))#"#"+hex(int(max(l)))[1:]
                low_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvuge", name, low)
                high_str=BINARY_EXPRESSION_TEMPLATE_STRING.format("bvule", name, high)
                big_or+="(and {0} {1}) ".format(low_str, high_str)
            big_or+=")"
            return big_or

	def __str__(self):
            s=""
            for name, ranges in self.rangeAssertions.iteritems():
                s+="(assert"+ self.get_int_smt_ranges(name, ranges)+")\n"

            
            for name, ranges in self.specialAssertions.iteritems():
                s+="(assert" + self.get_ipv4_smt_ranges(name, ranges)+")\n"
                
            return s
