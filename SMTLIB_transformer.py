import Parser
from string import Template
import re
import sys
import argparse
from SMTLIB_code_snippets import *
from SMTLIB_assertions import *
from collections import defaultdict
from Util import *

smt_type_translation={
    "int16": "Int",
    "int32": "Int",
    "int64": "Int",
    "uint8": "Int",
    "uint16": "Int",
    "uint32": "Int",
    "uint64": "Int",
    "boolean": "Bool",
    "string": "String",
    "moRef": "Int",
}


def get_smt_type(tp):
        return smt_type_translation.get(tp, tp)


"""
ClassType container. Contains all neccessary things
for the SMTLIB2.0 code generation
"""
class ClassType:
	def __init__(self, name):
		self.name=name
		self.constructor="mk_"+self.name
		self.function=name[0].lower()+name[1:]+"_instance"
		self.attributes=dict()
		self.attribute_name_order=list()
		self.attribute_type_order=list()
		self.attribute_string=""

	def addAttribute(self, name, typ):
		self.attributes[name]=typ
		self.attribute_name_order.append(name)
		self.attribute_type_order.append(typ)
		self.attribute_string+="("+name+" "+typ+")"
		self.type_set=set(self.attributes.values())

	def __str__(self):
		first=" ".join(self.type_set)
		second=self.name+" ("+self.constructor +" "+self.attribute_string+") "
		s=CLASS_TYPE_TEMPLATE_STRING.format(first, second)+"\n"
		s+=CLASS_INSTANCE_TEMPLATE_STRING.format(self.function, self.name, " ".join(self.type_set))+"\n"
		return s

"""
This class is responsible to keep gather and keep track about all the SMTLIB2
declarations. The information are taken from the parse tree.
The class itself does not need that much information about the parse tree.
Also a basic assertion_handler is introduced to create assertions according 
to the testing-strategy.
"""
class SMTLIBMainBuilder:
    """
    initializer just initializes the string fields for datatypes and classes.
    TODO include the Testing-strategy as an argument of this initializer in the future
    """
    def __init__(self, filenames, annotations):
	    self.filenames=filenames
	    self.stringsPresent=False

	    self.derivedSorts=dict()
	    self.enumDatatypes=dict()
	    self.classDatatypes=list()
	    self.structDatatypes=dict()

	    self.annotations=annotations

	    self.specialTypes=set(self.annotations[x][0] for x in self.annotations if "solver" not in x)
	    
	    
	    self.assertion_handler=AssertionHandler(self.annotations)

    """
    Creates the SMTLIB2 declarations for the basic datatypes inside the list from the parser.
    Calls the assertion_handler to create the baseTypeAssertions (only ranges)
    input:
         types: list of name of base-types
    """
    def createBaseSorts(self, types):
	    for t in types:
		    self.derivedSorts[t]=get_smt_type(t)
		    #if get_range(t) is not None and get_smt_type(t) != "string":
			    #self.assertion_handler.addBaseTypeAssertion(t,get_range(t)) 
	    #self.assertion_handler.createBaseTypeAssertions(types)
            

    """
    Creates the SMTLIB2 declarations for the derived types.
    If the base-type contains a range, we call the assertion_handler again.
    input:
         types: dict of name -> baseType[range]
    """
    def createDerivedSorts(self, types):
	    self.mac=False
	    self.ipv4=False
	    self.stringsPresent=("string" in types)
	    for k in types:
		    bt=types[k]
		    if "IPV4" in bt:
			    self.ipv4=True
			    bt="(IPV4 "+ ("ipv4_part "*5)+")"
		    if "MAC" in bt:
			    self.mac=True
			    bt="(MAC "+ ("mac_part "*6)+")"
		    if "string" in bt:
			    self.stringsPresent=True
		    
		    if "[" in bt:
			    rng=bt[bt.find("["):]
			    st=bt[:bt.find("[")]
			    #self.assertion_handler.addBaseTypeAssertion(k, tuple(int(v) for v in re.findall("[0-9]+", rng)))
			    self.derivedSorts[k]=get_smt_type(st)
			    continue
		    self.derivedSorts[k]=get_smt_type(bt)
    """
    Creates the SMTLIB2 declarations for the enums.
    input:
         enums: name -> members
    """
    def createEnums(self, enums):
	    for key in enums:
		    print key
		    name=key
		    temp=[name+"_"+s for s in enums[key] ]
		    self.enumDatatypes[name]=temp
		    #self.datatype_declarations+=ENUM_TYPE_TEMPLATE_STRING.format(name, " ".join(temp))+"\n"
    
    def createStructs(self, structs):
	    for name in structs:
		    self.structDatatypes[name]=structs[name]
	    
	    
    """
    Creates the SMTLIB2 declarations for classes. Takes the whole parse_object.
    input 
    """
    def createClasses(self, tree, parse_obj):
	    print parse_obj.derivedTypes
	    clsDt=ClassType(tree.name)
	    for a in tree.attributes:
		    t=a.type
		    if t in self.annotations:
			    clsDt.addAttribute(a.name, self.annotations[t][0])
			    self.assertion_handler.addSpecialAssertion(clsDt.function, a.name, self.annotations[t][1])
		    elif t in parse_obj.derivedTypes:
			    t=Util.get_plain_name(parse_obj.derivedTypes[a.type])
			    r=Util.get_range(parse_obj.derivedTypes[a.type])
			    if r is not None and get_smt_type(t) is not "String":
				    self.assertion_handler.addRangeAssertion(clsDt.function, a.name, r[0], r[1])
			    clsDt.addAttribute(a.name, get_smt_type(t))
		    elif t in parse_obj.enumTypes:
			    self.enumDatatypes[t]=parse_obj.enumTypes[t]
			    clsDt.addAttribute(a.name, t)
		    elif get_smt_type(t) != t:
			    #print "BASETYPE:", get_smt_type(t)
			    clsDt.addAttribute(a.name, get_smt_type(t))
		    else:
			    print "UNDETERMINED DATATYPE: ",t, a.name
	    self.classDatatypes.append(clsDt)
	
	    
	    for c in tree.children:
		    self.createClasses(c, parse_obj)

    def getRanges(self):
	    return dict(self.assertion_handler.rangeAssertions, **self.assertion_handler.specialAssertions)

    def __str__(self):
            s=";files: "+",".join(self.filenames)+"\n"


            s+=";----------\n"
            s+="; DATATYPES\n"
            s+=";----------\n\n"

	    for t in self.enumDatatypes:
		    s+=ENUM_TYPE_TEMPLATE_STRING.format(t, " ".join(self.enumDatatypes[t]))+"\n"

	    base_blocks=[]
	    datatypes=[]
	    declarations=[]
	    for name in self.specialTypes:
		    print name
		    typ=special_types[name]
		    for i, part in typ.iteritems():
			    if i == "base_block":
				    base_blocks.append(part)
			    elif i=="datatype":
				    datatypes.append(part)
			    elif i=="declaration":
				    declarations.append(part)
	    base_blocks=set(base_blocks)
	    declarations=set(declarations)
	    for bb in base_blocks:
		    s+=bb()
	    s+="\n"
	    for d in datatypes:
		    s+=d()
	    s+="\n"
	    for d in declarations:
		    s+=d()
	    
	    if self.ipv4:
		    s+="(define-sort special_part () (_ BitVec 8))\n"
		    s+="(define-datatypes (q1 q2 q3 q4 prefix) ((IPV4(mk_IPV4(q1 special_part) (q2 special_part) (q3 special_part) (q4 special_part) (prefix special_part)))))\n\n"

	    if self.mac:
		    s+="(define-datatypes (s1 s2 s3 s4 s5 s6) ((MAC(mk_MAC(s1 special_part) (s2 special_part) (s3 special_part) (s4 special_part) (s5 special_part) (s6 special_part)))))\n\n"

	    if self.stringsPresent:
		    s+="(define-sort String () (_ BitVec 32))\n"
	    s+="\n"
	    #for key in self.derivedSorts:
	#	    s+=BASE_TYPE_TEMPLATE_STRING.format(key, self.derivedSorts[key])+"\n"   
	 #   s+="\n"
	  
	    
	  #  if self.structDatatypes:
	#	    s+=";-------------------------\n"
	#	    s+="; STRUCTS\n"
	#	    s+=";-------------------------\n\n"
	    
	 #   for key in self.structDatatypes:
	#	    def_str=key+"( mk_"+key
	#	    for a in self.structDatatypes[key]:
	#		    def_str+="("+ a[0]+" "+get_smt_type(a[1])+") "
	#	    def_str+=")"
	#	    s+=CLASS_TYPE_TEMPLATE_STRING.format(" ".join([x[1] for x in self.structDatatypes[key]]), def_str)+"\n"
		    #TODO instance template string should be instantiated by the strategy module
	#	    s+=CLASS_INSTANCE_TEMPLATE_STRING.format(key[0].lower()+key[1:], key," ".join([get_smt_type(a[1]) for a in self.structDatatypes[key]]))+"\n\n"
	    
            s+=";-------------------------\n"
            s+="; CLASSES AND CONSTRUCTORS\n"
            s+=";-------------------------\n\n"
	    for c in self.classDatatypes:
		    s+=str(c)
            s+=";------------\n"
            s+="; ASSERTIONS\n"
            s+=";------------\n"
            s+=str(self.assertion_handler)
            return s
