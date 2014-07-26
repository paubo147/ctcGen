from string import Template
import re
import sys
import time
import types

import SMTLIBHandler

#from SMTLIB_code_snippets import *
from SMTLIB_assertions import *
from SMTLIBCodeGenerator import *
import string
from itertools import groupby
#from Util import *

import Util

smt_type_translation={}

def get_smt_type(k):
	return smt_type_translation.get(k, k)

"""
ClassType container. Contains all neccessary things
for the SMTLIB2.0 code generation
"""
class ClassType:
	def __init__(self, name):
		self.name=name
		self.constructor="mk_"+self.name
		self.instance_function=name[0].lower()+name[1:]+"_instance"
		#self.key_function=name[0].lower()+name[1:]+"_key"
		self.attributes={}
		self.attribute_name_order=[]
		self.attribute_type_order=[]
		self.attribute_string=""
		self.attribute_boundaries={}
		self.type_set=set()
		

	def addAttribute(self, name, typ, boundaries):
		self.attributes[name]=typ
		self.attribute_name_order.append(name)
		self.attribute_type_order.append(typ)
		self.attribute_string+="("+name+" "+typ+")"
		self.type_set=set(self.attributes.values())
		self.attribute_boundaries[typ]=boundaries

	def setKey(self, name, typ):
		self.key=name
		self.key_type=typ

	def getSMTLIBString(self, gen):
		first=" ".join(self.type_set)
		second="".join([self.name, " (", self.constructor, " ", self.attribute_string,") "])
		s=[gen.get_smt_comment(self.name),
		   gen.get_smt_datatypes(first, second),
		   gen.get_smt_declare_fun(self.instance_function, "", self.name, first),
		   "\n"]
		#if self.key_function and self.key_type:
		#	s+=SMTLIB_FUN.format(self.key_function, "("+(self.name+" "+(" ".join(self.type_set)))+")", self.key_type)+"\n"
		return "".join(s)

class SMTFacts:
	def __init__(self, filenames, smtlib_gen):
		self.filenames=filenames

		

		

		self.rangeAssertions={}
		self.testerAssertions=[]
		
		self.classOrder=[]

		
		self.smtFacts=""

		self.smtlib_gen=smtlib_gen
		

	def addClassOrder(self, parent, child):
		fullList=[child.name, parent.name]
		prefix=False
		for l in self.classOrder:
			if l[0]==fullList[1]:
				fullList.extend(l[1:])
			if l[-1]==fullList[0]:
				l.extend(fullList[1:])
				prefix=True
				       
		if not prefix:
			self.classOrder.append(fullList)
				
			


	def addRangeAssertion(self, name, typ, rng):
		self.rangeAssertions[name]= {"type":typ, "ranges":rng}

		
	def addTesterAssertion(self, a):
		self.testerAssertions.append(a)

	def removeTesterAssertion(self, k):
		self.testerAssertions.remove(k)

	def addDerivedSort(self, k, t):
		
		self.derivedSorts[k]=t

	def addEnum(self, k, t):
		self.enumDatatypes[k]=t

	def addStruct(self, k, t):
		self.structDatatypes[k]=t

	def addClass(self, cls):
		self.classDatatypes.append(cls)

	def storeSMTLIBString(self):
		l=[self.smtlib_gen.get_smt_comment("files: "+",".join(self.filenames))]
		l.append(self.smtlib_gen.get_smt_commented_section("DATATYPES"))

	      	l.append(self.smtlib_gen.get_smt_comment("SPECIAL BUILDING BLOCKS"))
		for n, t in self.specialBuildingBlocks.iteritems():
			l.append(self.smtlib_gen.get_smt_sort(n, t["smtType"]))
			l.append("\n")	
		l.append("\n")
		l.append(self.smtlib_gen.get_smt_comment("DERIVED TYPES"))
		for n, t in self.derivedSorts.iteritems():
			l.append(self.smtlib_gen.get_smt_sort(n, t))
			l.append("\n")
		l.append("\n")
		l.append(self.smtlib_gen.get_smt_comment("SPECIAL TYPES"))
		for name, f in self.specialDatatypes.iteritems():
			datatypes=set()
			definition=[name, "_dt(mk_", name]
			if "fields" in f:
				for field in sorted(f["fields"]):
					datatypes.add(f["fields"][field]["baseType"])
					definition.append("".join([" (",field," ",f["fields"][field]["baseType"],")"]))
			else:
				print "NO FIELDS FOUND FOR {0}".format(name)
			definition.append(")")
			datatypes=" ".join(datatypes)
			

			l.append(self.smtlib_gen.get_smt_comment(name))
			l.append(self.smtlib_gen.get_smt_datatypes(datatypes, "".join(definition)))
			l.append("\n")
			l.append(self.smtlib_gen.get_smt_sort(name, "".join(["(",name,"_dt ",datatypes,")"])))
			l.append("\n\n")

		for name, f in self.specialExclusiveDatatypes.iteritems():
			definition=[name]
			if "options" in f:
				for option, fields in f["options"].iteritems():
					definition.append("(")
					definition.append(option)
					optnum=option[7:]
					if "fields" in fields:
						for name1, val in fields["fields"].iteritems():
							definition.append("".join([" (", name1+"_"+optnum, " ", val["baseType"], ")"]))
					else:
						print "NO FIELDS FOUND FOR {0}, option {1}".format(name,option)
					definition.append(")")
					
				l.append(self.smtlib_gen.get_smt_comment(name))
				l.append(self.smtlib_gen.get_smt_datatypes("", "".join(definition)))
			#l.append("\n")
			#l.append(self.smtlib_gen.get_smt_sort(name, "".join(["(", name, "_dt ", datatypes, ")"])))
				l.append("\n\n")
				 

			
		l.append(self.smtlib_gen.get_smt_comment("ENUM TYPES"))
		for t in self.enumDatatypes:
			l.append(self.smtlib_gen.get_smt_datatypes("", t+" "+(" ".join(self.enumDatatypes[t]))))
			l.append("\n")

		l.append("\n")
		
		l.append(self.smtlib_gen.get_smt_comment("STRUCTS"))
		temp_exclusive="({0} ({1} {2}))"
		temp="({0} {1})"
		for t in self.structDatatypes:
			if not self.structDatatypes[t][0]:
				dts=[t, "(","mk_"+str(t)]+[temp.format(x["name"], x["dataType"]) for x in self.structDatatypes[t][1]]+[")"]
			else:
				dts=[t]+[temp_exclusive.format(x["name"], x["name"]+"_dt", x["dataType"]) for x in self.structDatatypes[t][1]]
			l.append(self.smtlib_gen.get_smt_datatypes("", " ".join(dts)))

		l.append(self.smtlib_gen.get_smt_commented_section("CLASSES AND CONSTRUCTORS"))
		for c in self.classDatatypes:
			l.append(c.getSMTLIBString(self.smtlib_gen))

		l.append(self.smtlib_gen.get_smt_commented_section("ASSERTIONS"))
		for name, body in self.rangeAssertions.iteritems():
			l.append(self.smtlib_gen.get_smt_range_assertion(name, body["type"], body["ranges"]))
			l.append("\n")
		self.smtFacts="".join(l)

	def toSMTLIB(self):
		s=[self.smtFacts,self.smtlib_gen.get_smt_commented_section("TEST ASSERTIONS")]
		for a in self.testerAssertions:
			s.append(a)
			s.append("\n")
		return "".join(s)


		
"""
Main method for building the SMTLIB facts
"""
#def buildSMTLIBFacts(filenames, parse_obj, smtlib_gen):#
	#print "BOUNDARIES:", parse_obj.boundaries
#	facts=SMTFacts(filenames, smtlib_gen)
	
#	for m in parse_obj.xml2SMT:
#		smt_type_translation[m]=parse_obj.xml2SMT[m]

	#methodCall=getattr(SMTFacts, "set")
#	for p in parse_obj.dataTypes.values():
#		methodName="add{0}".format(string.capitalize(p.type))

#	createDerivedSorts(facts, parse_obj.derivedTypes)
#	createEnums(facts, parse_obj.enumTypes)
#	createStructs(facts, parse_obj.structTypes)
#	createClasses(facts, parse_obj)

#	createClassOrder(facts, parse_obj)
#	facts.storeSMTLIBString()

#	return facts


def createClassOrder(facts, parse_obj):
	for parent, child in parse_obj.pc_relations:
		facts.addClassOrder(parent, child)

"""
Creates the SMTLIB2 declarations for the derived types.
If the base-type contains a range, we call the assertion_handler again.
input:
types: dict of name -> baseType[range]
"""
def createDerivedSorts(facts, types):
	for k in types:
		(typ, rng)=Util.get_name_range(types[k]["baseType"])
		facts.addDerivedSort(k, get_smt_type(typ))
		

"""
Creates the SMTLIB2 declarations for the enums.
input:
enums: name -> members
"""
def createEnums(facts, enums):
	for key in enums:
		name=key
		temp=[(name+"_"+s) for s in enums[key] ]
		facts.addEnum(name, temp)

    
def createStructs(facts, structs):
	for name in structs:
		for member in structs[name][1]:
			member["dataType"]=get_smt_type(member["dataType"])

	facts.addStruct(name, structs[name])
	    
	    
"""
Creates the SMTLIB2 declarations for classes. Takes the whole parse_object.
input 
"""
def createClasses(facts, parse_obj):
	for cl in parse_obj.classes:
		clsDt=ClassType(cl)
		for a in parse_obj.classes[cl].attributes:
			#if a["dataType"] not in parse_obj.boundaries:
			#	print "BOUNDARY MISSING FOR {0}".format(a["dataType"])
			if a["dataType"] in parse_obj.oldNewTranslations:
				details=parse_obj.oldNewTranslations[a["dataType"]]
				newType=None
				if details["newName"] in parse_obj.annotatedTypes:
					newType=parse_obj.annotatedTypes[details["newName"]]
				elif details["newName"] in parse_obj.exclusiveTypes:
					newType=parse_obj.exclusiveTypes[details["newName"]]
				clsDt.addAttribute(a["name"], details["newName"], parse_obj.boundaries[details["newName"]])
				ranges={}
				if "ranges" in details:
					for field in details["ranges"]:
						ranges[field]=details["ranges"][field]
						baseTypeName=parse_obj.buildingBlocks[newType["fields"][field]["baseType"]]["type"]
						facts.addRangeAssertion("({0} ({1} {2}))".format(field, a["name"], clsDt.instance_function), baseTypeName, ranges[field])

				if "fields" in newType:
					for field in newType["fields"]:
						if field not in ranges:
							ranges[field]=newType["fields"][field]["range"]
							facts.addRangeAssertion("({0} ({1} {2}))".format(field, a["name"], clsDt.instance_function), baseTypeName, [ranges[field]])
						baseTypeName=parse_obj.buildingBlocks[newType["fields"][field]["baseType"]]["type"]
						
				elif "options" in newType:
					for option in newType["options"]:
						pass
				else:
					print "NO FIELDS FOR ATTRIBUTE {0} TYPE {1}".format(a["name"], a["dataType"])
					
			elif a["dataType"] in parse_obj.enumTypes:
				clsDt.addAttribute(a["name"], a["dataType"], parse_obj.boundaries[a["dataType"]])
			elif a["dataType"] in parse_obj.structTypes:
				temp=parse_obj.boundaries[a["dataType"]]
				to_add={}
				for key, value in temp.iteritems():
					if key!=get_smt_type(key):
						to_add[get_smt_type(key)]=value
					to_add[key]=value
				clsDt.addAttribute(a["name"], a["dataType"], to_add)
			elif a["dataType"] in parse_obj.derivedTypes:
				baseType=parse_obj.derivedTypes[a["dataType"]]["baseType"]
				clsDt.addAttribute(a["name"], a["dataType"], parse_obj.boundaries[a["dataType"]])
				if "range" in parse_obj.derivedTypes[a["dataType"]]:
					rng=parse_obj.derivedTypes[a["dataType"]]["range"]
					facts.addRangeAssertion("({0} {1})".format(a["name"], clsDt.instance_function), get_smt_type(baseType), rng)
			elif a["dataType"]=="string":
				clsDt.addAttribute(a["name"], get_smt_type(a["dataType"]), [])
			else:
				print "UNKNOWN ATTRIBUTE TYPE: attribute name: ", a["name"], "type:", a["dataType"]

		facts.addClass(clsDt)
		

def buildSMTLIBFacts(files, parse_obj, smtlib_gen):
	parse_obj.dataTypes
	mthds= {a : SMTLIBHandler.__dict__.get(a) for a in dir(SMTLIBHandler)}
	for x in sorted(parse_obj.dataTypes.values(), key=lambda x: x.level, reverse=True):
		typestr=x.__class__.__name__
		if "get{0}SMT".format(typestr) not in mthds:
			print "get{0}SMT is missing in SMTLIBHandler".format(typestr)
		else:
			method=mthds["get{0}SMT".format(typestr)]
			setattr(x.__class__, "getSMT", method)
		if "init{0}SMT".format(typestr) in mthds:
			method1=mthds["init{0}SMT".format(typestr)]
			setattr(x.__class__, "init", method1)
			x.init(parse_obj)

	for y in parse_obj.classes.values():
		typestr=y.__class__.__name__
		if "init{0}SMT".format(typestr) in mthds:
			method2=mthds["init{0}SMT".format(typestr)]
			setattr(y.__class__, "init", method2)
			y.init(parse_obj)
		if "get{0}SMT".format(typestr) not in mthds:
			print "get{0}SMT is missing in SMTLIBHandler".format(typestr)
		else:
			method=mthds["get{0}SMT".format(typestr)]
			setattr(y.__class__, "getSMT", method)

	res=[smtlib_gen.get_smt_comment("mp_files:\t{0}".format(",".join(files))),
	     smtlib_gen.get_smt_comment("creation-date:\t{0}".format(time.strftime("%c"))),
	     smtlib_gen.get_smt_comment("created by:\tctcGen-tool v 1.0"),
	     smtlib_gen.get_smt_comment("author:\tPaul Borek"),
	     "\n"]
	res.append(smtlib_gen.get_smt_commented_section("DATATYPES"))
	
	data=sorted(parse_obj.dataTypes.values(), key=lambda x: x.level, reverse=True)
	for key, group in groupby(data, key=lambda x: SMTLIBHandler.name(x.__class__)):
		res.append(smtlib_gen.get_smt_comment(key))
		#res.append("\n") #smtlib_gen.get_smt_comment(key))
		for x in group:
			res.append(x.getSMT(smtlib_gen, parse_obj))
		res.append("\n")

	res.append(smtlib_gen.get_smt_commented_section("CLASSES and ASSERTIONS"))
	for c in parse_obj.classes.values():		
		res.append(smtlib_gen.get_smt_comment(c.name))
		res.append(c.getSMT(smtlib_gen))
		res.append("\n")

	return "".join(res)


def storeSMTLIBString(self):
		l.append(self.smtlib_gen.get_smt_commented_section("ASSERTIONS"))
		for name, body in self.rangeAssertions.iteritems():
			l.append(self.smtlib_gen.get_smt_range_assertion(name, body["type"], body["ranges"]))
			l.append("\n")
		self.smtFacts="".join(l)
