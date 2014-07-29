from itertools import groupby
from time import strftime

import SMTLIBHandler


from itertools import groupby

def update(smtgen):
	ret=list(fixedString)
	ret.append(smtgen.get_smt_commented_section("TESTER ASSERTIONS"))
	for a in SMTLIBHandler.testerAssertionsIter():
		ret.append(a.getSMT(smtgen))
		ret.append("\n")
      	return "".join(ret)


def init(files, parse_obj):
	print "INITALIZING SMTLIBHandler ..."
	mthds= {a : SMTLIBHandler.__dict__.get(a) for a in dir(SMTLIBHandler)}
	for x in parse_obj.dataTypes.values():
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

def buildSMTLIBFacts(files, parse_obj, smtlib_gen):
	print "BUILDING SMTLIB CODE"
	global fixedString
	fixedString=[smtlib_gen.get_smt_comment("mp_files:\t{0}".format(",".join(files))),
		     smtlib_gen.get_smt_comment("creation-date:\t{0}".format(strftime("%c"))),
		     smtlib_gen.get_smt_comment("created by:\tctcGen-tool v 1.0"),
		     smtlib_gen.get_smt_comment("author:\tPaul Borek"),
		     "\n"]
	fixedString.append(smtlib_gen.get_smt_commented_section("DATATYPES"))
	data=sorted(parse_obj.dataTypes.values(), key=lambda x: x.level, reverse=True)

	for k, group in groupby(data, key=lambda x:x.level):
		if k!=0:
			for val in group:
				fixedString.append(val.getSMT(smtlib_gen, parse_obj))

	#for key, group in groupby(data, key=lambda x: SMTLIBHandler.sortkey(x.__class__)):
#		fixedString.append(str(key))
		#res.append("\n") #smtlib_gen.get_smt_comment(key))
#		for x in group:
#			fixedString.append(x.getSMT(smtlib_gen, parse_obj))
#		fixedString.append("\n")

	fixedString.append(smtlib_gen.get_smt_commented_section("CLASSES and ASSERTIONS"))
	for c in parse_obj.classes.values():		
		fixedString.append(smtlib_gen.get_smt_comment(c.name))
		fixedString.append(c.getSMT(smtlib_gen))
		fixedString.append("\n")

	return "".join(fixedString)









def storeSMTLIBString(self):
		l.append(self.smtlib_gen.get_smt_commented_section("ASSERTIONS"))
		for name, body in self.rangeAssertions.iteritems():
			l.append(self.smtlib_gen.get_smt_range_assertion(name, body["type"], body["ranges"]))
			l.append("\n")
		self.smtFacts="".join(l)
