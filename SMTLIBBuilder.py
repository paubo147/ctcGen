from itertools import groupby

import SMTLIBHandler


from itertools import groupby

def update(smtgen):
	ret=list(fixedString)
	ret.append(smtgen.get_smt_commented_section("TESTER ASSERTIONS"))
	for a in SMTLIBHandler.testerAssertionsIter():
		ret.append(a.getSMT(smtgen))
		ret.append("\n")
      	return "".join(ret)


def init(smtlib_gen, parse_obj):
	print "INITALIZING SMTLIBHandler ..."
	mthds= {a : SMTLIBHandler.__dict__.get(a) for a in dir(SMTLIBHandler)}
	for x in parse_obj.dataTypes.values():
		typestr=x.__class__.__name__
		if "init{0}SMT".format(typestr) in mthds:
			method1=mthds["init{0}SMT".format(typestr)]
			setattr(x.__class__, "init", method1)
			x.init(smtlib_gen, parse_obj)

	for y in parse_obj.classes.values():
		typestr=y.__class__.__name__
		if "init{0}SMT".format(typestr) in mthds:
			method2=mthds["init{0}SMT".format(typestr)]
			setattr(y.__class__, "init", method2)
			y.init(smtlib_gen, parse_obj)




def buildSMTLIBFacts(files, parse_obj, smtlib_gen):
	print "BUILDING SMTLIB CODE"
	global fixedString
	fixedString=SMTLIBHandler.get_preface(smtlib_gen, files)
	
	fixedString.append(smtlib_gen.get_smt_commented_section("DATATYPES"))
	data=sorted(parse_obj.dataTypes.values(), key=lambda x: x.level, reverse=True)

	for k, group in groupby(data, key=lambda x:x.level):
		if k!=0:
			for val in group:
				fixedString.append(val.smt)

	fixedString.append(smtlib_gen.get_smt_commented_section("CLASSES and ASSERTIONS"))
	for c in parse_obj.classes.values():		
		fixedString.append(c.smt)

	# Here, the inter-class relationshipts (only assertions)

	for c in parse_obj.pc_relations:
		fixedString.append(smtlib_gen.get_smt_assertion("(< {0} {1})".format(c[0].name+"_sortkey", c[1].name+"_sortkey"))+"\n")
		#print "(assert (<= {0} {1}))".format(c[0].name+"_sortkey", c[1].name+"_sortkey")

	return "".join(fixedString)

