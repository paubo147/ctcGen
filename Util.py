import re
from lxml import etree as ET
import ast
import random
import string

def get_random_string(x):
    size=random.randint(5, 30)
    return "".join(random.choice(string.ascii_uppercase + string.digits) for _ in range(size))

def get_proper_int(s):
    #print s
    ret=0
    try:
        ret=int(s)
    except ValueError:
        ret=int("0"+s[1:], 16)
    return ret

def getNameRange(s):
    name=""
    rang=""
    if "[" in s:
        i=s.find("[")
        rang=ast.literal_eval(s[i:])
        #rang=[i.strip() for i in rang]
        name=s[:i]
        return (name, rang)
    elif "int" in s:
    	num=0
        if s[-2:]=="t8":
            num=8
        else:
            num=int(s[-2:])
			
        if s[0] == "u":
            return (s, [[0, (2**num)-1]])
        else:
            return (s, [[-(2**(num-1)), 2**(num-1)-1]])
    elif s=="boolean":
        return (s, [["true"], ["false"]])
    else:
        return (s, [])


def getPartitions(typ,rnge):
    if typ=="boolean":
        return [[1], [0], [None], [4]]
    elif typ=="string":
        return [[]]
    else:
        if rnge is not None:
            boundaries=[]
            n=3 #could be passed as a parameter
            for rng in rnge:
                b=get_proper_int(rng[1])
                a=get_proper_int(rng[0])
                division=(b-a)/float(n)
                for i in range(n):
                    boundaries.append([int(a+i*division+(1 if i!=0 else 0)),int(a+(i+1)*division)])
            #print boundaries, min(boundaries)[0], max(boundaries)[-1]
            boundaries.append(["-x", min(boundaries)[0]])
            boundaries.append([max(boundaries)[-1], "x"])
            boundaries.append([None])
            return boundaries

def getBoundaries(typ, rnge):
    if typ=="boolean":
        return [["true"], ["false"]]
    elif typ=="string":
        return [[]]
    else:
        if rnge is not None:
            boundaries=[]
            n=3 #could be passed as a parameter
            for rng in rnge:
                b=get_proper_int(rng[1])
                a=get_proper_int(rng[0])
                division=(b-a)/float(n)
                for i in range(n):
                    boundaries.append([int(a+i*division+(1 if i!=0 else 0)),int(a+(i+1)*division)])
            return boundaries

def getEnumBoundaries(members):
    if len(members) < 10:
        return [[m] for m in members]
    else:  
        return [[members[x[0]],members[x[1]]]for x in getBoundaries(None, [[0, len(members)-1]])]

def get_pretty_XML(elem, indent=" "):
    return ET.tostring(elem, pretty_print=True)
