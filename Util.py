import re
from lxml import etree as ET
import ast

def get_name_range(s):
    print "NAME_RANGE:", s
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
    else:
        return (s, None)

def getPrettyXML(elem, indent=" "):
    return ET.tostring(elem, pretty_print=True)
