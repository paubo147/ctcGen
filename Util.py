import re
from lxml import etree as ET
import ast
import random
import string

def get_random_string():
    size=random.randint(5, 30)
    return "".join(random.choice(string.ascii_uppercase + string.digits) for _ in range(size))

def get_proper_int(s):
    ret=0
    try:
        ret=int(s)
    except ValueError:
        ret=int("0"+s[1:], 16)
    return ret

def get_name_range(s):
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

def get_pretty_XML(elem, indent=" "):
    print elem
    return ET.tostring(elem, pretty_print=True)
