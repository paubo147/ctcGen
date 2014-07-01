import re
from lxml import etree as ET

"""
enum function for python<3.4
"""
def enum(**members):
    return type("Enum", (object,), members)

"""
returns the hex value (in string representation)
in a SMTLIB-conform hsaex value i.e., #xff #xa3
"""
def getSMThex(s, i=2):
    plain_hex=hex(int(s))[2:]
    return "#x"+plain_hex.zfill(i)
        
"""
returns the plain name of a string of the following shape:
"test[1:2]", "string[12:15]"

"""
def get_plain_name(s):
    if "[" in s:
        return s[0:s.find("[")]
    return s  

"""
in my case s can look like:
uint8, uint16, uint32, ..., int8, int16, int32,...
anyname['1','5'],...
"""
def get_range(s):
	if "[" in s:
		return re.findall(r"\d+",s[s.find("[")+1:])	
	elif "int" in s:
		num=0
		if s[-2:]=="t8":
			num=8
		else:
			num=int(s[-2:])
			
		if s[0] == "u":
			return (0, (2**num)-1)
		else:
			return (-(2**(num-1)), 2**(num-1)-1)
	else:
		return None


def getPrettyXML(elem, indent=" "):
    return ET.tostring(elem, pretty_print=True)
