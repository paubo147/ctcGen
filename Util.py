import re
import xml.etree.cElementTree as ET
from xml.dom import minidom


"""
enum function for python<3.4
"""
def enum(**members):
    return type("Enum", (object,), members)

"""
returns the hex value (in string representation)
in a SMTLIB-conform hex value i.e., #xff #xa3
"""
def getSMThex(s, i=2):
    plain_hex=hex(int(s))
    digits=re.findall("\d+", plain_hex[1:])
    if i-len(digits[0]) < 0:
        raise Exception("argument should be smaller than hex-representation: i="+i+", hex="+digits[0])
    return "#x"+ ("0"*(i-len(digits[0])))+"".join(digits[0])

        
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
    rough_string=ET.tostring(elem)
    reparsed=minidom.parseString(rough_string)
    return reparsed.toprettyxml(indent)
