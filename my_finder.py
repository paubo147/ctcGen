import xml.etree.cElementTree as ET
import os
import glob

if __name__=="__main__":
    xml_files=list()
    for filename in os.listdir("/home/ebopaul/Documents/ctcGen/models"):
        if "mp.xml" in filename:
            xml_files.append("/home/ebopaul/Documents/ctcGen/models/"+filename)

    models=list()
    dts=dict()

    for f in xml_files:
        with open(f, "r") as fl:
            el=ET.ElementTree(file=fl)

            for x in el.iter("derivedDataType"):
                if x.find("baseType")[0].find("validValues") is not None:
                    name=x.get("name")
                    rest=dict()
                    rest["BASETYPE"]=x.find("baseType")[0].tag
                    if x.find("description") is not None:
                        rest["DESCRIPTION"]=x.find("description").text
                    rest["VALIDVALS"]=x.find("baseType")[0].find("validValues").text
                    dts[name]=rest
                
    for key, values in dts.iteritems():
        print "NAME: ", key
        print "DESCRIPTION;", values.get("DESCRIPTION", "NATHING")
        print "VALIDVALUES:", values.get("VALIDVALS", "NATHING")
        print "-----------------------------------"
