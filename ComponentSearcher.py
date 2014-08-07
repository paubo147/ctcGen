from lxml import etree as ET


def searchForAttribute(xml_files, tagname, name, nameMatch):
    for f in xml_files:
        with open(f, "r") as fl:
            el=ET.ElementTree(file=fl)
            for x in el.iter(tagname):
                if x.get(name)==nameMatch:
                    return (f,nameMatch, x.getparent().get("name"))
    return (None, None, None)


def searchComponent(xml_files, cls, mim):
    my_mim=""
    my_class=""
    my_file=""
    if mim:
        (my_file, my_mim, dummy) = searchForAttribute(xml_files, "mim", "name", mim)

    if my_file:
        if cls:
            (my_file, my_mim, dummy)=searchForAttribute([my_file], "class", "name", cls)
            if my_mim:
                print my_mim+"::"+cls+" found in '"+my_file+"'"
            else:
                print my_mim+" found in '"+my_file+"', "+cls+" not found!"
        else:
            print my_mim+" found in '"+my_file+"'"
    else:
        if cls:
            (my_file, my_mim, parent) = searchForAttribute(xml_files, "class", "name", cls)
            if my_file and my_mim and parent:
                print cls+" found in "+my_file+"::"+parent
            else:
                print cls+" was not found!"
        else:
            print mim+" not found!"
       
