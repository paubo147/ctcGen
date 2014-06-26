import xml.etree.cElementTree as ET



def getRanges(et):
    ret=dict()
    for p in et:
        fieldname=p.tag
        ranges=list()
        for r in p.findall("range"):
            ranges.append([r.find("min").text, r.find("max").text])
        ret[fieldname]=ranges
    return ret

def parse_annotation_file(file):
    annotations=dict()
    with open(file, "r") as f:
        #datatypeAnnotations
        root=ET.ElementTree(file=f)
        for ann in root.findall("dtMapping"):
            oldName=ann.get("old")
            newName=ann.get("new")
            ranges=getRanges(ann)
            annotations[oldName]=[newName, ranges]

        #solver-things
        solver_root=root.findall("solver")[0]
        annotations["solver_path"]=solver_root.find("path").text
        i=0
        for arg in solver_root.findall("arg"):
           annotations["solver_arg{0}".format(i)]=arg.text
           i+=1
    return annotations
                

             
