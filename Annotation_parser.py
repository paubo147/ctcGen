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
        root=ET.ElementTree(file=f)

        #buildingblocks for datatypes
        for bb in root.findall("buildingBlock"):
            name=bb.get("name")
            smt=bb.find("smt").text
            typ=bb.get("type")
            annotations["bb_"+name]=(typ,smt)
            
        #datatypes
        for dt in root.findall("datatype"):
            dt_name=dt.get("name")
            fields=dt.find("fields")
            if fields is not None:
                no_fields=int(fields.get("cardinality"))
                prefix=fields.get("prefix")
                f=fields.find("field")
                basetype=f.find("bb").text
                rng=[f.find("range").find("min").text, f.find("range").find("max").text]
                fs=dict()
                for i in range(no_fields):
                    fs[prefix+str(i)]=(basetype, rng)
                annotations["dt_"+dt_name]=fs
            else:
                #TODO what about simplier datatypes, like "string" ---> covered in basic building blocks
                print "ANNOTATION_PARSER: DUNO WHAT TO DO!"
                exit()

        #datatypeAnnotations
        for ann in root.findall("dtMapping"):
            oldName=ann.get("old")
            newName=ann.get("new")
            ranges=getRanges(ann)
            annotations["on_"+oldName]=[newName, ranges]

        #solver-things
        solver_root=root.findall("solver")[0]
        annotations["solver_path"]=solver_root.find("path").text
        i=0
        for arg in solver_root.findall("arg"):
           annotations["solver_arg{0}".format(i)]=arg.text
           i+=1
    return annotations
                

             
