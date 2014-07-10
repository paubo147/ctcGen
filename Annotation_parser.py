from lxml import etree as ET



def getRanges(et):
    ret={}
    for p in et:
        fieldname=p.tag
        ranges=list()
        for r in p.findall("range"):
            ranges.append([r.find("min").text, r.find("max").text])
        ret[fieldname]=ranges
    return ret

def parse_annotation_file(file):
    annotations={}
    with open(file, "r") as f:
        root=ET.ElementTree(file=f)
        #smtmappings
        for m in root.findall("xml2SMTmapping"):
            annotations["mapping_"+m.get("xml")]=m.get("smt")


        #buildingblocks for datatypes
        for bb in root.findall("buildingBlock"):
            name=bb.get("name")
            smt=bb.find("smt").text
            typ=bb.get("type")
            annotations["bb_"+name]={"type":typ,"smtType":smt}
            
        #datatypes
        for dt in root.findall("datatype"):
            dt_name=dt.get("name")
            fields=dt.find("fields")
            if fields is not None:
                no_fields=int(fields.get("cardinality"))
                prefix=fields.get("prefix")
                f=fields.find("field")
                basetype=f.find("bb").text
                delimiter=dt.find("delimiter").text
                rng=[f.find("range").find("min").text, f.find("range").find("max").text]
                fs={}
                produce_str=[]
                for i in range(no_fields):
                    fs[prefix+str(i)]={"basetype": basetype, "range":rng}
                    produce_str.append("field")
                    if i < no_fields-1:
                        produce_str.append(delimiter)
                        #fs["delimiter_"+prefix+str(i)]=delimiter

                fs["produce_string"]=produce_str
                    
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
            annotations["on_"+oldName]={"newName":newName, "ranges":ranges}

        #solver-things
        solver_root=root.findall("solver")[0]
        annotations["solver_path"]=solver_root.find("path").text
        i=0
        for arg in solver_root.findall("arg"):
           annotations["solver_arg{0}".format(i)]=arg.text
           i+=1
    return annotations
                

             
