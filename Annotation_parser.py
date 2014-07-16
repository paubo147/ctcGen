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
                    fs[prefix+str(i)]={"baseType": basetype, "range":rng}
                    produce_str.append("field")
                    if i < no_fields-1:
                        produce_str.append(delimiter)
                        #fs["delimiter_"+prefix+str(i)]=delimiter

                fs["produce_string"]=produce_str
                    
                annotations["dt_"+dt_name]=fs
            else:
                #NASTY STUFF: no fields? probably an exclusive datatype
                options={}
                for option in dt.iter("option"):
                    option_id=option.get("id")
                    delimiter=option.find("delimiter").text
                    produce_str=[]
                    fields={}
                    for field in option.iter("field"):
                        if field.find("bb") is not None:
                            bt=field.find("bb").text
                        elif field.find("dtRef") is not None:
                            bt=field.find("dtRef").text
                        if field.find("range") is not None:
                            rng=[field.find("range").find("min").text, field.find("range").find("max").text]
                        vals={}
                        vals["baseType"]=bt
                        if rng:
                            vals["range"]=rng
                        fields[field.get("id")]=vals
                        produce_str.append("field")
                        produce_str.append(delimiter)
                        
                    options["option_"+option_id]={"delimiter":delimiter, "produce_string": produce_str[:-1], "fields": fields}
                annotations["exdt_"+dt_name]=options


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

        #strategy
        strat=root.find("strategy")
        for e in strat:
            if e.tag=="maxCoverage":
                val=e.find("value").text
                unit=e.find("unit").text
                annotations["strategy_maxCoverage"]={"value":val, "unit":unit}
            if e.tag=="behavior":
                annotations["behavior_attributes"]=e.find("attributes").text
    return annotations
                

             
