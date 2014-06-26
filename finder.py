#!/usr/bin/python
import sys
import os

if __name__=="__main__":
    if len(sys.argv) != 2:
        print("Usage: 'finder [mim::class]'")
        exit(-2)
    mim_cls=sys.argv[1]
    mim=mim_cls[:mim_cls.find("::")]
    cls=mim_cls[mim_cls.find("::")+2:]
    models_folder="/home/ebopaul/Documents/ctcGen/models"
 
    mim_in_file="0"
    cls_in_file="-1"
    for subdir, dirs, files in os.walk(models_folder):
        for file in files:
            if file[0] not in ("#", "."):
                with open(subdir+"/"+file) as f:
                    for l in f:
                        if "<mim " in l and 'name="'+mim+'"' in l:
                            print(file)
                            mim_in_file=file
                        if "<class " in l and 'name="'+cls+'"' in l:
                            print(file)
                            cls_in_file=file
                        if mim_in_file==cls_in_file:
                            print(file)
                            exit(0)
    print("mim and class not found!")

    
