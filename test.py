import subprocess

def print_out(out):
    print out


args=["/home/ebopaul/Documents/smt/z3-4.3.2.8ef4ec7009ab-x64-debian-7.4/bin/z3", "-smt2", "_temp_smt_facts.smt2"]

process=subprocess.Popen(args, stdout=subprocess.PIPE)
out, err=process.communicate()
print_out(out)
