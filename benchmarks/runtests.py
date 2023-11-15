import os
import sys
import socket
from datetime import date

def getOption(str) :                                                                                
    return sys.argv.count(str) > 0                                                                  
                                                                                                    
def getArg(str, default) :                                                                          
  a = sys.argv                                                                                      
  l = len(a)                                                                                        
  for i in range(1, l) :                                                                            
    if (a[i] == str and  (i+1 != l)) :                                                              
        return sys.argv[i+1]                                                                        
  return default

rounds = int(getArg("-r", 0));

time = float(getArg("-t", 0.0));

shuffle = getOption("-shuffle");

test_only = getOption("-test")

today = date.today().strftime("%m_%d_%y")
hostname = socket.gethostname()

print(hostname)
print(today)
    
def detectCPUs():
    """
     Detects the number of CPUs on a system. Cribbed from pp.
     """
    # Linux, Unix and MacOS:
    if hasattr(os, "sysconf"):
       if "SC_NPROCESSORS_ONLN" in os.sysconf_names :
           # Linux & Unix:
           ncpus = os.sysconf("SC_NPROCESSORS_ONLN")
           if isinstance(ncpus, int) and ncpus > 0:
               return ncpus
       else: # OSX:
           return int(os.popen2("sysctl -n hw.ncpu")[1].read())
    # Windows:
    if os.environ.has_key("NUMBER_OF_PROCESSORS"):
           ncpus = int(os.environ["NUMBER_OF_PROCESSORS"]);
           if ncpus > 0:
               return ncpus
    return 1 # Default

maxcpus = detectCPUs()

class parameters :
    time = 1
    rounds = 1
    zipfians = []
    file_suffix = ""
    lists = []
    lists_ro = []
    list_sizes = []
    trees = []
    trees_ro = []
    tree_sizes = []
    suffixes_all = [""]
    suffixes_ro = []
    mix_percents = [[5,0,0,0]]
    trans_sizes = [0]
    processors = [maxcpus-1]

def runstring(op, outfile) :
    use_outfile = not(test_only) and len(outfile) > 0
    if use_outfile :
        cmd = op + " >> " + outfile
    else :
        cmd = op
    os.system("echo \"" + cmd + "\"")
    x = os.system(cmd)
    if (x) :
        if (os.WEXITSTATUS(x) == 0) : raise NameError("  aborted: " + op)
        if use_outfile :
            os.system("echo \"Failed: " + op + "\" >> " + outfile)
        os.system("echo Failed")

def runtest(test,procs,n,z,mix,ts,params,filename) :
    num_threads = max(procs,maxcpus)
    if mix[1] > 0: str_mfind = "-mfind "
    else : str_mfind = ""
    str_proc = "-p " + str(procs) + " "
    str_mix = "-u " + str(mix[0]) + " " # " -rqthreads " + str(mix[2]) + " "
    str_rs = "" # "-rs " + str(mix[3]) + " "
    str_zipfians = "-z " + str(z) + " "
    str_trans_size = "" # "-trans " + str(ts) + " "
    num_rounds = rounds
    if (num_rounds == 0) :
        num_rounds = params.rounds
    str_rounds = "-r " + str(num_rounds) + " "
    run_time = time
    if (run_time == 0.0) : run_time = params.time
    str_time = "-tt " + str(run_time) + " "
    str_n = "-n " + str(n) + " "
    if shuffle : str_other = "-shuffle "
    else : str_other = ""
    runstring("PARLAY_NUM_THREADS=" + str(num_threads) + " numactl -i all ./" + test + " " + str_time + str_rounds + str_n + str_mfind + str_mix + str_rs + str_proc + str_zipfians + str_trans_size + str_other + "-nomeans", filename)

def run_tests(tests, sizes, params, filename) :
    for test in tests :
        for suffix in params.suffixes_all:
            for n in sizes :
                for mix in params.mix_percents :
                    for ts in params.trans_sizes :
                        for z in params.zipfians :
                            for p in params.processors :
                                runtest(test + suffix, p, n, z, mix, ts, params, filename)
                with open(filename, "a") as f:
                    f.write("...\n")


def run_all(params) :
    filename = "../../timings/" + hostname[0:5] + "_" + params.file_suffix + "_" + today
    if test_only :
        params.time = .2
        params.zipfians = [.99]
        params.tree_sizes = [1,1000,100000]
        params.list_sizes = [1, 100]
        params.trans_sizes = [16]
        params.mix_percents = [[50,0,0,0]]
        params.processors = [maxcpus]
    run_tests(params.trees, params.tree_sizes, params, filename)
    run_tests(params.lists, params.list_sizes, params, filename)            
                    
def compile_clear(file_suffix) :
    os.system("make -j")
    runstring("git rev-parse --short HEAD", "")
    filename = "../../timings/" + hostname[0:5] + "_" + file_suffix + "_" + today
    if os.path.exists(filename) :
        os.remove(filename)
