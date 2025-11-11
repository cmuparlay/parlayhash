#!/bin/bash

structs="parlay_hash parlay_hashlf parlay_hashnoopt parlay_hashindirect tbb_hash libcuckoo folly_sharded folly_hash parallel_hashmap seq_hash"
threads="8 16 32 64 96 192 384"
head="numactl -i all"

# print various imformation about the machine/compiler/date at head of file
procs=`nproc`
today=`date +"%m-%d-%Y"`
machine=`lscpu | grep 'Model name' | rev | cut -c 1-5 | rev`
machine_nowhite=${machine//[[:space:]]/}
filename=../../timings/${procs}-${machine}_${today}

echo ${filename}
> ${filename}
echo "Date:" ${today} >> ${filename}
echo `lscpu | grep 'Model name'` >> ${filename}
echo "Git branch:" `git rev-parse --short HEAD` >> ${filename}
echo "Compiler:" `g++ --version | head -1` >> ${filename}
echo "OS:" `lsb_release -a | grep 'Description' | cut -c 14-` >> ${filename}
echo "Hugepage:" `cat /sys/kernel/mm/transparent_hugepage/enabled` >> ${filename}

# non list structures
for struct in ${structs}
do
    echo ${struct}
    for tr in ${threads}
    do
        PARLAY_NUM_THREADS=${tr} ${head} ./${struct} >> ${filename}
    done
done
