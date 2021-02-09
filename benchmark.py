import os
import time
import subprocess
import csv
import sys
import functools
import signal
# Timeout code adapted from: https://stackoverflow.com/questions/1359383/run-a-process-and-kill-it-if-it-doesnt-end-within-one-hour

def wait_timeout(proc, seconds):
    """Wait for a process to finish, or raise exception after timeout"""
    start = time.time()
    end = start + seconds
    interval = min(seconds / 1000.0, .25)

    while True:
        result = proc.poll()
        if result is not None:
            return result
        if time.time() >= end:
            raise TimeoutError
        time.sleep(interval)

# Dynamic reordering: No dynamic reordering, reordering with window2, etc.
reordering_options = ['', "-reordering 0", "-reordering 1", "-reordering 2", "-reordering 3", "-reordering 4"]
# if you don't want to wait for 6 different executions, you can use a smaller list e.g.,
# reordering_options = ['',"-reordering 4"]


# Simulator options: old simulator, new simulator with given number of skips
simulator_options = ['', "-new-sim -sim-skip 0", "-new-sim -sim-skip 1", "-new-sim -sim-skip 3", "-new-sim -sim-skip 5","-new-sim -sim-skip 10"]
# simulator_options = ['']

def reordering_toString(s):
    if s == "-reordering 0":
        return "WINDOW2"
    elif s == "-reordering 1":
        return "WINDOW2_CONV"
    elif s == "-reordering 2":
        return "WINDOW3"
    elif s == "-reordering 3":
        return "WINDOW3_CONV"
    elif s == "-reordering 4":
        return "WINDOW4"
    else: 
        return "disabled"

def simulator_toString(s):
    if s == "-new-sim":
        return "New Simulator"
    else: 
        return "Classic Simulator"

# Parses the output of an execution of probNv
def parse_output(filename, ro, so, lines):
    simulator = ""
    skips = '0'
    if so != "":
        skips = so.split(' ')[2] 
        simulator = so.split(' ')[0]
    stats = {'benchmark':filename, 'reordering':(reordering_toString(ro)), 'sim':simulator_toString(simulator), 'skips':skips}
    for l in lines:
        ls = l.split(':')
        if ls[0] == "Number of calls to merge":
            stats.update({'merge_calls': float(ls[1])})
        elif ls[0] == "Number of transfers":
            stats.update({'transfer_calls': float(ls[1])})
        elif ls[0] == "Transfer time":
            stats.update({'transfer_time': float(ls[1])})
        elif ls[0] == "Merge time":
            stats.update({'merge_time': float(ls[1])})
        elif ls[0] == "Native simulation took":
            stats.update({'simulation_time': float(ls[1])})
        elif ls[0] == "Time to check assertions took":
            stats.update({'assertion_time': float(ls[1])})
        elif ls[0] == "Peak number of nodes":
            stats.update({'peak_nodes': float(ls[1])})
        elif ls[0] == "Time for garbage collection":
            stats.update({'gc_time': float(ls[1].split(' ')[1])})
        elif ls[0] == "Time for reordering":
            stats.update({'reordering_time': float(ls[1].split(' ')[1])})
        elif ls[0] == "Memory in use":
            stats.update({'cudd_memory': (float(ls[1])/1024)/1024 })
        else: None
    return stats

def print_output(filename, stats):
    with open(filename + '.csv', 'w', newline='') as csvfile:
        fieldnames = ['benchmark', 'reordering', 'sim', 'skips', 'merge_calls', 'transfer_calls', 'transfer_time', 'merge_time', 'simulation_time', 'assertion_time', 'peak_nodes', 'gc_time', 'reordering_time', 'cudd_memory']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames,restval='')

        writer.writeheader()
        for s in stats:
            writer.writerow(s)

def timeout_output(filename, ro, so):
    simulator = ""
    skips = '0'
    if so != "":
        skips = so.split(' ')[2] 
        simulator = so.split(' ')[0]
    return {'benchmark':filename, 'reordering':reordering_toString(ro), 'sim':simulator_toString(simulator), 'skips':skips, 'merge_calls':'0', 'transfer_calls':'0', 'transfer_time':'0', 'merge_time':'0', 'simulation_time':'0', 'assertion_time':'0', 'peak_nodes':'0', 'gc_time':'0', 'reordering_time':'0', 'cudd_memory':'0'}


def start_benchmark(folder, filename):
    sims = []
    for ro in reordering_options:
        for so in simulator_options:
            print('Executing ' + filename + ' for options: ' + ro + ' and ' + so)
            options = [o.split() for o in ['probNv', ro, so, folder + filename + '.nv'] if o != '' ]
            args = [item for sublist in options for item in sublist]
            benchProcess = subprocess.Popen(args,stdout=subprocess.PIPE,universal_newlines=True)
            try:
                wait_timeout(benchProcess, 3600) # do not set timeout to a too low value, it takes a few seconds to compile and install
                benchStats = parse_output(filename, ro, so, iter(benchProcess.stdout.readline,''))
                sims.append(benchStats)
            except TimeoutError:
                sims.append(timeout_output(filename, ro, so))
                os.kill(benchProcess.pid, signal.SIGKILL)
    print_output(filename, sims)


#start_benchmark(sys.argv[1], sys.argv[2])

start_benchmark("examples/BICS/","bics_nodeFaults")
start_benchmark("examples/BICS/","bics_nodeFaults_bfs")
start_benchmark("examples/BICS/","bics_linkFaults")
start_benchmark("examples/BICS/","bics_linkFaults_bfs")

start_benchmark("examples/USCarrierOSPF/","USCarrierOSPF_nodeFaults")
start_benchmark("examples/USCarrierOSPF/","USCarrierOSPF_nodeFaults_bfs")
start_benchmark("examples/USCarrierOSPF/","USCarrierOSPF_linkFaults")
start_benchmark("examples/USCarrierOSPF/","USCarrierOSPF_linkFaults_bfs")

start_benchmark("examples/Fat6/","fat6_nodeFaults")
start_benchmark("examples/Fat6/","fat6_nodeFaults_bfs")
start_benchmark("examples/Fat6/","fat6_nodeFaults_fat")
start_benchmark("examples/Fat6/","fat6_linkFaults")
start_benchmark("examples/Fat6/","fat6_linkFaults_bfs")

start_benchmark("examples/Fat8/","fat8_nodeFaults")
start_benchmark("examples/Fat8/","fat8_nodeFaults_bfs")
start_benchmark("examples/Fat8/","fat8_nodeFaults_fat")
start_benchmark("examples/Fat8/","fat8_linkFaults")
start_benchmark("examples/Fat8/","fat8_linkFaults_bfs")

start_benchmark("examples/sp8/","sp8_nodeFaults")
start_benchmark("examples/sp8/","sp8_nodeFaults_bfs")
start_benchmark("examples/sp8/","sp8_nodeFaults_fat")
start_benchmark("examples/sp8/","sp8_linkFaults")
start_benchmark("examples/sp8/","sp8_linkFaults_bfs")

start_benchmark("examples/sp12/","sp12_nodeFaults")
start_benchmark("examples/sp12/","sp12_nodeFaults_bfs")
start_benchmark("examples/sp12/","sp12_nodeFaults_fat")
start_benchmark("examples/sp12/","sp12_linkFaults")
start_benchmark("examples/sp12/","sp12_linkFaults_bfs")