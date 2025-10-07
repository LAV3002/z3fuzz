import sys
import pathlib
import os
import shutil

import subprocess

def getFuzzerName(idx):
    suffix = str(idx)
    if len(suffix) == 1:
        suffix = "0" + suffix
    
    return "fuzzer" + suffix


def main() -> int:
    baseDir = pathlib.Path(os.getcwd())
    aflDir = baseDir / "AFLplusplus"
    z3Dir = baseDir / "z3"
    fuzzDir = baseDir / "fuzzdir"
    samplesDir = baseDir / "base"

    z3 = z3Dir / "build/z3"
    afl = aflDir / "afl-fuzz"

    if os.path.exists(fuzzDir):
        shutil.rmtree(fuzzDir)
    
    os.makedirs(fuzzDir)

    os.chdir(fuzzDir)

    envVariables = dict()
    envVariables["PYTHONPATH"] = str(baseDir)
    envVariables["AFL_PYTHON_MODULE"] = "mutator"
    envVariables["AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES"] = "1"
    envVariables["AFL_SKIP_CPUFREQ"] = "1"
    envVariables["AFL_CUSTOM_MUTATOR_ONLY"] = "1"

    fuzzArgs = [str(afl), "{}", "{}", "-m", "4096", "-t", "10000", "-i", str(samplesDir), '-o', 'sync_dir/', str(z3), "-smt2", "@@"]

    envPrefix = "env "
    for key in envVariables:
        envPrefix += key + "=" + envVariables[key] + " "

    runFuzzCmd = envPrefix + " ".join(fuzzArgs).format("-M", "fuzzer01")

    secondarys = []
    fuzzArgs[1] = "-S"

    env = dict(os.environ)
    env.update(envVariables)
    print(env)

    processNumber = 1

    if len(sys.argv) == 2:
        processNumber = int(sys.argv[1]) - 1

    for idx in range(processNumber):
        fuzzArgs[2] = getFuzzerName(idx + 2)
        secondarys.append(subprocess.Popen(fuzzArgs, env=env, stdout=subprocess.DEVNULL))

    os.system(runFuzzCmd)

    for p in secondarys:
        p.kill()
        print("kill " + str(p))

if __name__ == '__main__':
    sys.exit(main())
