import sys
import pathlib
import os


def main() -> int:
    baseDir = pathlib.Path(os.getcwd())
    aflDir = baseDir / "AFLplusplus"
    z3Dir = baseDir / "z3"

    os.chdir(aflDir)

    aflBuildCmd = "make all"

    os.system(aflBuildCmd)

    aflCC = aflDir / "afl-gcc-fast"
    aflCXX = aflDir / "afl-g++-fast"

    os.chdir(z3Dir)
    
    z3ConfigureCmd = "env CC={} CXX={} cmake -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -S . -B ./build -G Ninja".format(aflCC, aflCXX)
    
    os.system(z3ConfigureCmd)

    z3BuildCmd = "cmake --build build -t all -j8"

    os.system(z3BuildCmd)

if __name__ == '__main__':
    sys.exit(main())
