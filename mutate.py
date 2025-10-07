import sys
import pathlib

import mutator

encoding = "utf-8"

def mutate(formula):
    mutatedFormula = bytearray(formula.encode(encoding))

    mutatedFormula = mutator.fuzz(mutatedFormula, None, 15000)
    mutatedFormula = mutatedFormula.decode(encoding)

    return mutatedFormula
    

def main() -> int:
    fileWithFormula = pathlib.Path(sys.argv[1])
    numberOfGeneratedFormulas = int(sys.argv[2])
    outDir = pathlib.Path(sys.argv[3])

    if not fileWithFormula.is_file():
        print("incorrect file")
        sys.exit(1)

    formula = ""

    with open(fileWithFormula, 'r') as file:
        formula = file.read()
    
    for idx in range(1, numberOfGeneratedFormulas + 1):
        formula = mutate(formula)

        with open(outDir / (str(idx) + ".smt"), 'w') as file:
            file.write(formula)

if __name__ == '__main__':
    sys.exit(main())