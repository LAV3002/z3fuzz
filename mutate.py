import sys
import pathlib

import mutator

encoding = "utf-8"


def main() -> int:
    fileWithFormula = pathlib.Path(sys.argv[1])

    if not fileWithFormula.is_file():
        print("incorrect file")
        sys.exit(1)

    formula = ""

    with open(fileWithFormula, 'r') as file:
        formula = file.read()
    formula = bytearray(formula.encode(encoding))

    mutatedFormula = mutator.fuzz(formula, None, 10000)
    mutatedFormula = mutatedFormula.decode(encoding)

    print(mutatedFormula)

if __name__ == '__main__':
    sys.exit(main())