import random

from enum import Enum

encoding = "utf-8"

class NodeType(Enum):
    Op = 1
    Symbolic = 2
    Constant = 3

class DefsInfo:
    def __init__(self):
        self.funcsInfo = dict()
        self.symbolicNames = []

    def getFuncsInfo(self):
        return self.funcsInfo
    
    def getSymbolicNames(self):
        return self.symbolicNames

    def getArgNumber(self, funcName):
        for key in self.funcsInfo.keys():
            if funcName in self.funcsInfo[key]:
                return key
        raise Exception("Bad func name") 

staticNodeTypes = [NodeType.Constant, NodeType.Symbolic]

def getRandomConst():
    return "bv" + str(random.randint(0, (2 ** 64) - 1))

class Node:
    def __init__(self, type, op):
        self.type = type
        self.op = op
        self.args = []

    def setOp(self, op):
        self.op = op

    def setType(self, type):
        self.type = type

    def getOp(self):
        return self.op
    
    def getType(self):
        return self.type

    def addArg(self, node):
        self.args.append(node)

    def getArgs(self):
        return self.args
    
    def setArgs(self, args):
        self.args = args

    def mutate(self, defsInfo):
        mutationIdx = random.randint(1, 50)

        if mutationIdx == 1:
            if not self.getType() == NodeType.Op:
                return
            
            self.setOp(random.choice(defsInfo.getFuncsInfo()[len(self.getArgs())]))
        elif mutationIdx == 2:
            random.shuffle(self.getArgs())
        elif mutationIdx == 3:
            if self.getType() == NodeType.Op:
                for arg in self.getArgs():
                    if arg.getType() == NodeType.Op:
                        return

            newType = random.choice(staticNodeTypes)

            self.setType(newType)
            self.setArgs([])
            
            if newType == NodeType.Symbolic:
                self.setOp(random.choice(defsInfo.getSymbolicNames()))
            
            if newType == NodeType.Constant:
                self.setOp(getRandomConst())
        elif mutationIdx == 4:
            if self.getType() in staticNodeTypes:
                newOp = random.choice(defsInfo.getFuncsInfo()[2])
                newType = NodeType.Op

                newArgs = [Node(NodeType.Symbolic, random.choice(defsInfo.getSymbolicNames())),
                            Node(NodeType.Constant, getRandomConst())]
                
                self.setOp(newOp)
                self.setType(newType)
                self.setArgs(newArgs)
        elif mutationIdx == 5:
            if not self.getType() == NodeType.Op:
                return
            
            if len(self.getArgs()) == 1:
                self.setOp(random.choice(defsInfo.getFuncsInfo()[2]))
                self.addArg(self.getArgs()[0])
            elif len(self.getArgs()) == 2:
                self.setOp(random.choice(defsInfo.getFuncsInfo()[1]))
                self.setArgs([self.getArgs()[1]])
            else:
                return
        elif mutationIdx == 6:
            if not self.getType() == NodeType.Constant:
                return
            
            self.setOp(getRandomConst())
        else:
            return

    def serialize(self, out, defsInfo):
        self.mutate(defsInfo)

        if self.getType() == NodeType.Symbolic:
            return self.getOp()

        idx = len(out)
        name = "T" + str(idx)
        out.append("")

        definition = "(define-fun "
        definition += name
        definition += " () (_ BitVec 64) ( "

        if self.getType() == NodeType.Op:
            definition += self.getOp()

            for node in self.getArgs():
                definition += " " + node.serialize(out, defsInfo)

        if self.getType() == NodeType.Constant:
            definition += "_ " + self.getOp() + " 64"

        definition += " ))"

        out[idx] = definition

        return name
    

class Component(Enum):
    Func = 1
    Symbols = 2
    Body = 3
    Epilog = 4
    Undef = 5

def getComponentType(name):
    for type in Component:
        if name == type.name.lower():
            return type
    return Component.Undef

def getComponentLabel(componentType):
    return "; " + componentType.name.lower()

def init(_):
    pass

def deinit():
    pass

defaultFormula = bytearray("(check-sat)".encode(encoding))

def fuzz(buf, _, max_size):
    formula = buf.decode("utf-8").strip()

    lines = list(map(str.strip, formula.split('\n')))

    funcs = []
    symbolics = []
    body = []
    epilog = []

    funcArgCount = 0
    defsInfo = DefsInfo()

    currentComp = Component.Undef

    for line in lines:
        if len(line) == 0:
            continue

        tokens = list(line.split(' '))
        if len(tokens) >= 2 and getComponentType(tokens[1]) != Component.Undef:
            currentComp = getComponentType(tokens[1])

            if currentComp == Component.Func:
                funcArgCount = int(tokens[2])
                defsInfo.getFuncsInfo()[funcArgCount] = []
                funcs.append(line)

            continue

        if currentComp == Component.Func:
            funcs.append(line)
            defsInfo.getFuncsInfo()[funcArgCount].append(tokens[1])
        elif currentComp == Component.Symbols:
            symbolics.append(line)
            defsInfo.getSymbolicNames().append(tokens[1])
        elif currentComp == Component.Body:
            body.append(line)
        elif currentComp == Component.Epilog:
            epilog.append(line)
        else:
            continue

    evalGraph = dict()

    for variableName in defsInfo.getSymbolicNames():
        evalGraph[variableName] = Node(NodeType.Symbolic, variableName)

    root = None

    for definition in body:
        tokens = list(definition.split(' '))
        
        if tokens[0] == ';':
            continue

        name = tokens[1]
        op = tokens[7]

        node = None
        if op == '_':
            node = Node(NodeType.Constant, tokens[8])
        else:
            node = Node(NodeType.Op, op)

            args = tokens[8:8 + defsInfo.getArgNumber(op)]

            for arg in args:
                try:
                    node.addArg(evalGraph[arg])
                except KeyError:
                    print(lines)
                    print(definition)
                    print(symbolics)
                    print(defsInfo.getSymbolicNames())

        evalGraph[name] = node
        root = node

    out = []

    root.serialize(out, defsInfo)

    out.reverse()

    newFormula = funcs + [getComponentLabel(Component.Symbols)] + symbolics + \
          [getComponentLabel(Component.Body)] + out + [getComponentLabel(Component.Epilog)] + epilog
    newFormula = "\n".join(newFormula) + "\n"
    newFormula = bytearray(newFormula.encode(encoding))

    if len(newFormula) > max_size:
        return defaultFormula

    return newFormula
