struct BTopLevelProgram: CustomStringConvertible {
  let declarations: [BTopLevelDeclaration]

  var description: String {
    return declarations.reduce("", {x, y in "\(x)\n\n\(y)"})
  }
}

enum BTopLevelDeclaration: CustomStringConvertible {
  case functionDeclaration(BFunctionDeclaration)
  case axiomDeclaration(BAxiomDeclaration)
  case variableDeclaration(BVariableDeclaration)
  case typeDeclaration(BTypeDeclaration)
  case procedureDeclaration(BProcedureDeclaration)

  var description: String {
    switch self {
    case .functionDeclaration(let bFunctionDeclaration):
      return "\(bFunctionDeclaration)"
    case .axiomDeclaration(let bAxiomDeclaration):
      return "\(bAxiomDeclaration)"
    case .variableDeclaration(let bVariableDeclaration):
      return "\(bVariableDeclaration)"
    case .typeDeclaration(let bTypeDeclaration):
      return "\(bTypeDeclaration)"
    case .procedureDeclaration(let bProcedureDeclaration):
      return "\(bProcedureDeclaration)"
    }
  }
}

struct BFunctionDeclaration: CustomStringConvertible {
  let name: String
  let returnType: BType?
  let returnName: String?
  let parameters: [BParameterDeclaration]

  var description: String {
    let parameterString = parameters.map({(x) -> String in return x.description}).joined(separator: ", ")
    let returnComponent = returnType == nil ? " " : " returns (\(returnName!): \(returnType!))"
    return "function \(name)(\(parameterString))\(returnComponent));"
  }
}

struct BAxiomDeclaration: CustomStringConvertible {
  let proposition: BExpression

  var description: String {
    return "\(proposition)"
  }
}

struct BVariableDeclaration: CustomStringConvertible {
  let name: String
  let rawName: String
  let type: BType

  var description: String {
    return "var \(name): \(type);"
  }
}

struct BTypeDeclaration: CustomStringConvertible {
  let name: String

  var description: String {
    return "type \(name);"
  }
}

struct BProcedureDeclaration: CustomStringConvertible {
  let name: String
  let returnType: BType?
  let returnName: String?
  let parameters: [BParameterDeclaration]
  let preConditions: [BExpression]
  let postConditions: [BExpression]
  let modifies: [BModifiesDeclaration]
  let statements: [BStatement]
  let variables: [BVariableDeclaration]

  var description: String {
    let parameterString = parameters.map({(x) -> String in return x.description}).joined(separator: ", ")
    let statementsString = statements.reduce("", {x, y in "\(x)\n\(y)"})
    let preString = preConditions.reduce("", {x, y in "\(x)\nrequires(\(y));"})
    let postString = postConditions.reduce("", {x, y in "\(x)\nensures(\(y));"})
    let modifiesString = modifies.reduce("", {x, y in "\(x)\n\(y)"})
    let returnString = returnType == nil ? " " : " returns (\(returnName!): \(returnType!))"
    let variablesString = variables.map({(x) -> String in return x.description}).joined(separator: "\n")

    return """
    procedure \(name)(\(parameterString))\(returnString)
      // Pre-Conditions
      \(preString)
      // Modifies
      \(modifiesString)
      // Post-Conditions
      \(postString)
    {
    // Local variable declarations
    \(variablesString)

    // \(name)'s implementation
    \(statementsString)
    }
    """
  }
}

struct BModifiesDeclaration: CustomStringConvertible {
  // Name of global variable being modified
  let variable: String

  var description: String {
    return "modifies \(variable);"
  }
}

struct BParameterDeclaration: CustomStringConvertible {
  let name: String
  let rawName: String
  let type: BType

  var description: String {
    return "\(name): \(type)"
  }
}

enum BStatement: CustomStringConvertible {
  case expression(BExpression)
  case ifStatement(BIfStatement)
  case whileStatement(BWhileStatement)
  case assertStatement(BExpression)
  case assertMarker(Int)
  case assume(BExpression)
  case havoc(String)
  case assignment(BExpression, BExpression)
  case callProcedure([String], String, [BExpression])
  case callForallProcedure(String, [BExpression])
  case breakStatement
  case returnStatement

  var description: String {
    switch self {
    case .expression(let expression): return expression.description
    case .ifStatement(let ifStatement): return ifStatement.description
    case .whileStatement(let whileStatement): return whileStatement.description
    case .assertStatement(let assertion): return "assert (\(assertion));"
    case .assertMarker(let id): return "//#ASSERT# \(id)"
    case .assume(let assumption): return "assume (\(assumption));"
    case .havoc(let identifier): return "havoc \(identifier);"
    case .assignment(let lhs, let rhs): return "\(lhs) := \(rhs);"
    case .callProcedure(let returnedValues, let functionName, let arguments):
      let argumentComponent = arguments.map({(x) -> String in x.description}).joined(separator: ", ")
      var returnValuesComponent = ""
      if returnedValues.count > 0 {
        returnValuesComponent = "\(returnedValues.joined(separator: ", ")) := "
      }

      return "call \(returnValuesComponent) \(functionName)(\(argumentComponent));"
    case .callForallProcedure(let functionName, let arguments):
      let argumentComponent = arguments.map({(x) -> String in x.description}).joined(separator: ", ")

      return "call forall \(functionName) (\(argumentComponent));"
    case .breakStatement: return "break;"
    case .returnStatement: return "return;"
    }
  }
}

indirect enum BExpression: CustomStringConvertible {
  case equivalent(BExpression, BExpression)
  case implies(BExpression, BExpression)
  case or(BExpression, BExpression)
  case and(BExpression, BExpression)
  case equals(BExpression, BExpression)
  case lessThan(BExpression, BExpression)
  case greaterThan(BExpression, BExpression)
  case concat(BExpression, BExpression)
  case add(BExpression, BExpression)
  case subtract(BExpression, BExpression)
  case multiply(BExpression, BExpression)
  case divide(BExpression, BExpression)
  case modulo(BExpression, BExpression)
  case not(BExpression)
  case negate(BExpression)
  case mapRead(BExpression, BExpression)
  case boolean(Bool)
  case integer(Int)
  case real(Int, Int)
  case identifier(String)
  case old(BExpression)
  case quantifier(BQuantifier, [BParameterDeclaration], BExpression)
  case functionApplication(String, [BExpression])
  case nop

  var description: String {
    switch self {
    case .equivalent(let lhs, let rhs): return "(\(lhs) <==> \(rhs))"
    case .implies(let lhs, let rhs): return "(\(lhs) ==> \(rhs))"
    case .or(let lhs, let rhs): return "(\(lhs) || \(rhs))"
    case .and(let lhs, let rhs): return "(\(lhs) && \(rhs))"
    case .equals(let lhs, let rhs): return "(\(lhs) == \(rhs))"
    case .lessThan(let lhs, let rhs): return "(\(lhs) < \(rhs))"
    case .greaterThan(let lhs, let rhs): return "(\(lhs) > \(rhs))"
    case .concat(let lhs, let rhs): return "(\(lhs) ++ \(rhs))"
    case .add(let lhs, let rhs): return "(\(lhs) + \(rhs))"
    case .subtract(let lhs, let rhs): return "(\(lhs) - \(rhs))"
    case .multiply(let lhs, let rhs): return "(\(lhs) * \(rhs))"
    case .divide(let lhs, let rhs): return "(DIV(\(lhs), \(rhs)))"
    case .modulo(let lhs, let rhs): return "(MOD(\(lhs), \(rhs)))"
    case .not(let expression): return "(!\(expression))"
    case .negate(let expression): return "(-\(expression))"
    case .mapRead(let map, let key): return "\(map)[\(key)]"
    case .boolean(let bool): return "\(bool)"
    case .integer(let int): return "\(int)"
    case .real(let b, let f): return "\(b).\(f)"
    case .identifier(let string): return string
    case .old(let expression): return "old(\(expression))"
    case .nop: return "// nop"
    case .quantifier(let quantifier, let parameterDeclaration, let expression):
      let parameterDeclarationComponent
        = parameterDeclaration.map({(x) -> String in x.description}).joined(separator: ", ")
      return "(\(quantifier) \(parameterDeclarationComponent) :: \(expression))"
    case .functionApplication(let functionName, let arguments):
      let argumentsComponent = arguments.map({(x) -> String in x.description}).joined(separator: ", ")
      return "\(functionName)(\(argumentsComponent))"
    }
  }
}

enum BQuantifier {
  case forall
  case exists

  var description: String {
    switch self {
    case .forall:
      return "forall"
    case .exists:
      return "exists"
    }
  }
}

struct BIfStatement: CustomStringConvertible {
  let condition: BExpression
  let trueCase: [BStatement]
  let falseCase: [BStatement]

  var description: String {
    let trueComponent = trueCase.map({(x) -> String in x.description}).joined(separator: "\n")
    let falseComponent = falseCase.map({(x) -> String in x.description}).joined(separator: "\n")
    return """
    if (\(condition)) {
      \(trueComponent)
    } else {
      \(falseComponent)
    }
    """
  }
}

struct BWhileStatement: CustomStringConvertible {
  let condition: BExpression
  let body: [BStatement]
  let invariants: [BExpression]

  var description: String {
    let invariantComponent = invariants.map({(x) -> String in "invariant (\(x.description));"}).joined(separator: "\n")
    let bodyComponent = body.map({(x) -> String in x.description}).joined(separator: "\n")
    return """
    while(\(condition))
    // Loop invariants
    \(invariantComponent)
    {
      \(bodyComponent)
    }
    """
  }
}

indirect enum BType: CustomStringConvertible {
  case int
  case real
  case boolean
  case userDefined(String)
  case map(BType, BType)

  var description: String {
    switch self {
    case .int: return "int"
    case .real: return "real"
    case .boolean: return "bool"
    case .userDefined(let type): return type
    case .map(let type1, let type2): return "[\(type1)]\(type2)" //TODO: Wrong format, needs to be [int][int]int .., not [[int]int]int
    }
  }
}