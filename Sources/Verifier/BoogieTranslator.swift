import AST
import Source
import Lexer
import Foundation

class BoogieTranslator {
  let topLevelModule: TopLevelModule
  let environment: Environment
  // Variables declared in each function
  var functionVariableDeclarations = [String: [BVariableDeclaration]]()
  // Procedure paramters
  var functionParameters = [String: [BParameterDeclaration]]()
  // Name of procedure return variable
  var functionReturnVariableName = [String: String]()
  // Global variables modified in each procedure
  var functionGlobalModifications = [String: [String]]()
  // Empty Map Properties, for each type
  var emptyMapProperties = [BType: (BFunctionDeclaration, BAxiomDeclaration, String)]()

  // Source location that each proof oligation corresponds to
  var flintProofObligationSourceLocation = [Int: SourceLocation]()

  // Current behaviour member - function / special / signature declaration ..
  var currentBehaviourMember: ContractBehaviorMember?
  // Current top level declaration - contract behaviour / trait / struct ..
  var currentTLD: TopLevelDeclaration?

  // Name of state variable for each contract
  var contractStateVariable = [String: String]()
  // Mapping of each state name, for each contract state variable
  var contractStateVariableStates = [String: [String: Int]]()
  // Statements to be placed in the constructor of the contract
  var contractConstructorInitialisations = [String: [BStatement]]()

  // Name of global variables in the contract
  var contractGlobalVariables = [String: [String]]()
  // List of invariants for each tld
  var tldInvariants = [String: [BProofObligation]]()

  // Struct function instance variable
  var structInstanceVariableName: String?

  public init(topLevelModule: TopLevelModule, environment: Environment) {
    self.topLevelModule = topLevelModule
    self.environment = environment
  }

  public func translate() -> (String, [Int: SourceLocation]) {
    /* for everything defined in TLM, generate Boogie representation */
    // Generate AST and print
    let boogieCode = "// Generated by flintc\n \(generateAST())"
    return (boogieCode, generateFlint2BoogieMapping(code: boogieCode))
  }

  func generateAST() -> BTopLevelProgram {
    var declarations = [BTopLevelDeclaration]()

    for case .contractDeclaration(let contractDeclaration) in topLevelModule.declarations {
      self.currentTLD = .contractDeclaration(contractDeclaration)
      declarations += process(contractDeclaration)
      self.currentTLD = nil
    }

    for case .structDeclaration(let structDeclaration) in topLevelModule.declarations {
      self.currentTLD = .structDeclaration(structDeclaration)
      declarations += process(structDeclaration)
      self.currentTLD = nil
    }

    for case .enumDeclaration(let enumDeclaration) in topLevelModule.declarations {
      self.currentTLD = .enumDeclaration(enumDeclaration)
      declarations += process(enumDeclaration)
      self.currentTLD = nil
    }

    for case .traitDeclaration(let traitDeclaration) in topLevelModule.declarations {
      self.currentTLD = .traitDeclaration(traitDeclaration)
      declarations += process(traitDeclaration)
      self.currentTLD = nil
    }

    for case .contractBehaviorDeclaration(let contractBehaviorDeclaration) in topLevelModule.declarations {
      self.currentTLD = .contractBehaviorDeclaration(contractBehaviorDeclaration)
      declarations += process(contractBehaviorDeclaration)
      self.currentTLD = nil
    }

    let propertyDeclarations: [BTopLevelDeclaration]
      = emptyMapProperties.map({ arg in
                                     let (_, v) = arg
                                     let funcDec: BFunctionDeclaration = v.0
                                     let axDec: BAxiomDeclaration = v.1
                                     return [BTopLevelDeclaration.functionDeclaration(funcDec),
                                             BTopLevelDeclaration.axiomDeclaration(axDec)]
                                   }).reduce([], +)

    return BTopLevelProgram(declarations: propertyDeclarations + declarations)
  }

   func process(_ contractDeclaration: ContractDeclaration) -> [BTopLevelDeclaration] {
    var declarations = [BTopLevelDeclaration]()
    var contractGlobalVariables = [String]()

    for variableDeclaration in contractDeclaration.variableDeclarations {
      let name = translateGlobalIdentifierName(variableDeclaration.identifier.name)
      let type = convertType(variableDeclaration.type)

      // Some variables require shadow variables, eg dictionaries need an array of keys
      for bvariableDeclaration in generateVariables(variableDeclaration) {
        declarations.append(.variableDeclaration(bvariableDeclaration))
        contractGlobalVariables.append(bvariableDeclaration.name)
      }

      // Record assignment to put in constructor procedure
      let (assignedExpression, preStatements) = variableDeclaration.assignedExpression == nil
        ? (defaultValue(type), []) : process(variableDeclaration.assignedExpression!)
      if contractConstructorInitialisations[contractDeclaration.identifier.name] == nil {
        contractConstructorInitialisations[contractDeclaration.identifier.name] = []
      }
      contractConstructorInitialisations[contractDeclaration.identifier.name]! += preStatements
      contractConstructorInitialisations[contractDeclaration.identifier.name]!.append(
        .assignment(.identifier(name), assignedExpression)
      )
    }

    // TODO: Handle usage of += 1 and preStmts
    var invariantDeclarations = [BProofObligation]()
    for declaration in contractDeclaration.invariantDeclarations {
      //Invariants are turned into both pre and post conditions
      invariantDeclarations.append(BProofObligation(expression: process(declaration).0,
                                                    mark: declaration.sourceLocation.line,
                                                    obligationType: .preCondition))
      invariantDeclarations.append(BProofObligation(expression: process(declaration).0,
                                                    mark: declaration.sourceLocation.line,
                                                    obligationType: .postCondition))
      flintProofObligationSourceLocation[declaration.sourceLocation.line] = declaration.sourceLocation
    }
    tldInvariants[contractDeclaration.identifier.name] = invariantDeclarations

    let stateVariableName = generateStateVariable(contractDeclaration)
    contractStateVariable[contractDeclaration.identifier.name] = stateVariableName
    // Declare contract state variable
    declarations.append(.variableDeclaration(BVariableDeclaration(name: stateVariableName,
                                                                  rawName: stateVariableName,
                                                                  type: .int)))
    contractGlobalVariables.append(stateVariableName)

    contractStateVariableStates[contractDeclaration.identifier.name] = [String: Int]()
    for typeState in contractDeclaration.states {
      contractStateVariableStates[contractDeclaration.identifier.name]![typeState.name]
        = contractStateVariableStates[contractDeclaration.identifier.name]!.count
    }

    self.contractGlobalVariables[getCurrentTLDName()] = contractGlobalVariables

    return declarations
  }

  func process(_ enumDeclaration: EnumDeclaration) -> [BTopLevelDeclaration] {
    // TODO:
    return []
  }

  func process(_ traitDeclaration: TraitDeclaration) -> [BTopLevelDeclaration] {
    // TODO:
    return []
  }

   func process(_ structDeclaration: StructDeclaration) -> [BTopLevelDeclaration] {
    // Skip special global struct - too solidity low level - TODO: Is this necessary?
    if structDeclaration.identifier.name == "Flint$Global" { return [] }

    var declarations = [BTopLevelDeclaration]()

    for variableDeclaration in structDeclaration.variableDeclarations {
      let name = translateGlobalIdentifierName(variableDeclaration.identifier.name)
      let type = convertType(variableDeclaration.type)

      // TODO: Some variables require shadow variables, eg dictionaries need an array of keys
      declarations.append(.variableDeclaration(BVariableDeclaration(name: name,
                                                                    rawName: variableDeclaration.identifier.name,
                                                                    type: .map(.int, type))))

      /* TODO: Struct variable assignment
      // Record assignment to put in constructor procedure
      let (assignedExpression, preStatements) = variableDeclaration.assignedExpression == nil
        ? (defaultValue(type), []) : process(variableDeclaration.assignedExpression!)
      if contractConstructorInitialisations[contractDeclaration.identifier.name] == nil {
        contractConstructorInitialisations[contractDeclaration.identifier.name] = []
      }
      contractConstructorInitialisations[contractDeclaration.identifier.name]! += preStatements
      contractConstructorInitialisations[contractDeclaration.identifier.name]!.append(
        .assignment(.identifier(name), assignedExpression)
      )
      */
    }

    // Add nextInstance variable
    declarations.append(.variableDeclaration(BVariableDeclaration(name: getStructInstanceVariable(),
                                                                  rawName: getStructInstanceVariable(),
                                                                  type: .int)))

    var invariantDeclarations = [BProofObligation]()
    for declaration in structDeclaration.invariantDeclarations {
      //Invariants are turned into both pre and post conditions
      structInstanceVariableName = "i" // TODO: Check that i is unique

      let expr = process(declaration).0 // TODO: Handle usage of += 1 and preStmts
      let inv = BExpression.quantified(.forall, [BParameterDeclaration(name: structInstanceVariableName!,
                                                           rawName: structInstanceVariableName!,
                                                           type: .int)], expr)

      structInstanceVariableName = nil

      invariantDeclarations.append(BProofObligation(expression: inv,
                                                    mark: declaration.sourceLocation.line,
                                                    obligationType: .preCondition))
      invariantDeclarations.append(BProofObligation(expression: inv,
                                                    mark: declaration.sourceLocation.line,
                                                    obligationType: .postCondition))
      flintProofObligationSourceLocation[declaration.sourceLocation.line] = declaration.sourceLocation
    }
    tldInvariants[getCurrentTLDName()] = invariantDeclarations

    for functionDeclaration in structDeclaration.functionDeclarations {
      self.currentBehaviourMember = .functionDeclaration(functionDeclaration)
      declarations.append(process(functionDeclaration))
      self.currentBehaviourMember = nil
    }

    //TODO: Handle constructor declarations
    for specialDeclaration in structDeclaration.specialDeclarations {
      let initFunction = specialDeclaration.asFunctionDeclaration
      self.currentBehaviourMember = .functionDeclaration(initFunction)
      declarations.append(process(initFunction, isStructInit: true))
      self.currentBehaviourMember = nil
    }

    return declarations
  }

   func process(_ contractBehaviorDeclaration: ContractBehaviorDeclaration) -> [BTopLevelDeclaration] {
    // TODO: Use type states, to generate pre-conditions
    _ = contractBehaviorDeclaration.states
    // TODO: Use caller capabilities
    _ = contractBehaviorDeclaration.callerProtections
    var declarations = [BTopLevelDeclaration]()

    for member in contractBehaviorDeclaration.members {
      self.currentBehaviourMember = member
      switch member {
      case .specialDeclaration(let specialDeclaration):
        let currentFunctionName = getCurrentFunctionName()!
        let body = specialDeclaration.body
        let parameters = specialDeclaration.signature.parameters
        // TODO: let userPreConditions = specialDeclaration.signature.prePostConditions.map({ process($0).0 }) // TODO: +=1 etc
        let processedBody = body.flatMap({x in process(x)})

        let bParameters = parameters.map({x in process(x)})
        setFunctionParameters(name: currentFunctionName, parameters: bParameters)

        // Constructor has no pre-conditions
        // - and constructor must setup invariant
        let postConditions = (tldInvariants[getCurrentTLDName()] ?? [])
          .filter({$0.obligationType != .preCondition})

        // Constructor
        declarations.append(.procedureDeclaration(BProcedureDeclaration(
          name: currentFunctionName,
          returnType: nil,
          returnName: nil,
          parameters: bParameters,
          prePostConditions: postConditions, //+ userPreConditions,
          //TODO: Only specify actually modified variables
          modifies: contractGlobalVariables[getCurrentTLDName()]!.map({ BModifiesDeclaration(variable: $0) }),
          statements: ((specialDeclaration.isInit ? contractConstructorInitialisations[getCurrentTLDName()] ?? [] : [])
                       + processedBody),
          variables: getFunctionVariableDeclarations(name: currentFunctionName)
          )))

      case .functionDeclaration(let functionDeclaration):
        declarations.append(process(functionDeclaration))

      default:
        // TODO: Handle functionSignatureDeclaration case
        // TODO: Handle specialFunctionSignatureDeclaration case
        print("found declaration: \(member)")
      }
      self.currentBehaviourMember = nil
    }

    return declarations
  }

  func process(_ parameter: Parameter) -> BParameterDeclaration {
    let name = parameter.identifier.name
    return BParameterDeclaration(name: translateIdentifierName(name),
                                 rawName: name,
                                 type: convertType(parameter.type))
  }

  func process(_ token: Token) -> BExpression {
    switch token.kind {
    case .literal(let literal):
      return process(literal)
    default:
      print("Not implemented handling other literals")
      fatalError()
    }
  }

  func process(_ literal: Token.Kind.Literal) -> BExpression {
    switch literal {
    case .boolean(let booleanLiteral):
      return .boolean(booleanLiteral == Token.Kind.BooleanLiteral.`true`)

    case .decimal(let decimalLiteral):
      switch decimalLiteral {
      case .integer(let i):
        return .integer(i)
      case .real(let b, let f):
        return .real(b, f)
      }

    case .string:
      // TODO: Implement strings
      // Create const string for this literal -> const normalisedString: String;
      print("Not implemented translating strings")
      fatalError()
    case .address:
      // TODO: Implement addresses
      // Create const address -> for this literal -> const normalisedAddress: Address;
      print("Not implemented translating addresses")
      fatalError()
    }
  }

  func generateVariables(_ variableDeclaration: VariableDeclaration) -> [BVariableDeclaration] {
    // If currently in a function, then generate name with function in it
    // If in contractDeclaration, then generate name with only contract in it
    let name = getCurrentFunctionName() == nil ?
      translateGlobalIdentifierName(variableDeclaration.identifier.name)
      : translateIdentifierName(variableDeclaration.identifier.name)

    var declarations = [BVariableDeclaration]()
    let type = convertType(variableDeclaration.type)

    // TODO: Bounded array, then create array size variable
    switch type {
    case .map(let keyType, let valueType):
      declarations.append(BVariableDeclaration(name: "keys_\(name)",
                                               rawName: "keys_\(name)",
                                               type: .map(.int, keyType)))
      declarations.append(BVariableDeclaration(name: "values_\(name)",
                                               rawName: "values_\(name)",
                                               type: .map(.int, valueType)))
    default:
      break
    }

    declarations.append(BVariableDeclaration(name: name,
                                             rawName: variableDeclaration.identifier.name,
                                             type: type))
    return declarations
  }

  func getStateVariable() -> String {
    return contractStateVariable[getCurrentTLDName()]!
  }

  func getStateVariableValue(_ identifier: String) -> Int {
    return contractStateVariableStates[getCurrentTLDName()]![identifier]!
  }

  func generateStateVariable(_ contractDeclaration: ContractDeclaration) -> String {
    let contractName = contractDeclaration.identifier.name
    return "stateVariable_\(contractName)"
  }

  func randomIdentifier(`prefix`: String = "i") -> String {
    return `prefix` + randomString(length: 10) // 10 random characters feels random enough
  }

  func randomString(length: Int) -> String {
      let alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
      var s = ""
      for _ in 0..<length {
        let r = Int.random(in: 0..<alphabet.count)
        s += String(alphabet[alphabet.index(alphabet.startIndex, offsetBy: r)])
      }

    return s
  }

   func generateRandomIdentifier(prefix: String) -> String {
    if let functionName = getCurrentFunctionName() {
      let variableDeclarations = getFunctionVariableDeclarations(name: functionName)
      let returnIdentifier = randomIdentifier(prefix: prefix)

      for declaration in variableDeclarations
        where declaration.name == returnIdentifier {
        return generateRandomIdentifier(prefix: prefix)
      }
      return returnIdentifier
    }
    print("Could not generate function return value name, not currently in function")
    fatalError()
  }

  func getCurrentContractBehaviorDeclaration() -> ContractBehaviorDeclaration? {
    if let tld = currentTLD {
      switch tld {
      case .contractBehaviorDeclaration(let contractBehaviorDeclaration):
        return contractBehaviorDeclaration
      default:
        return nil
      }
    }
    print("Error cannot get current contract declaration - not in any TopLevelDeclaration")
    fatalError()
  }

  func getCurrentTLDName() -> String {
    if let tld = currentTLD {
      switch tld {
      case .contractDeclaration(let contractDeclaration):
        return  contractDeclaration.identifier.name

      case .contractBehaviorDeclaration(let contractBehaviorDeclaration):
        return contractBehaviorDeclaration.contractIdentifier.name
      case .structDeclaration(let structDeclaration):
        return structDeclaration.identifier.name

      default:
        break
      /*
        TODO: Implement
      case .enumDeclaration(let enumDeclaration):
      case .traitDeclaration(let traitDeclaration):
        */
      }
    }

    print("Error cannot get current contract name: not in a contract")
    fatalError()
  }

  func translateIdentifierName(_ name: String) -> String {
    if let functionName = getCurrentFunctionName() {
      // Function name already has contract scope (eg. funcA_ContractA
      return name + "_\(functionName)"
    }
    print("Error cannot translate identifier: \(name), not translating contract")
    fatalError()
  }

  func translateGlobalIdentifierName(_ name: String, tld owningTld: String? = nil) -> String {
    if let tld = owningTld {
      return name + "_\(tld)"
    }
    return name + "_\(getCurrentTLDName())"
  }

  func convertType(_ type: Type) -> BType {
    return convertType(type.rawType)
  }

  func convertType(_ type: RawType) -> BType {
    func convertBasicType(_ bType: RawType.BasicType) -> BType {
      switch bType {
      case .address: return .userDefined("Address")
      case .int: return .int
      case .bool: return .boolean
      default:
        print("not implemented conversion for basic type: \(type)")
        fatalError()
      }
    }

    func convertStdlibType(_ sType: RawType.StdlibType) -> BType {
      switch sType {
      case .wei:
        return .int
      }
    }

    switch type {
    case .basicType(let basicType):
      return convertBasicType(basicType)
    case .stdlibType(let stdlibType):
      return convertStdlibType(stdlibType)
    case .dictionaryType(let keyType, let valueType):
      return BType.map(convertType(keyType), convertType(valueType))
    case .arrayType(let type):
      return .map(.int, convertType(type))
    case .inoutType(let type):
      return convertType(type)
    case .userDefinedType:
      return .int
    default:
      print("not implemented conversion for type: \(type)")
      fatalError()
    }
  }

   func defaultValue(_ type: BType) -> BExpression {
    switch type {
    case .int: return .integer(0)
    case .real: return .real(0, 0)
    case .boolean: return .boolean(false) // TODO: Is this the default bool value?
    case .userDefined:
      print("Can't translate default value for user defined type yet")
      fatalError()
    case .map(let t1, let t2):
      if let properties = emptyMapProperties[type] {
        return .functionApplication(properties.2, [])
      }

      let t2Default = defaultValue(t2)
      let emptyMapPropertyName = "Map_\(type.nameSafe).Empty"
      let emptyMapPropertyFunction: BFunctionDeclaration =
      BFunctionDeclaration(name: emptyMapPropertyName,
                           returnType: type,
                           returnName: "result",
                           parameters: [])
      let emptyMapPropertyAxiom: BAxiomDeclaration = BAxiomDeclaration(proposition:
       .quantified(.forall,
                   [BParameterDeclaration(name: "i", rawName: "i", type: t1)],
                   .equals(.mapRead(.functionApplication(emptyMapPropertyName, []), .identifier("i")), t2Default))
      )

      emptyMapProperties[type] = (emptyMapPropertyFunction, emptyMapPropertyAxiom, emptyMapPropertyName)

      return .functionApplication(emptyMapPropertyName, [])
    }
  }

  func generateFlint2BoogieMapping(code: String) -> [Int: SourceLocation] {
    var mapping = [Int: SourceLocation]()

    let lines = code.trimmingCharacters(in: .whitespacesAndNewlines)
                               .components(separatedBy: "\n")
    var boogieLine = 1 // Boogie starts counting lines from 1
    for line in lines {
      // Pre increment because assert markers precede asserts and pre/post condits
      boogieLine += 1

      // Look for ASSERT markers
      let matches = line.groups(for: "// #MARKER# ([0-9]+)")
      if matches.count == 1 {
        // Extract line number
        mapping[boogieLine] = flintProofObligationSourceLocation[Int(matches[0][1])!]!
      }
    }
    return mapping
  }
}
