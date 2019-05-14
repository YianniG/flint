import AST
import Source
import Lexer
import Foundation
import Utils

extension BoogieTranslator {
  func getCurrentFunction() -> FunctionDeclaration {
    if let behaviourDeclarationMember = currentBehaviourMember {
      switch behaviourDeclarationMember {
      case .functionDeclaration(let functionDeclaration):
        return functionDeclaration
      case .specialDeclaration(let specialDeclaration):
        return specialDeclaration.asFunctionDeclaration
      default:
        print("Error getting current function - not in a function: \(behaviourDeclarationMember.description)")
      }
    }
    print("Error getting current function - not in a current behaviour declaration")
    fatalError()
  }

  func getCurrentFunctionName() -> String? {
    if let behaviourDeclarationMember = currentBehaviourMember {
      return normaliser.getFunctionName(function: behaviourDeclarationMember, tld: getCurrentTLDName())
    }
    return nil
  }

  func addCurrentFunctionVariableDeclaration(_ vDeclaration: VariableDeclaration) {
    let name = translateIdentifierName(vDeclaration.identifier.name)
    let type = convertType(vDeclaration.type)
    // Declared local expressions don't have assigned expressions
    assert(vDeclaration.assignedExpression == nil)

    addCurrentFunctionVariableDeclaration(BVariableDeclaration(name: name,
                                                               rawName: vDeclaration.identifier.name,
                                                               type: type))
  }

  func generateStructInstanceVariableName() -> String {
    if let functionName = getCurrentFunctionName() {
      let instance = generateRandomIdentifier(prefix: "struct_instance_\(functionName)_")
      return instance
    }
    print("Cannot generate struct instance variable name, not currently in a function")
    fatalError()
  }

   func getFunctionParameters(name: String) -> [BParameterDeclaration] {
    if functionParameters[name] == nil {
      functionParameters[name] = []
    }
    return functionParameters[name]!
  }

   func setFunctionParameters(name: String, parameters: [BParameterDeclaration]) {
    functionParameters[name] = parameters
  }

   func getFunctionVariableDeclarations(name: String) -> Set<BVariableDeclaration> {
    if functionVariableDeclarations[name] == nil {
      functionVariableDeclarations[name] = Set<BVariableDeclaration>()
    }
    return functionVariableDeclarations[name]!
  }

   func setFunctionVariableDeclarations(name: String, declarations: Set<BVariableDeclaration>) {
    functionVariableDeclarations[name] = declarations
  }

   func addCurrentFunctionVariableDeclaration(_ bvDeclaration: BVariableDeclaration) {
    if let functionName = getCurrentFunctionName() {
      var variableDeclarations = getFunctionVariableDeclarations(name: functionName)
      variableDeclarations.insert(bvDeclaration)
      setFunctionVariableDeclarations(name: functionName, declarations: variableDeclarations)
    } else {
      print("Error cannot add variable declaration to function: \(bvDeclaration), not currently translating a function")
      fatalError()
    }
  }

   func generateFunctionReturnVariable() -> String {
    if let functionName = getCurrentFunctionName() {
      let returnVariable = generateRandomIdentifier(prefix: "result_variable_\(functionName)_")
      functionReturnVariableName[functionName] = returnVariable
      return returnVariable
    }
    print("Cannot generate function return variable, not currently in a function")
    fatalError()
  }

  func getFunctionReturnVariable() -> String {
    if let functionName = getCurrentFunctionName() {
      if let returnVariable = functionReturnVariableName[functionName] {
        return returnVariable
      }
      print("Could not find return variables for function \(functionName)")
      fatalError()
    }
    print("Could not find return variable not currently in a function")
    fatalError()
  }

   func getFunctionTypes(_ functionCall: FunctionCall,
                         enclosingType: RawTypeIdentifier?) -> (RawType, [RawType], Bool) {
    let currentType = enclosingType == nil ? getCurrentTLDName() : enclosingType!
    if let scopeContext = getCurrentScopeContext() {
      let callerProtections = getCurrentContractBehaviorDeclaration()?.callerProtections ?? []
      let typeStates = getCurrentContractBehaviorDeclaration()?.states ?? []
      let matchedCall = environment.matchFunctionCall(functionCall,
                                                      enclosingType: currentType,
                                                      typeStates: typeStates,
                                                      callerProtections: callerProtections,
                                                      scopeContext: scopeContext)
      var returnType: RawType
      var parameterTypes: [RawType]
      var isInit: Bool = false
      switch matchedCall {
      case .matchedFunction(let functionInformation):
        returnType = functionInformation.resultType
        parameterTypes = functionInformation.parameterTypes

      case .matchedGlobalFunction(let functionInformation):
        returnType = functionInformation.resultType
        parameterTypes = functionInformation.parameterTypes

      case .matchedFunctionWithoutCaller(let callableInformations):
        //TODO: No idea what this means
        print("Matched function without caller?")
        print(callableInformations)
        fatalError()

      case .matchedInitializer(let specialInformation):
        // Initialisers do not return values -> although struct inits do = ints
        // TODO: Assume only for struct initialisers. Need to implement for contract initialisers/fallback functions?

        // This only works for struct initialisers.
        returnType = .basicType(.int)
        parameterTypes = specialInformation.parameterTypes
        isInit = true

      case .matchedFallback(let specialInformation):
        //TODO: Handle fallback functions
        print("Handle fallback calls")
        print(specialInformation)
        fatalError()

      case .failure(let candidates):
        print("function - could not find function for call: \(functionCall)")
        print(currentType)
        print(candidates)
        fatalError()
      }

      return (returnType, parameterTypes, isInit)
    }
    print("Cannot get scopeContext from current function")
    fatalError()
  }

   func handleFunctionCall(_ functionCall: FunctionCall,
                           structInstance: BExpression? = nil,
                           owningType: String? = nil) -> (BExpression, [BStatement], [BStatement]) {
    let rawFunctionName = functionCall.identifier.name
    var argumentsExpressions = [BExpression]()
    var argumentsStatements = [BStatement]()
    var argumentPostStmts = [BStatement]()
    guard let currentFunctionName = getCurrentFunctionName() else {
      print("Unableto get current function name - while processing function call")
      fatalError()
    }

    // Process triggers
    let context = Context(environment: environment,
                          enclosingType: getCurrentTLDName(),
                          scopeContext: getCurrentScopeContext() ?? ScopeContext())
    let (triggerPreStmts, triggerPostStmts) = triggers.lookup(functionCall, context)

    for arg in functionCall.arguments {
      let (expr, stmts, postStmts) = process(arg.expression)
      argumentsExpressions.append(expr)
      //TODO: Type of array/dict -> add those here
      //TODO if type array/dict return shadow variables - size_0, 1, 2..  + keys
      argumentsStatements += stmts
      argumentPostStmts += postStmts
    }

    switch rawFunctionName {
    // Special case to handle assert functions
    case "assert":
      // assert that assert function call always has one argument
      assert (argumentsExpressions.count == 1)
      argumentsStatements.append(.assertStatement(BAssertStatement(expression: argumentsExpressions[0],
                                                                   ti: TranslationInformation(sourceLocation: functionCall.sourceLocation))))
      return (.nop, argumentsStatements + triggerPreStmts, argumentPostStmts + triggerPostStmts)

    // Handle fatal error case
    case "fatalError":
      argumentsStatements.append(.assume(.boolean(false), TranslationInformation(sourceLocation: functionCall.sourceLocation)))
      return (.nop, argumentsStatements + triggerPreStmts, argumentPostStmts + triggerPostStmts)

    case "send":
      // send calls should have 2 arguments:
      // send(account, &w)
      assert (argumentsExpressions.count == 2)

      let procedureName = "send"
      // Call Boogie send function
      let functionCall = BStatement.callProcedure(BCallProcedure(returnedValues: [],
                                                                 procedureName: procedureName,
                                                                 arguments: argumentsExpressions,
                                                                 ti: TranslationInformation(sourceLocation: functionCall.sourceLocation)))
      // Add procedure call to callGraph
      addProcedureCall(currentFunctionName, procedureName)
      return (.nop, triggerPreStmts + [functionCall], argumentPostStmts + triggerPostStmts)
    default:
      // Check if a trait 'initialiser' is being called
      if environment.isTraitDeclared(rawFunctionName) {
        // Is being called, so return dummy value - ignore the init, doesn't do anything
        return (.integer(0), [], [])
      }
    }

    // TODO: Assert that contract invariant holds
    // TODO: Need to link the failing assert to the invariant =>
    //  error msg: Can't call function, the contract invariant does not hold at this point
    //argumentsStatements += (tldInvariants[getCurrentTLDName()] ?? []).map({ .assertStatement($0) })

    let (returnType, parameterTypes, isInit) = getFunctionTypes(functionCall, enclosingType: owningType)
    let functionName: String

    if isInit {
      // When calling struct constructors, need to identify this special
      // function call and set the owning type to the Struct
      functionName = normaliser.translateGlobalIdentifierName("init" + normaliser.flattenTypes(types: parameterTypes),
                                                              tld: rawFunctionName)
    } else {
      functionName = normaliser.translateGlobalIdentifierName(rawFunctionName + normaliser.flattenTypes(types: parameterTypes),
                                                              tld: owningType ?? getCurrentTLDName())
    }

    if let instance = structInstance, !isInit {
      // instance to pass as first argument
      argumentsExpressions.insert(instance, at: 0)
    }

    if returnType != RawType.basicType(.void) {
      // Function returns a value
      let returnValueVariable = generateRandomIdentifier(prefix: "v_") // Variable to hold return value
      let returnValue = BExpression.identifier(returnValueVariable)
      let functionCall = BStatement.callProcedure(BCallProcedure(returnedValues: [returnValueVariable],
                                                                 procedureName: functionName,
                                                                 arguments: argumentsExpressions,
                                                                 ti: TranslationInformation(sourceLocation: functionCall.sourceLocation)))
      addCurrentFunctionVariableDeclaration(BVariableDeclaration(name: returnValueVariable,
                                                                 rawName: returnValueVariable,
                                                                 type: convertType(returnType)))
      argumentsStatements.append(functionCall)
      // Add procedure call to callGraph
      addProcedureCall(currentFunctionName, functionName)
      return (returnValue, argumentsStatements + triggerPreStmts, triggerPostStmts)
    } else {
      // Function doesn't return a value
      // Can assume can't be called as part of a nested expression,
      // has return type Void
      argumentsStatements.append(.callProcedure(BCallProcedure(returnedValues: [],
                                                               procedureName: functionName,
                                                               arguments: argumentsExpressions,
                                                               ti: TranslationInformation(sourceLocation: functionCall.sourceLocation))))
      // Add procedure call to callGraph
      addProcedureCall(currentFunctionName, functionName)
      return (.nop, argumentsStatements + triggerPreStmts, argumentPostStmts + triggerPostStmts)
    }
  }

  private func getIterableTypeDepth(type: RawType, depth: Int = 0) -> Int {
    switch type {
    case .arrayType(let type): return getIterableTypeDepth(type: type, depth: depth+1)
    case .dictionaryType(_, let valueType): return getIterableTypeDepth(type: valueType, depth: depth+1)
    case .fixedSizeArrayType(let type, _): return getIterableTypeDepth(type: type, depth: depth+1)
    default:
      return depth
    }
  }

   func process(_ functionDeclaration: FunctionDeclaration,
                isStructInit: Bool = false,
                isContractInit: Bool = false,
                callerProtections: [CallerProtection] = [],
                callerBinding: Identifier? = nil,
                structInvariants: [BIRInvariant] = [],
                typeStates: [TypeState] = []
                ) -> BIRTopLevelDeclaration {
    let currentFunctionName = getCurrentFunctionName()!
    let body = functionDeclaration.body
    let parameters = functionDeclaration.signature.parameters
    var signature = functionDeclaration.signature
    var returnName = signature.resultType == nil ? nil : generateFunctionReturnVariable()
    var returnType = signature.resultType == nil ? nil : convertType(signature.resultType!)
    let oldCtx = setCurrentScopeContext(functionDeclaration.scopeContext)

    let callers = callerProtections.filter({ !$0.isAny }).map({ $0.identifier })

    // Process caller capabilities
    // Need the caller preStatements to handle the case when a function is called
    let (callerPreConds, callerPreStatements) = processCallerCapabilities(callers, callerBinding)

    // Process type states
    let typeStatePreConds = processTypeStates(typeStates)

    // Process triggers
    let context = Context(environment: environment,
                          enclosingType: getCurrentTLDName(),
                          scopeContext: getCurrentScopeContext() ?? ScopeContext())
    let (triggerPreStmts, triggerPostStmts) = triggers.lookup(functionDeclaration, context)

    var functionPostAmble = [BStatement]()
    var functionPreAmble = [BStatement]()

    var preConditions = [BPreCondition]()
    var postConditions = [BPostCondition]()
    var bParameters = [BParameterDeclaration]()
    for param in parameters {
      let (bParam, initStatements, functionPreconditions) = processParameter(param)
      functionPreAmble += initStatements
      bParameters += bParam
      preConditions += functionPreconditions
    }

    // If returns int, the int must not overflow
    if returnType != nil,
       case .int = returnType!,
       let returnName = returnName {
      let checkOverflow = BExpression.and(.lessThanOrEqual(.identifier(returnName), .integer(Utils.INT_MAX)),
                                          .greaterThanOrEqual(.identifier(returnName), .integer(Utils.INT_MIN)))
      postConditions.append(BPostCondition(expression: checkOverflow,
                                           ti: TranslationInformation(sourceLocation: signature.resultType!.sourceLocation)))
    }


    let ti = TranslationInformation(sourceLocation: functionDeclaration.sourceLocation)

    if let cTld = currentTLD {
      switch cTld {
      case .structDeclaration:
        self.structInstanceVariableName = generateStructInstanceVariableName()
        if isStructInit {
          returnType = .int
          returnName = generateFunctionReturnVariable()

          let nextInstance = normaliser.generateStructInstanceVariable(structName: getCurrentTLDName())

          addCurrentFunctionVariableDeclaration(BVariableDeclaration(name: self.structInstanceVariableName!,
                                                                     rawName: self.structInstanceVariableName!,
                                                                     type: .int))
          let reserveNextStructInstance: [BStatement] = [
            .assignment(.identifier(self.structInstanceVariableName!),
                        .identifier(nextInstance),
                        ti),
            .assignment(.identifier(nextInstance),
                        .add(.identifier(nextInstance), .integer(1)),
                        ti)
          ]
          // Include nextInstance in modifies
          var nextInstanceId = Identifier(name: "nextInstance", //TODO: Work out how to get raw name
                                          sourceLocation: functionDeclaration.sourceLocation)
          nextInstanceId.enclosingType = getCurrentTLDName()
          signature.mutates.append(nextInstanceId)

          let returnAllocatedStructInstance: [BStatement] = [
            .assignment(.identifier(returnName!),
                        .identifier(self.structInstanceVariableName!),
                        ti)
            //.returnStatement
          ]

          let structInitPost: BExpression =
            .equals(.identifier(nextInstance), .add(.old(.identifier(nextInstance)), .integer(1)))

          postConditions.append(BPostCondition(expression: structInitPost,
                                              ti: ti))

          functionPreAmble += reserveNextStructInstance
          functionPostAmble += returnAllocatedStructInstance
        } else {
          bParameters.insert(BParameterDeclaration(name: self.structInstanceVariableName!,
                                                   rawName: self.structInstanceVariableName!,
                                                   type: .int), at: 0)
          // Make sure that the struct passed in, 'exists'
          preConditions.append(BPreCondition(expression: .lessThan(.identifier(self.structInstanceVariableName!),
                                                                   .identifier(normaliser.generateStructInstanceVariable(structName: getCurrentTLDName()))), ti: ti))
        }
      default: break
      }
    }
    setFunctionParameters(name: currentFunctionName, parameters: bParameters)

    // TODO: Handle += operators and function calls in pre conditions
    for condition in signature.prePostConditions {
      switch condition {
      case .pre(let e):
        preConditions.append(BPreCondition(expression: process(e).0,
                                           ti: TranslationInformation(sourceLocation: e.sourceLocation)))
      case .post(let e):
        postConditions.append(BPostCondition(expression: process(e).0,
                                             ti: TranslationInformation(sourceLocation: e.sourceLocation)))
      }
    }

    if isContractInit || isStructInit {
      var assignments = [BStatement]()

      for (name, expression) in (tldConstructorInitialisations[getCurrentTLDName()] ?? []) {
        let (e, pre, post) = process(expression)
        assignments += pre
        if isStructInit {
          assignments.append(.assignment(.mapRead(.identifier(name),
                                                  .identifier(self.structInstanceVariableName!)),
                                         e, TranslationInformation(sourceLocation: expression.sourceLocation)))
        } else {
          assignments.append(.assignment(.identifier(name), e, TranslationInformation(sourceLocation: expression.sourceLocation)))
        }
        assignments += post
      }
      functionPostAmble += assignments
    }

    // Procedure must hold contract invariants
    let contractInvariants = (tldInvariants[getCurrentTLDName()] ?? [])

    let bStatements = functionIterableSizeAssumptions
                    + functionPreAmble
                    + body.flatMap({x in process(x)})
                    + functionPostAmble

    var modifies = [String]()
    // Get mutates from function clause, or from environment if the function was made from a trait
    for mutates in functionDeclaration.mutates + (self.traitFunctionMutates[currentFunctionName] ?? []) {
      let enclosingType = mutates.enclosingType ?? getCurrentTLDName()
      let variableType = environment.type(of: mutates.name, enclosingType: enclosingType)
      switch variableType {
      case .arrayType, .dictionaryType:
        let depthMax = getIterableTypeDepth(type: variableType)
        for depth in 0..<depthMax {
          modifies.append(normaliser.getShadowArraySizePrefix(depth: depth) + normaliser.translateGlobalIdentifierName(mutates.name, tld: enclosingType))
          if case .dictionaryType = variableType {
            modifies.append(normaliser.getShadowDictionaryKeysPrefix(depth: depth) + normaliser.translateGlobalIdentifierName(mutates.name, tld: enclosingType))
          }
        }
      default:
        break
      }

      modifies.append(normaliser.translateGlobalIdentifierName(mutates.name, tld: enclosingType))
    }

    if isContractInit {
      modifies += contractGlobalVariables[getCurrentTLDName()] ?? []
    }

    if isStructInit {
      modifies += structGlobalVariables[getCurrentTLDName()] ?? []
    }

    let modifiesClauses = Set<BIRModifiesDeclaration>(modifies.map({
       BIRModifiesDeclaration(variable: $0, userDefined: true)
    }))
    // Get the global shadow variables, the function modifies
    // (but can't be directly expressed by the user) - ie. nextInstance_struct
    .union((functionModifiesShadow[currentFunctionName] ?? []).map({
       BIRModifiesDeclaration(variable: $0, userDefined: false)
     }))

    // About to exit function, reset struct instance variable
    self.structInstanceVariableName = nil
    _ = setCurrentScopeContext(oldCtx)

    return .procedureDeclaration(BIRProcedureDeclaration(
      name: currentFunctionName,
      returnType: returnType,
      returnName: returnName,
      parameters: bParameters,
      preConditions: callerPreConds + typeStatePreConds + preConditions, //Inits should establish
      postConditions: postConditions,
      structInvariants: structInvariants,
      contractInvariants: contractInvariants,
      globalInvariants: self.globalInvariants,
      modifies: modifiesClauses,
      statements: callerPreStatements + triggerPreStmts + bStatements + triggerPostStmts,
      variables: getFunctionVariableDeclarations(name: currentFunctionName),
      ti: ti,
      isHolisticProcedure: false,
      isStructInit: isStructInit,
      isContractInit: isContractInit
    ))
  }
}
