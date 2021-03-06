//
//  MovePreprocessor+Expressions.swift
//  MoveGen
//
//

import AST
import Lexer
import Foundation
import Diagnostic

/// A prepocessing step to update the program's AST before code generation.
extension MovePreprocessor {
  public func process(expression: Expression, passContext: ASTPassContext) -> ASTPassResult<Expression> {
    var expression = expression
    let environment = passContext.environment!
    var updatedContext = passContext

    if case .binaryExpression(let binaryExpression) = expression {
      if case .dot = binaryExpression.opToken,
         case .identifier(let lhsId) = binaryExpression.lhs,
         case .identifier(let rhsId) = binaryExpression.rhs,
         environment.isEnumDeclared(lhsId.name),
         let matchingProperty = environment.propertyDeclarations(in: lhsId.name)
             .filter({ $0.identifier.identifierToken.kind == rhsId.identifierToken.kind }).first,
         matchingProperty.type!.rawType != .errorType {
        expression = matchingProperty.value!
      }

      if case .equal = binaryExpression.opToken,
         case .variableDeclaration(let variableDeclaration) = binaryExpression.lhs {
        expression = variableDeclaration.assignment(to: binaryExpression.rhs)
        updatedContext.functionDeclarationContext?.innerDeclarations += [variableDeclaration]
        updatedContext.specialDeclarationContext?.innerDeclarations += [variableDeclaration]
        updatedContext.functionDeclarationContext?.declaration.scopeContext?.localVariables += [variableDeclaration]
        updatedContext.specialDeclarationContext?.declaration.scopeContext.localVariables += [variableDeclaration]
        updatedContext.scopeContext?.localVariables += [variableDeclaration]
      }
    }

    return ASTPassResult(element: expression, diagnostics: [], passContext: updatedContext)
  }

  func expandProperties(_ expression: Expression,
                        passContext: inout ASTPassContext,
                        borrowLocal: Bool = false) -> Expression {
    switch expression {
    case .identifier(let identifier):
      guard let scopeContext = passContext.scopeContext else { break }
      if let type = scopeContext.type(for: identifier.name),
         !type.isInout {
        // Handle `x.y` when x is not a reference
        return preAssign(expression, passContext: &passContext, borrowLocal: borrowLocal, isReference: false)
      } else if identifier.enclosingType != nil {
        // Handle `x.y` when x is implicitly self.x
        return preAssign(expression, passContext: &passContext, borrowLocal: borrowLocal)
      }
    case .binaryExpression(var binary):
      if binary.opToken == .dot {
        binary.lhs = expandProperties(binary.lhs, passContext: &passContext, borrowLocal: borrowLocal)
        return preAssign(.binaryExpression(binary), passContext: &passContext, borrowLocal: borrowLocal)
      } else {
        binary.lhs = expandProperties(binary.lhs, passContext: &passContext, borrowLocal: borrowLocal)
        binary.rhs = expandProperties(binary.rhs, passContext: &passContext, borrowLocal: borrowLocal)
        return preAssign(.binaryExpression(binary), passContext: &passContext, borrowLocal: borrowLocal)
      }
    default: break
    }
    return expression
  }

  public func process(binaryExpression: BinaryExpression,
                      passContext: ASTPassContext) -> ASTPassResult<BinaryExpression> {
    var passContext = passContext
    var binaryExpression = binaryExpression

    if let op = binaryExpression.opToken.operatorAssignmentOperator {
      let sourceLocation = binaryExpression.op.sourceLocation
      let token = Token(kind: .punctuation(op), sourceLocation: sourceLocation)
      binaryExpression.op = Token(kind: .punctuation(.equal), sourceLocation: sourceLocation)
      binaryExpression.rhs = .binaryExpression(BinaryExpression(lhs: binaryExpression.lhs,
                                                                op: token,
                                                                rhs: binaryExpression.rhs))
    } else if case .dot = binaryExpression.opToken {
      let trail = passContext.functionCallReceiverTrail ?? []
      passContext.functionCallReceiverTrail = trail + [binaryExpression.lhs]

      switch binaryExpression.lhs {
      case .identifier:
        if case .functionCall = binaryExpression.rhs {} else {
          binaryExpression.lhs = expandProperties(binaryExpression.lhs, passContext: &passContext)
        }
      case .binaryExpression(let binary):
        if binary.opToken == .dot {
          // Handle w.x...y.z
          binaryExpression.lhs = expandProperties(binaryExpression.lhs, passContext: &passContext)
        }
      default: break
      }
    }

    return ASTPassResult(element: binaryExpression,
                         diagnostics: [],
                         passContext: passContext)
  }

  func constructExpression<Expressions: Sequence & RandomAccessCollection>(from expressions: Expressions) -> Expression
      where Expressions.Element == Expression {
    guard expressions.count > 1 else { return expressions.first! }
    let head = expressions.first!
    let tail = expressions.dropFirst()

    let op = Token(kind: .punctuation(.dot), sourceLocation: head.sourceLocation)
    return .binaryExpression(BinaryExpression(lhs: head, op: op, rhs: constructExpression(from: tail)))
  }

  public func process(externalCall: ExternalCall, passContext: ASTPassContext) -> ASTPassResult<ExternalCall> {
    guard let environment = passContext.environment,
          let enclosingType = passContext.enclosingTypeIdentifier?.name,
          let scopeContext = passContext.scopeContext else {
      return ASTPassResult(element: externalCall, diagnostics: [
            Diagnostic(severity: .error,
                       sourceLocation: externalCall.sourceLocation,
                       message: "Insufficient environment information to deduce external call trait name")
      ], passContext: passContext)
    }
    // Update trait name for external calls
    var externalCall = externalCall
    let receiver = externalCall.functionCall.lhs
    let receiverType = environment.type(of: receiver, enclosingType: enclosingType, scopeContext: scopeContext)
    externalCall.externalTraitName = receiverType.name
    return ASTPassResult(element: externalCall, diagnostics: [], passContext: passContext)
  }

  public func process(functionCall: FunctionCall, passContext: ASTPassContext) -> ASTPassResult<FunctionCall> {
    var functionCall = functionCall
    let environment = passContext.environment!
    var receiverTrail = passContext.functionCallReceiverTrail ?? []
    let enclosingType = passContext.enclosingTypeIdentifier!.name
    //let typeStates = passContext.contractBehaviorDeclarationContext?.typeStates ?? []
    let callerProtections = passContext.contractBehaviorDeclarationContext?.callerProtections ?? []
    let isGlobalFunctionCall = self.isGlobalFunctionCall(functionCall, in: passContext)

    let scopeContext = passContext.scopeContext!
    var passContext = passContext

    guard !Environment.isRuntimeFunctionCall(functionCall) else {
      // Don't further process runtime functions
      return ASTPassResult(element: functionCall, diagnostics: [], passContext: passContext)
    }

    if receiverTrail.isEmpty {
      receiverTrail = [.`self`(Token(kind: .`self`, sourceLocation: functionCall.sourceLocation))]
    }

    functionCall.mangledIdentifier = mangledFunctionName(for: functionCall, in: passContext)

    if !environment.isInitializerCall(functionCall) && !environment.isTraitDeclared(functionCall.identifier.name) {
      // Get the result type of the call.
      let declarationEnclosingType: RawTypeIdentifier
      if isGlobalFunctionCall {
        declarationEnclosingType = Environment.globalFunctionStructName
      } else {
        declarationEnclosingType = passContext.environment!.type(of: receiverTrail.last!,
                                                                 enclosingType: enclosingType,
                                                                 callerProtections: callerProtections,
                                                                 scopeContext: scopeContext).name
      }

      // If it returns a dynamic type, pass the receiver as the first parameter.
      let environment = passContext.environment!
      if environment.isStructDeclared(declarationEnclosingType)
        || environment.isContractDeclared(declarationEnclosingType)
        || environment.isExternalTraitDeclared(declarationEnclosingType) {
        if !isGlobalFunctionCall {
          var receiver = constructExpression(from: receiverTrail)
          let type: RawType

          if receiver.enclosingType != nil {
            receiver = expandProperties(receiver, passContext: &passContext)
          } else if case .binaryExpression = receiver {
            receiver = expandProperties(receiver, passContext: &passContext)
          }

          switch receiver {
          case .identifier(let identifier):
            type = scopeContext.type(for: identifier.name)
              ?? environment.type(of: receiver,
                                  enclosingType: passContext.enclosingTypeIdentifier!.name,
                                  scopeContext: scopeContext)
          default:
            type = environment.type(of: receiver,
                                    enclosingType: passContext.enclosingTypeIdentifier!.name,
                                    scopeContext: scopeContext)
          }

          if !type.isInout {
            let inoutExpression = InoutExpression(ampersandToken: Token(kind: .punctuation(.ampersand),
                                                                        sourceLocation: receiver.sourceLocation),
                                                  expression: receiver)
            receiver = .inoutExpression(inoutExpression)
          }

          functionCall.arguments.insert(FunctionArgument(receiver), at: 0)
        }
      }
    }

    guard case .failure(let candidates) =
    environment.matchEventCall(functionCall,
                               enclosingType: enclosingType,
                               scopeContext: passContext.scopeContext ?? ScopeContext()),
          candidates.isEmpty else {
      return ASTPassResult(element: functionCall, diagnostics: [], passContext: passContext)
    }

    passContext = passContext.withUpdates { $0.functionCallReceiverTrail = [] }
    return ASTPassResult(element: functionCall, diagnostics: [], passContext: passContext)
  }

  func mangledFunctionName(for functionCall: FunctionCall, in passContext: ASTPassContext) -> String? {
    // Don't mangle runtime and external functions
    guard !Environment.isRuntimeFunctionCall(functionCall),
          !passContext.isExternalFunctionCall else {
      return functionCall.identifier.name
    }

    let environment = passContext.environment!

    let enclosingType: String = functionCall.identifier.enclosingType ?? passContext.enclosingTypeIdentifier!.name

    // Don't mangle event calls
    if case .matchedEvent =
    environment.matchEventCall(functionCall,
                               enclosingType: enclosingType,
                               scopeContext: passContext.scopeContext ?? ScopeContext()) {
      return functionCall.identifier.name
    }

    let typeStates = passContext.contractBehaviorDeclarationContext?.typeStates ?? []
    let callerProtections = passContext.contractBehaviorDeclarationContext?.callerProtections ?? []
    let matchResult = environment.matchFunctionCall(functionCall,
                                                    enclosingType: enclosingType,
                                                    typeStates: typeStates,
                                                    callerProtections: callerProtections,
                                                    scopeContext: passContext.scopeContext!)

    switch matchResult {
    case .matchedFunction(let functionInformation):
      let declaration = functionInformation.declaration
      let parameterTypes = declaration.signature.parameters.rawTypes

      return Mangler.mangleFunctionName(declaration.identifier.name,
                                        parameterTypes: parameterTypes,
                                        enclosingType: enclosingType)
    case .matchedFunctionWithoutCaller(let candidates):
      guard candidates.count == 1 else {
        fatalError("Unable to find unique declaration of \(functionCall)")
      }
      guard case .functionInformation(let candidate) = candidates.first! else {
        fatalError("Non-function CallableInformation where function expected")
      }
      let declaration = candidate.declaration
      let parameterTypes = declaration.signature.parameters.rawTypes
      return Mangler.mangleFunctionName(declaration.identifier.name,
                                        parameterTypes: parameterTypes,
                                        enclosingType: enclosingType)
    case .matchedInitializer(let initializerInformation):
      let declaration = initializerInformation.declaration
      let parameterTypes = declaration.signature.parameters.rawTypes
      return Mangler.mangleInitializerName(functionCall.identifier.name, parameterTypes: parameterTypes)
    case .matchedFallback:
      return Mangler.mangleInitializerName(functionCall.identifier.name, parameterTypes: [])
    case .matchedGlobalFunction(let functionInformation):
      let parameterTypes = functionInformation.declaration.signature.parameters.rawTypes
      return Mangler.mangleFunctionName(functionCall.identifier.name,
                                        parameterTypes: parameterTypes,
                                        enclosingType: Environment.globalFunctionStructName)
    case .failure:
      return nil
    }
  }

  func isGlobalFunctionCall(_ functionCall: FunctionCall, in passContext: ASTPassContext) -> Bool {
    let enclosingType = passContext.enclosingTypeIdentifier!.name
    let typeStates = passContext.contractBehaviorDeclarationContext?.typeStates ?? []
    let callerProtections = passContext.contractBehaviorDeclarationContext?.callerProtections ?? []
    let scopeContext = passContext.scopeContext!
    let environment = passContext.environment!

    let match = environment.matchFunctionCall(functionCall,
                                              enclosingType: enclosingType,
                                              typeStates: typeStates,
                                              callerProtections: callerProtections,
                                              scopeContext: scopeContext)

    // Mangle global function
    if case .matchedGlobalFunction = match {
      return true
    }

    return false
  }

  public func process(functionArgument: FunctionArgument,
                      passContext: ASTPassContext) -> ASTPassResult<FunctionArgument> {
    var functionArgument = functionArgument
    var passContext = passContext

    var expression: Expression
    var borrowLocal = false
    if case .inoutExpression(let inOut) = functionArgument.expression {
      expression = inOut.expression
      if let environment = passContext.environment,
         let scopeContext = passContext.scopeContext,
         let enclosingType = passContext.enclosingTypeIdentifier?.name {
        let type = environment.type(
             of: expression,
             enclosingType: enclosingType,
             typeStates: passContext.contractBehaviorDeclarationContext?.typeStates ?? [],
             callerProtections: passContext.contractBehaviorDeclarationContext?.callerProtections ?? [],
             scopeContext: scopeContext
        )
        if !type.isCurrencyType && !type.isExternalResource(environment: environment) {
          borrowLocal = true
        }
      } else { // If we can't deduce the type, expect it to be an external type
        borrowLocal = true
      }
    } else {
      expression = functionArgument.expression
    }

    switch expression {
    case .identifier(let identifier):
      // Handle x where x is implicitly self.x
      if identifier.enclosingType != nil {
        expression = preAssign(expression, passContext: &passContext, borrowLocal: borrowLocal)
      }
    case .binaryExpression(let binary):
      // Handle x.y
      if binary.opToken == .dot {
        expression = expandProperties(expression, passContext: &passContext, borrowLocal: borrowLocal)
      }
    default:
      if case .inoutExpression = functionArgument.expression {
        expression = functionArgument.expression
      }
    }

    functionArgument.expression = expression
    return ASTPassResult(element: functionArgument, diagnostics: [], passContext: passContext)
  }
}
