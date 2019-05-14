import Diagnostic
import Source
import Utils

class BoogieIntOverflow {
  private let monoLocation: String
  private let boogieLocation: String
  private var boogieAst: BTopLevelProgram
  private var arithmeticChecks = Set<SourceLocation>()

  init (boogie: BTopLevelProgram, monoLocation: String, boogieLocation: String) {
    self.monoLocation = monoLocation
    self.boogieLocation = boogieLocation
    self.boogieAst = boogie
  }

  func diagnose() -> [Diagnostic] {
    // Put assert in front of each expression, to check that is within bounds

    let globalVariables: [BVariableDeclaration] = self.boogieAst.declarations.compactMap({
                                                                   switch $0 {
                                                                   case .variableDeclaration(let vd):
                                                                     return vd
                                                                   default:
                                                                     return nil
                                                                   }
                                                                 })
    let (boogieSource, boogieMapping)
      = BTopLevelProgram(declarations: self.boogieAst.declarations.map({ checkDeclaration($0, globalVariables: globalVariables) }))
        .render()

    let boogieErrors = Boogie.verifyBoogie(boogie: boogieSource,
                                           monoLocation: self.monoLocation,
                                           boogieLocation: self.boogieLocation,
                                           printVerificationOutput: false)
    return resolveBoogieErrors(errors: boogieErrors, mapping: boogieMapping)
  }

  private func checkDeclaration(_ declaration: BTopLevelDeclaration, globalVariables: [BVariableDeclaration]) -> BTopLevelDeclaration {
    switch declaration {
    case .procedureDeclaration(let bProcedureDeclaration):
      return .procedureDeclaration(checkProcedureDeclaration(bProcedureDeclaration, globalVariables: globalVariables))
    default: return declaration
    }
  }

  private func checkProcedureDeclaration(_ bProcedureDeclaration: BProcedureDeclaration,
                                         globalVariables: [BVariableDeclaration]) -> BProcedureDeclaration {
    let env: [String: BType] = Dictionary(uniqueKeysWithValues: globalVariables.map({ ($0.name, $0.type) })
                               + bProcedureDeclaration.variables.map({ ($0.name, $0.type) })
                               + bProcedureDeclaration.parameters.map({ ($0.name, $0.type) }))
    let checkedStatements: [BStatement] = bProcedureDeclaration.statements.flatMap {
      checkStatement($0, env: env)
     }

    var postConditions = bProcedureDeclaration.postConditions
    return BProcedureDeclaration(name: bProcedureDeclaration.name,
                                 returnType: bProcedureDeclaration.returnType,
                                 returnName: bProcedureDeclaration.returnName,
                                 parameters: bProcedureDeclaration.parameters,
                                 preConditions: bProcedureDeclaration.preConditions,
                                 postConditions: postConditions,
                                 modifies: bProcedureDeclaration.modifies,
                                 statements: checkedStatements,
                                 variables: bProcedureDeclaration.variables,
                                 ti: bProcedureDeclaration.ti)
  }

  private func checkStatement(_ statement: BStatement,
                              env: [String: BType]) -> [BStatement] {
    switch statement {
    case .assignment(_, let rhs, let ti):
      return checkExpression(rhs, env: env, ti: ti) + [statement]
    case .callProcedure(let callProcedure):
      let checkExpressions = callProcedure.arguments.flatMap {
        checkExpression($0, env: env, ti: callProcedure.ti)
      }
      return checkExpressions + [statement]
    case .ifStatement(let bIfStatement):
      return checkExpression(bIfStatement.condition, env: env, ti: bIfStatement.ti) + [statement]
    case .whileStatement(let bWhileStatement):
      return checkExpression(bWhileStatement.condition, env: env, ti: bWhileStatement.ti) + [statement]
    case .assertStatement(let bAssertStatement):
      return checkExpression(bAssertStatement.expression, env: env, ti: bAssertStatement.ti) + [statement]
    default: break
    }
    return [statement]
  }

  private func checkExpression(_ expression: BExpression,
                               env: [String: BType],
                               ti: TranslationInformation) -> [BStatement] {
    var checkStatements = [BStatement]()

    switch expression {
    case .equivalent(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .implies(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .or(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .and(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .equals(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .lessThan(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .lessThanOrEqual(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .greaterThan(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .greaterThanOrEqual(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .concat(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .add(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .subtract(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .multiply(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .divide(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .modulo(let lhs, let rhs):
      checkStatements += (checkExpression(lhs, env: env, ti: ti) + checkExpression(rhs, env: env, ti: ti))
    case .not(let expression):
      checkStatements += checkExpression(expression, env: env, ti: ti)
    case .negate(let expression):
      checkStatements += checkExpression(expression, env: env, ti: ti)
    case .mapRead(let map, let key):
      checkStatements += (checkExpression(map, env: env, ti: ti) + checkExpression(key, env: env, ti: ti))

    //case .functionApplication(let functionName, let arguments):
    //case .boolean(let bool):
    //case .integer(let int):
    //case .real(let b, let f):
    //case .identifier(let string):
    //case .old(let expression):
    //case .nop:
    //case .quantified(let quantifier, let parameterDeclaration, let expression):
    default: break
    }

    if case .int = type(of: expression, env: env),
       ti.isUserDirectCause {
      let checkOverflow = BExpression.and(.lessThanOrEqual(expression, .integer(Utils.INT_MAX)),
                                          .greaterThanOrEqual(expression, .integer(Utils.INT_MIN)))
      checkStatements.append(.assertStatement(BAssertStatement(expression: checkOverflow, ti: ti)))
      self.arithmeticChecks.insert(ti.sourceLocation)
    }
    return checkStatements
  }

  private func resolveBoogieErrors(errors: [BoogieError], mapping: [Int: TranslationInformation]) -> [Diagnostic] {
    // The asserts which have overflows, will throw errors
    var overflowingLocations = Set<SourceLocation>()

    for error in errors {
      switch error {
      case .assertionFailure(let lineNumber):
        guard let ti = mapping[lineNumber] else {
          print(mapping)
          print("Couldn't find translation information for assertion on line \(lineNumber) in unreachable code")
          fatalError()
        }

        if arithmeticChecks.contains(ti.sourceLocation) {
          overflowingLocations.insert(ti.sourceLocation)
        }

      default:
        // Other failures may happen, but we're not interested in those.
        break
      }
    }

    var diagnostics = [Diagnostic]()
    for location in overflowingLocations {
      diagnostics.append(Diagnostic(severity: .warning,
                                    sourceLocation: location,
                                    message: "This expression could overflow",
                                    notes: []))
    }

    return diagnostics
  }
}
