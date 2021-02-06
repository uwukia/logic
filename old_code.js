'use strict'

/**
 * @typedef Pathway
 * @property {boolean} hasFound - Whether the Pathway describes something that has been found or not
 * @property {Array} path - The path it took to reach something (will be empty if it hasn't been found).
 */

// should the json file include string representations?
const saveString = true

const logic = {
  argument: {
    assumption: {
      premise: {}
    },
    reasoning: {
      axiom: {},
      proof: {},
      subproof: {},
    },
    empty: {}
  },
  formula: {
    statement: {},
    wff: {},
    conclusion: {},
    unary: {
      negation: {},
      scope: {}
    },
    binary: {
      conditional: {},
      conjunction: {},
      disjunction: {},
      biconditional: {},
    },
    quantifier: {
      existential: {},
      universal: {}
    },
  },
  predicate: {},
  term: {
    constant: {},
    variable: {}
  }
}

const logictype = {
  argument: 'argument',
  arg: 'argument',
  premise: 'premise',
  axiom: 'axiom',
  assumption: 'assumption',
  proof: 'proof',
  subproof: 'subproof',
  reasoning: 'reasoning',
  reason: 'reasoning',
  conclusion: 'conclusion',
  formula: 'formula',
  binary: 'binary',
  bin: 'binary',
  conditional: 'conditional',
  con: 'conditional',
  biconditional: 'biconditional',
  bicon: 'bicontidional',
  conjunction: 'conjunction',
  and: 'conjunction',
  disjunction: 'disjunction',
  or: 'conjunction',
  negation: 'negation',
  not: 'negation',
  statement: 'statement',
  state: 'statement',
  predicate: 'predicate',
  pred: 'predicate',
  term: 'term',
  constant: 'constant',
  def: 'constant',
  variable: 'variable',
  var: 'variable',
  wff: 'wff',
  quantifier: 'quantifier',
  universal: 'universal',
  existence: 'existence',
  scope: 'scope',
  unary: 'unary',
  uni: 'unary',
  empty: 'empty'
}

// LOGIC FUNCTIONS

  /**
   * This section of the code will handle logical operations and objects.
   * 
   * Arguments are made up of arguments and formulas. Formulas are made up of of formulas until the axiomatic formulas, Predicates.
   * Predicates are made up of terms and terms can be represented with variables.
   * 
   * 
   */

  /**
   * @typedef Term
   * @property {string} type   - Either logictype.var or logictype.def
   * @property {string} symbol - The string representation of the term.
   * 
   * @typedef Predicate
   * @property {string} type    - = logictype.pred
   * @property {number} arity   - Integer greater or equal to zero.
   * @property {Array} visual   - Array of size (arity+1) storing the string representation of the given predicate.
   * 
   * @typedef Statement
   * @property {string} type         - = logictype.state
   * @property {Predicate} predicate - A valid predicate.
   * @property {Array} terms         - An array composed of terms and size (arity of Predicate).
   * @property {Array} variables     - A list of objects with each variable in terms and wether they're bound or not.
   * @property {string} [string]     - Its string representation.
   * 
   * @typedef WFF
   * @property {string} type         - = logictype.wff
   * @property {Array} [terms]       - An array composed of terms.
   * @property {Array} [variables]   - A list of objects with each variable in terms and wether they're bound or not.
   * @property {string} [string]     - Its string representation.
   * 
   * @typedef Unary
   * @property {string} type      - must be a key in logic.formula.unary
   * @property {Object} formula   - A well-formed-formula
   * @property {Array} visual     - A length-2 array with the string representation of the given unary type.
   * @property {Array} variables  - A list of dependent variables
   * 
   * @typedef Binary
   * @property {string} type      - must be a key in logic.formula.binary
   * @property {Array} formulas   - A length-2 array composed of formulas (wff, statement, binary, etc.).
   * @property {Array} visual     - A length-3 array with the string representation of the given binary type.
   * @property {Array} variables  - A list of dependent variables
   */

  /**
   * Checks for an object type and verifies if it is of type typeToVerify
   * 
   * It'll go through the object in logictype and check if the type in typeToVerify is equal or parent of logicalObject.type
   * @see logictype
   * 
   * @param {Object} logicalObject 
   * @param {string} typeToVerify 
   * 
   * @returns {boolean} whether the logical object is or isn't of type typeToVerify
   */
  function isType(logicalObject, typeToVerify) {
    let find_type = findType(logicalObject.type)
    if (!find_type.hasFound) throw 'LogicError: isType() expects a logical object.'
    else {
      // if we found a logical type, check if typeToVerify is itself or a parent type
      if (find_type.path.includes(typeToVerify)) return true
      else return false
    }
  }

  /**
   * This function converts any logical objects into readable strings.
   * 
   * If anyone has a suggestion of a better way to do this other than a ridiculous amount of else if's, I'd appreciate it.
   * 
   * @param {Object} logicalObject
   * 
   * @returns {string} the string representation of the given object.
   */
  function logicString(logicalObject) {
    if (typeof logicalObject.type === 'undefined') {
      throw 'LogicError: logicString() received an invalid or non-logical object.'
    } else if (isType(logicalObject, logictype.term)) {
      return logicalObject.symbol
    } else if (isType(logicalObject, logictype.state)) {
      let visual = logicalObject.predicate.visual
      let returnString
      logicalObject.terms.forEach((term, index) => {
        // the following line is confusing but essentially we want: visual[0] term[0] ... visual[n] term[n] visual[n+1]
        // that's why predicate.visual has 1 more entry than arity, to have an additional string to attach to the end
        returnString = returnString.concat(visual[index], logicString(term))
      })
      // finally, to wrap everything up, finish with the last visual bit of the predicate, and return it
      returnString = returnString.concat(visual[visual.length - 1])
      return returnString
    } else if (isType(logicalObject, logictype.wff)) {
      let returnString = logicalObject.symbol
      logicalObject.terms.forEach(term => returnString = returnString.concat(logicString(term)))
      return returnString
    } else if (isType(logicalObject, logictype.bin)) {
      let returnString = ''
      // returnString = visual[0] + formula[0] + visual[1] + formula[1] + visual[2]
      logicalObject.formulas.forEach((formula, index) => {
        returnString = returnString.concat(logicString(formula), logicalObject.visual[index])
      })
      returnString = returnString.concat(logicalObject.visual[2])
      return returnString
    } else if (isType(logicalObject, logictype.uni)) {
      let visual = logicalObject.visual
      let formula = logicalObject.formula
      let returnString = visual[0] + logicString(formula) + visual[1]
      return returnString
    } else if (isType(logicalObject, logictype.conclusion)) {
      return logicString(logicalObject.formula)
    } else {
      throw 'LogicError: Could not identify the logic object type: ' + logicalObject.type
    }
  }

  /**
   * Gets the information within two formulas check if they're equal.
   * @param {Object} firstFormula 
   * @param {Object} secondFormula 
   * 
   * @returns {boolean} whether they're equal or not.
   */
  function checkEqual(firstFormula, secondFormula) {
    // this method is quite cheat-y, however, it's code-efficient and should always work.
    let firstString = logicString(firstFormula)
    let secondString = logicString(secondFormula)
    return (firstString === secondString)
  }

  /**
   * Checks if the formula lookForFormula is one of the formulas inside listOfFormulas.
   * 
   * This function is similar to Array.includes(), as if we were doing listOfFormulas.includes(lookForFormula).
   * 
   * @param {Array} listOfFormulas 
   * @param {Object} lookForFormula 
   */
  function formulasInclude(listOfFormulas, lookForFormula) {
    // assume it doesn't include
    let includes = false

    for (let formula = 0; formula < listOfFormulas; formula++) {
      if (checkEqual(formula, lookForFormula)) {
        // yes it does, we found it!
        includes = true
        break
      }
    }

    return includes
  }

  // FORMULA FUNCTIONS

    /**
     * Creates a term that is represented by symbol.
     * 
     * Terms are the fundamental objects to build predicates and so any formulas in First Order Logic.
     * 
     * @param {string} symbol - The string representation of the term
     * @param {string} termType - Either logictype.var or logictype.def
     * 
     * @returns {Term} a term
     */
    function newTerm(symbol, termType) {
      if (typeof symbol === 'string') {
        if (termType === logictype.var || termType === logictype.def) {
          return {'type': termType, 'symbol': symbol}
        } else {
          if (typeof termType === 'string') {
            throw 'LogicError: Terms must be of type variable or constant. Received: ' + termType
          } else {
            throw 'LogicError: Term types must be strings. Received: ' + typeof termType
          }
        }
      } else {
        throw 'LogicError: Terms must be composed of strings. Received: ' + typeof symbol
      }
    }

    /**
     * Creates a predicate.
     * 
     * Predicates, when combined with terms, create logical statements, the foundational blocks of logic.
     * 
     * Visual example: (x=y) can be created like this: newPredicate(2, ['(', '=', ')'])
     * 
     * @param {number} arity        - The amount of terms the predicate will have
     * @param {Array|string} visual - The visual representation of the given predicate
     * 
     * @returns {Predicate} a predicate
     */
    function newPredicate(arity, visual) {
      if (typeof arity !== 'number') throw 'LogicError: Predicate arity must be a number. Received: ' + typeof arity
      if (arity !== Math.floor(Math.abs(arity))) throw 'LogicError: Predicate arity must be a non-negative whole number. Received: ' + typeof arity

      // convert string to array if needed
      if (typeof visual === 'string') visual = stringToArray(visual, arity + 1)

      if (!Array.isArray(visual)) throw 'LogicError: visual must be an Array or string. Received: ' + typeof visual

      if (visual.length !== arity + 1) throw 'LogicError: Expected visual to be an array of length' + arity+1 + '. Received: ' + visual.length

      return {'type': logictype.pred, 'arity': arity, 'visual': visual}
    }

    /**
     * Creates a statement based on a predicate and a list of terms.
     * 
     * The array terms must be only composed of terms and its size must match the predicate's arity.
     * Never call this function with manually written objects, see the functions below.
     * @see newTerm
     * @see newPredicate
     * 
     * @param {Predicate} predicate 
     * @param {Array} terms 
     * 
     * @returns {Statement}
     */
    function newStatement(predicate, terms) {
      if (!isType(predicate, logictype.pred)) throw 'LogicError: newStatement(pred, terms) pred expects a predicate.'
      if (!Array.isArray(terms)) throw 'LogicError: newStatement(pred, terms) terms expects an array. Received: ' + typeof terms

      let problematicIndexes = []
      let termsAreValid = true
      terms.forEach((term, index) => {
        if (!isType(term, logictype.term)) {
          if (termsAreValid) termsAreValid = false
          problematicIndexes.push(index)
        }
      })

      if (!termsAreValid) {
        problematicIndexes.forEach(termIndex => {
          console.error('Received an invalid term of type ' + terms[termIndex].type + ' in index ' + termIndex)
        })
        throw 'LogicError: newStatement(pred, terms) terms expects an array of valid terms.'
      }

      if (terms.length !== predicate.arity) throw 'LogicError: Expected ' + predicate.arity + 'terms. Received: ' + terms.length

      // from here, predicate is valid, terms are valid

      let variableList = []
      // I could do this when I first called terms.forEach but it would make the code bad looking for an unnecessary improvement in efficiency
      terms.forEach((term) => {
        if (isType(term, logictype.var)) variableList.push({isBound: false, variable: term})
      })

      let returnObj = {}
      returnObj['type'] = logictype.state
      returnObj[logictype.pred] = predicate
      returnObj['terms'] = terms
      returnObj['variables'] = variableList
      if (saveString) returnObj['string'] = logicString(returnObj)

      return returnObj
    }

    /**
     * Creates a representation of a formula, which is useful for stating theorems.
     * 
     * @todo this
     * 
     * @param {string} symbol - The string representation
     * @param {Array} [terms] - The terms the given formula should be depended on
     * 
     * @returns {WFF} a well-formed-formula
     */
    function newWFF(symbol, terms = []) {
      if (typeof symbol !== 'string') throw 'LogicError: newWFF() expects a symbol of type string to represent it. Received: ' + typeof symbol
      if (!Array.isArray(terms)) throw 'LogicError: newWFF() terms expects an array. Received: ' + typeof terms

      let problematicIndexes = []
      let termsAreValid = true
      terms.forEach((term, index) => {
        if (!isType(term, logictype.term)) {
          if (termsAreValid) termsAreValid = false
          problematicIndexes.push(index)
        }
      })

      if (!termsAreValid) {
        problematicIndexes.forEach(termIndex => {
          console.error('Received an invalid term of type ' + terms[termIndex].type + ' in index ' + termIndex)
        })
        throw 'LogicError: newStatement(pred, terms) terms expects an array of valid terms.'
      }

      // from here, symbol is valid, terms (if any) are valid

      let variableList = []
      // I could do this when I first called terms.forEach but it would make the code bad looking for an unnecessary improvement in efficiency
      terms.forEach((term) => {
        if (isType(term, logictype.var)) variableList.push({isBound: false, variable: term})
      })

      let returnObj = {}
      returnObj['type'] = logictype.wff
      returnObj['symbol'] = symbol
      returnObj['terms'] = terms
      returnObj['variables'] = variableList
      if (saveString) returnObj['string'] = logicString(returnObj)
      return returnObj
    }

    /**
     * Creates a negation based on a formula.
     * 
     * @param {Formula} formula 
     * 
     * @returns {Unary} !formula
     */
    function newNot(formula) {
      if (!isType(formula, logictype.formula)) throw 'LogicError: Negation expects a formula. Received: ' + formula.type

      let variables = formula.variables

      let returnObj = {}
      returnObj['type'] = logictype.not
      returnObj['formula'] = formula
      returnObj['variables'] = variables
      returnObj['visual'] = ['¬', '']
      if (saveString) returnObj['string'] = logicString(returnObj)
      return returnObj
    }

    /**
     * Creates a logical binary operation (like a conditional or a conjunction)
     * 
     * @param {string} binaryType - must be a key in logic.formula.binary
     * @param {Array} formulas    - A length-2 array composed of formulas (wff, statement, binary, etc.)
     * @param {Array} visual      - A length-3 array with the string representation of the given binary type.
     * 
     * @returns {Binary} a logical binary operation.
     */
    function newBinary(binaryType, formulas, visual) {
      if (!isType({type: binaryType}, logictype.bin)) throw 'LogicError: Expected a binary-operation type. Received: ' + binaryType

      if (!Array.isArray(formulas)) throw 'LogicError: Formulas must be within an array. Received: ' + typeof formulas
      else if (formulas.length !== 2) throw 'LogicError: Binary operations are composed of 2 formulas. Received: ' + formulas.length
      
      // I didn't use forEach because the loop may have to break
      for (let index = 0; index < 2; index++) {
        if (!isType(formulas[index], logictype.formula)) throw 'LogicError: Binary formulas are composed of type formula objects. Received ' + formulas[index].type
      }

      if (!Array.isArray(visual)) throw 'LogicError: Visuals must be within an array. Received: ' + typeof visual
      else if (visual.length !== 3) throw 'LogicError: Binary visuals are composed of 3 strings. Received: ' + visual.length
      
      // I didn't use forEach because the loop may have to break
      for (let index = 0; index < 3; index++) {
        if (typeof visual[index] !== 'string') throw 'LogicError: Visuals must be of type string. Received: ' + typeof visual[index]
      }

      // from here, all of the inputs are valid

      let variables = formulas[0].variables.concat(formulas[1].variables)

      let returnObj = {}
      returnObj['type'] = binaryType
      returnObj['formulas'] = formulas
      returnObj['visual'] = visual
      returnObj['variables'] = variables
      if (saveString) returnObj['string'] = logicString(returnObj)

      return returnObj
    }

    /**
     * Creates a conditional statement.
     * @see newBinary
     * 
     * @param {Array} formulas - A length-2 array composed of formulas
     * @returns {Binary} a conditional statement.
     */
    function newConditional(formulas) {
      return newBinary(logictype.con, formulas, ['(', '\implies', ')'])
    }

    /**
     * Converts a formula into a conclusion.
     * 
     * @param {Object} formula
     * 
     * @returns {Object} a conclusion 
     */
    function newConclusion(formula) {
      if (!isType(formula, logictype.formula)) throw 'LogicError: Expected a formula to be converted. Received: ' + formula.type

      return {'type': logictype.conclusion, 'formula': formula}
    }

  // ARGUMENT FUNCTIONS

    /**
     * @typedef Argument
     * @property {string} type
     * @property {Array} premise
     * @property {Argument} [assumption]
     * @property {Array} reasoning
     * @property {Object} conclusion
     */

    const emptyConclusion = newConclusion(newWFF(''))
    const emptyArgument = newArgument(logictype.empty, [], {type: logictype. assumption}, [], emptyConclusion)
    const emptyAssumption = {type: logictype.assumption, argument: emptyArgument}

    /**
     * Creates a new argument.
     * 
     * Arguments, in logic, are made up of premises (a set of arguments assumed to be true), lines of reasoning (arguments that can be concluded from previous lines),
     * and a conclusion, which is the conclusion from the last line of reasoning (unless it's a special type of argument, like an axiom).
     * 
     * Please don't call this function to create empty arguments. Use the const emptyArgument instead.
     * 
     * @param {string} argType 
     * @param {Array} argPremises 
     * @param {Array} argReasoning 
     * @param {Object} argConclusion
     * 
     * @returns {Object} an argument
     */
    function newArgument(argType, argPremises, argAssumption, argReasoning, argConclusion) {

      if (!isType({type: argType}, logictype.arg)) throw 'LogicError: Expected an argument. Received: ' + argType

      if (!validPremise(argType, argPremises)) throw 'LogicError: Argument premises are invalid.'

      if (!isType(argAssumption, logictype.assumption)) throw 'LogicError: Expected an assumption. Received: ' + argAssumption.type

      if (!validReasoning(argType, argPremises, argAssumption, argReasoning)) throw 'LogicError: Argument reasoning is invalid.'

      if (!validConclusion(argType, argReasoning, argConclusion)) throw 'LogicError: Argument conclusion is invalid.'

      // from here, the code knows all the inputs are valid

      let returnArg = {
        type: argType,
        premise: argPremises,
        assumption: argAssumption,
        reasoning: argReasoning,
        conclusion: argConclusion
      }

      return returnArg
    }

      /**
       * Verify an argument's premises based on its type.
       * 
       * @param {string} argType 
       * @param {Array} argPremises 
       * 
       * @returns {boolean} whether premises are valid or not.
       */
      function validPremise(argType, argPremises) {
        if (!Array.isArray(argPremises)) throw 'Premises should be within an array. Received: ' + typeof argPremises

        if (isType({type: argType}, logictype.assumption) && argPremises.length > 0) {
          console.error('LogicError: Assumptions must have no premises.')
          return false
        }

        let problematicPremises = {}
        argPremises.forEach(((premise, index) => {
          if (!isType(premise, logictype.premise)) {
            problematicPremises[index] = premise
          }
        }))

        if (problematicPremises.length > 0) {
          for (index in problematicIndexes) {
            console.error('LogicError: Expected a premise in index ' + index + '. Received ' + problematicIndexes[index].type)
          }
          return false
        }

        return true
      }

      /**
       * Verify an argument's line of reasoning.
       * 
       * @see verifyLineOfReasoning
       * 
       * @param {string} argType 
       * @param {Array} argPremises 
       * @param {Argument} argAssumption
       * @param {Array} argReasoning 
       * 
       * @returns {boolean} whether the reasoning is valid or not.
       */
      function validReasoning(argType, argPremises, argAssumption, argReasoning) {

        if (!Array.isArray(argReasoning)) throw 'Reasoning should be within an array. Received: ' + typeof argReasoning

        // axioms must have no reasoning, axioms are set to be true, so we can't reason around them
        // isType expects an object with property 'type'
        let dummyType = {type: argType}
        if (argReasoning.length > 0 && isType(dummyType, logictype.axiom)) {
          console.error('Axioms must have no reasoning.')
          return false
        }

        // this array will store all conclusions up to some point in the function
        let previousConclusions = []

        argPremises.forEach(premise => {
          previousConclusions.push(premise.conclusion)
        })

        // if the assumption isn't empty, add its conclusion to the list as well
        if (!isType(argAssumption, logictype.empty)) {
          previousConclusions.push(argAssumption.conclusion)
        }

        // assume reasoning is valid
        let reasoningIsValid = true

        // since we may have to stop the loop in case of an invalid line of reasoning, we use for instead of forEach
        for (let line = 0; line < argReasoning.length; line++) {
          reasoningIsValid = verifyLineOfReasoning(previousConclusions, argReasoning[line])
          if (!reasoningIsValid) {
            console.error('LogicError: The reasoning in line ' + line + 'is invalid.')
            break
          } else {
            // if the reasoning is valid, add its conclusion to the list of previous conclusions
            previousConclusions.push(argReasoning[line].conclusion)
          }
        }
        return reasoningIsValid
      }

        /**
         * Checks if the argument in lineOfReasoning is valid, based on previousConclusions.
         * 
         * If a line of reasoning has no premises, it must be an axiom. If it's not an axiom, its premises conclusions must come from previousConclusions.
         * 
         * @param {Array} previousConclusions 
         * @param {Argument} lineOfReasoning 
         * 
         * @returns {boolean} whether lineOfReasoning is valid or not.
         */
        function verifyLineOfReasoning(previousConclusions, lineOfReasoning) {
          if (isType(lineOfReasoning, logictype.axiom)) {
            return true
          } else {
            
            if (lineOfReasoning.premise.length === 0) {
              console.error('LogicError: Non-axiomatic arguments expect at least one premise.')
              return false
            } else {

              let premises = lineOfReasoning.premise
              
              let premisesAreValid = true
              for (let premise = 0; premise < premises.length; premise++) {
                if (!formulasInclude(previousConclusions, premise.conclusion)) {
                  console.error('LogicError: Cannot assume ' + logicString(premise.conclusion) + ' from previous conclusions.')
                  premisesAreValid = false
                  break
                }
              }
              return premisesAreValid
            }

          }
        }
      
      /**
       * Verifies if the conclusion is valid, based on previous lines of reasoning.
       * 
       * Within axioms, conclusions are set to true. Otherwise, conclusions are set to be the last conclusion within the reasoning.
       * 
       * @param {string} argType 
       * @param {Array} argReasoning 
       * @param {Object} argConclusion 
       * 
       * @returns {boolean} whether the conclusion is valid or not.
       */
      function validConclusion(argType, argReasoning, argConclusion) {
        if (!isType(argConclusion, logictype.conclusion)) throw 'LogicError: Conclusions must be of type conclusion. Received: ' + argConclusion.type

        // if argument is empty, conclusion is valid (see emptyArgument)
        if (isType({type: argType}, logictype.empty)) return true

        // conclusions within axioms are always true, no matter reasoning
        if (isType({type: argType}, logictype.axiom)) {
          return true
        } else {
          // get the last conclusion from reasoning
          let lastConclusion = argReasoning[argReasoning.length - 1].conclusion

          return checkEqual(lastConclusion, argConclusion)
        }
      }

  // FORMULA->ARGUMENT FUNCTIONS

    /**
     * Creates an axiom.
     * 
     * Axioms are arguments set to be true within a logical system.
     * 
     * @param {Object} formula 
     * @param {Array} [optionalPremises]
     * 
     * @returns {Argument} an axiom
     */
    function toAxiom(formula, optionalPremises = []) {
      if (!validPremise(logictype.axiom, optionalPremises)) throw 'LogicError: toAxiom() received invalid premises.'

      let argConclusion = newConclusion(formula)
      return newArgument(logictype.axiom, optionalPremises, emptyAssumption, [], argConclusion)
    }

// UTILITY FUNCTIONS

  /**
   * Looks for a key inside the object.
   * 
   * It will iterate through keys and objects inside objects (if any) until it finds a key or has iterated through the entire object.
   * 
   * @example
   * // returns {hasFound: true, path: ["Teyvat", "Liyue", "Nantianmen"]}
   * findKey({Teyvat: {Mondstadt: {Starfell_Lake: {}}, Liyue: {Wangshu_Inn: {}, Nantianmen: {}, Lingju_Pass: {}}}}, 'Nantianmen')
   * @example
   * // returns {hasFound: false, path: []}
   * findKey({a: {b: {}, c: {d: {}}}}, 'e')
   * 
   * @param {Object} object - The object it should look for a key in.
   * @param {string} key - The key it should look for.
   * 
   * @returns {Pathway} The pathway it took to find the key.
   */
  function findKey(object, key) {

    if (typeof object !== 'object') return {hasFound: false, path: []}

    for (let objKey in object) {

      if (objKey === key) return {hasFound: true, path: [objKey]}

      else if (typeof object[objKey] === 'object') {
        let find_key = findKey(object[objKey], key)

        if (find_key.hasFound) {
          let returnPath = find_key.path
          returnPath.unshift(objKey)
          return {hasFound: true, path: returnPath}
        }
      }

    }

    return {hasFound: false, path: []}

  }

  /**
   * Looks for a type inside logic.
   * 
   * @see findKey
   * 
   * @param {string} type - The type it should look for.
   * 
   * @returns {Pathway} The pathway it took to find the type.
   */
  function findType(type) {

    return findKey(logic, type)

  }

  /**
   * Checks if a given child key is inside a nested object of key parent.
   * 
   * If the given child is not found in object, it'll return undefined. Else, it will get its pathway and see if parent is there.
   * 
   * @see findKey
   * 
   * @param {Object} object - The object to look for the keys
   * @param {string} parent - The key associated with a nested object
   * @param {string} child - A key inside the nested object
   * 
   * @returns {boolean|undefined} Whether parent is the key to a nested object with child inside
   */
  function hasParentKey(object, parent, child) {
    let findChild = findKey(object, child)

    if (findChild.hasFound) {
      let result = findChild.path.includes(parent)
      return result
    } else {
      return undefined
    }
  }
  
  /**
   * Creates an array of length arraySize where index zero has string
   * 
   * The rest of the entries in the array will be empty strings.
   * 
   * @example
   * // returns ['owo', '', '']
   * stringToArray('owo', 3)
   * 
   * @param {string} string - The string to put on index zero
   * @param {number} [arraySize] - The size of the array
   * 
   * @returns {Array} An array
   */
  function stringToArray(string, arraySize = 1) {
    if (!(arraySize >= 1)) arraySize = 1
    if (!(typeof string === 'string')) string = string.toString()

    let returnArray = [string]

    for (let index = 1; index < arraySize; index++) {
      returnArray.push('')
    }

    return returnArray
  }

// TEST FUNCTIONS

  /**
   * Creates an object of random length, random key names and random values for each key.
   * 
   * @see randomValue
   * 
   * @param {number} maxLength - The length will be a random number from 0 to maxLength-1
   * 
   * @returns {Object} A random object
   */
  function randomObject(maxLength = 20) {
    let objectLength = Math.floor(Math.random() * Math.abs(maxLength))

    let returnObj = {}

    for (let index = 0; index < objectLength; index++) {
      let key = randomString()

      let value = randomValue(maxLength)

      returnObj[key] = value
    }

    return returnObj
  }

  /**
   * Creates an array of random length and random values
   * 
   * @see randomValue
   * 
   * @param {number} maxLength - The length will be a random number from 0 to maxLength-1
   * 
   * @returns {Array} A random array
   */
  function randomArray(maxLength = 20) {
    let arrayLength = Math.floor(Math.random() * Math.abs(maxLength))

    let returnArray = []

    for (let index = 0; index < arrayLength; index++) {
      let value = randomValue(maxLength)

      returnArray[index] = value
    }

    return returnArray
  }

  /**
   * Creates a string filled with random characters
   * 
   * It'll get a random number in [0, 1) and if it's smaller than 0.85, it'll add a character.
   * That way, the chance of getting an empty string is 15%, a length<10 string is 80%, a length>30 string is 0.64%
   * 
   * @param {Array} include - Which characters the random string should have
   * 
   * @example
   * // may return "mattzipokirtnjjtjif"
   * randomString(['lowercase'])
   * 
   * @example
   * // may return "2C9f3/Y$F=ep"
   * randomString()
   * 
   * @returns {string} A random string
   */
  function randomString(include = ['lowercase', 'uppercase', 'number', 'special']) {
    const char = {
      lowercase: 'abcdefghijklmnopqrstuvwxyz',
      uppercase: 'ABCDEFGHIJKLMNOPQRSTUVWXYZ',
      number: '0123456789',
      special: '!@#$%&*()_-+=/'
    }

    // if function received a non array or empty array parameter, set it to default
    if (!Array.isArray(include) || include.length === 0) include = ['lowercase', 'uppercase', 'special']
    // filter out any invalid sets in include
    include = include.filter(set => (set in char))

    const newCharChance = 0.85  // 85%

    let returnString = ''

    let addChar = Math.random() < newCharChance

    while (addChar) {
      let getRandomIndex = Math.floor(Math.random() * include.length)
      let getRandomCharSet = char[include[getRandomIndex]]
      let randomCharIndex = Math.floor(Math.random() * getRandomCharSet.length)
      let randomChar = getRandomCharSet[randomCharIndex]

      returnString = returnString.concat(randomChar)

      addChar = Math.random() < newCharChance
    }

    return returnString

  }

  /**
   * Creates a value of random variable type
   * 
   * @see randomObject
   * @see randomArray
   * @see randomString
   * 
   * @return {string|number|boolean|undefined} A random value
   */
  function randomValue() {
    const possibleTypes = ['string', 'number', 'boolean', 'undefined']

    let randomTypeIndex = Math.floor(Math.random() * possibleTypes.length)
    let valueType = possibleTypes[randomTypeIndex]

    let value
    switch(valueType) {
      case 'string':
        value = randomString()
        break
      case 'number':
        let randomSign = Math.sign(Math.random() - 0.5) // since random() is between 0 and 1, subtracting 0.5 will yield -0.5 to 0.5
        let randomExponent = Math.floor(Math.random() * 100) - 50 // will return something between -50 and 49
        value = randomSign * Math.random() * 2**randomExponent
        break
      case 'boolean':
        value = Math.random() < 0.5 ? true : false
        break
      case 'undefined':
        value = undefined
        break
    }

    return value
  }
