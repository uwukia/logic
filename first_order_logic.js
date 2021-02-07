'use strict'

/**
 * @author Kia Strawberries
 * Github: {@link https://github.com/uwukia}
 */

// should the json file include string representations?
const saveString = true

/**
 * I settled with 5 fundamental categories of objects within F.O.L
 * 
 * Predicates + Terms = Statement
 * Axiomatic formulas generate every other category of formula.
 * Formulas can be converted into arguments
 */

const logic = {
  argument: {
    assumption: {
      premise: {}
    },
    proof: {},
    axiom: {}
  },
  formula: {
    axiomatic: {
      statement: {},
      wff: {},
    },
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
    conclusion: {}
  },
  scope: {},
  predicate: {},
  term: {
    constant: {},
    variable: {}
  }
}

const logictype = {
  and: 'conjunction',
  argument: 'argument',
  arg: 'argument',
  assumption: 'assumption',
  axiom: 'axiom',
  axiomatic: 'axiomatic',
  bicon: 'bicontidional',
  biconditional: 'biconditional',
  bin: 'binary',
  binary: 'binary',
  con: 'conditional',
  conclusion: 'conclusion',
  conditional: 'conditional',
  conjunction: 'conjunction',
  const: 'constant',
  constant: 'constant',
  disjunction: 'disjunction',
  existential: 'existential',
  formula: 'formula',
  negation: 'negation',
  not: 'negation',
  or: 'conjunction',
  pred: 'predicate',
  predicate: 'predicate',
  premise: 'premise',
  proof: 'proof',
  quantifier: 'quantifier',
  reason: 'reasoning',
  reasoning: 'reasoning',
  scope: 'scope',
  state: 'statement',
  statement: 'statement',
  subproof: 'subproof',
  term: 'term',
  unary: 'unary',
  uni: 'unary',
  universal: 'universal',
  var: 'variable',
  variable: 'variable',
  wff: 'wff',
  empty: 'empty'
}

// LOGIC FUNCTIONS

  // MAIN FUNCTIONS

    /**
     * Checks for an object type and verifies if it is of type typeToVerify
     * 
     * It'll go through the object in logic and check if the type in typeToVerify is equal or parent of logicalObject.type
     * @see logic
     * @see findKey
     * 
     * @param {Object} logicalObject 
     * @param {string} typeToVerify 
     * 
     * @returns {boolean} whether the logical object is or isn't of type typeToVerify
     */
    function isType(logicalObject, typeToVerify) {

      if (typeof logicalObject === 'undefined') throw 'LogicError: isType() received an undefined object.'

      if (typeof logicalObject === 'string') logicalObject = {type: logicalObject}

      let findType = findKey(logic, logicalObject.type)

      if (!findType.hasFound) throw 'LogicError: Cannot recognize the logical type: ' + logicalObject.type
      else {
        // if we found a logical type, check if typeToVerify is itself or a parent type
        if (findType.path.includes(typeToVerify)) return true
        else return false
      }
    }
      
    /**
     * This function gets two logical objects and checks if their contents are equal.
     * 
     * @param {Formula|Predicate|Term} logic1 
     * @param {Formula|Predicate|Term} logic2 
     * 
     * @returns {boolean} logic1 === logic2
     */
    function checkEqual(logic1, logic2) {

      if (!findKey(logic, logic1.type).hasFound) throw 'LogicError: First input has an invalid logic type: ' + logic1.type
      if (!findKey(logic, logic2.type).hasFound) throw 'LogicError: Second input has an invalid logic type: ' + logic2.type

      let checkType = logic1.type === logic2.type

      if (!checkType) return false
      else {
        let logicType = logic1.type

        if (typeof logicType === 'undefined') {
          throw 'LogicError: Expected logical objects. Received: ' + formulaType
        } else if (isType(logicType, logictype.term)) {

          return (logic1.symbol === logic2.symbol) // @see Term

        } else if (isType(logicType, logictype.pred)) {

          let arityEqual = logic1.arity === logic2.arity
          // assume visuals are equal
          let visualEqual = true

          if (arityEqual) {
            let arity = logic1.arity
            // visuals are of size arity + 1
            for (let index = 0; index < arity + 1; index++) {
              // if at least one visual is different, visuals are different
              if (logic1.visual[index] !== logic2.visual[index]) {
                visualEqual = false
                break
              }
            }
          }

          return (arityEqual && visualEqual)
          
        } else if (isType(logicType, logictype.formula)) {
          if (isType(logicType, logictype.wff)) {
            
            let symbolEqual = logic1.symbol === logic2.symbol
            // assume terms are equal based on array size (@see WFF)
            let termsEqual = logic1.terms.length === logic2.terms.length

            if (termsEqual) {
              for (let index = 0; index < logic1.terms.length; index++) {
                let termEqual = checkEqual(logic1.terms[index], logic2.terms[index])
                if (!termEqual) {
                  termsEqual = false
                  break
                }
              }
            }

            return (symbolEqual && termsEqual)
          } else if (isType(logicType, logictype.state)) {
            
            let predEqual = checkEqual(logic1[logictype.pred], logic2[logictype.pred])
            // assume terms are equal
            let termsEqual = true

            for (let index = 0; index < logic1.terms.length; index++) {
              let termEqual = checkEqual(logic1.terms[index], logic2.terms[index])
              if (!termEqual) {
                termsEqual = false
                break
              }
            }

            return (predEqual && termsEqual)
          } else if (isType(logicType, logictype.unary)) {
            return checkEqual(logic1.formula, logic2.formula)
          } else if (isType(logicType, logictype.binary)) {
            let firstEqual = checkEqual(logic1.formula[0], logic2.formula[0])
            let secondEqual = checkEqual(logic1.formula[1], logic2.formula[1])
            return (firstEqual && secondEqual)
          }
        }

        throw 'LogicError: checkEqual() is missing a case for type: ' + logicType.type
      }
    }

    /**
     * Substitutes a formula for anothe formula.
     * 
     * It'll go through each entry in subMap, and if formulaToSub is equal to entry[0], it'll change to entry[1].
     * If the formula is not axiomatic, it'll go through the formulas inside of it.
     * 
     * @param {Array.<Array.<Formula>>} subMap - an array of length-2 arrays where [0] is the formula to find and [1] is the formula to substitute it for.
     * @param {Formula} formulaToSub - The formula in which the substitutions will be performed.
     * 
     * @returns {Formula} the substitution.
     */
    function formulaSub(subMap, formulaToSub) {
      if (!Array.isArray(subMap)) throw 'LogicError: Substitution Map must be an array. Received: ' + typeof subMap
      else {
        // subMap may have to break in case of an error, so I used for instead of forEach
        for (let sub = 0; sub < subMap.length; sub++) {
          if (!Array.isArray(subMap[sub])) throw 'LogicError: Substitution Map must be composed of arrays. Received: ' + typeof subMap[sub]
          if (subMap[sub].length !== 2) throw 'LogicError: Substitution must be an array of length 2. Received length: ' + subMap[sub].length
          if (!isType(subMap[sub][0], logictype.formula)) throw 'LogicError: Substitution[0] expected a formula. Received: ' + subMap[sub][0].type
          if (!isType(subMap[sub][1], logictype.formula)) throw 'LogicError: Substitution[1] expected a formula. Received: ' + subMap[sub][1].type
        }
      }
      // from here, subMap is valid

      if (!isType(formulaToSub, logictype.formula)) throw 'formulaSub() expects a formula. Received: ' + formulaToSub.type
      
      // from here, formulaToSub is valid

      // initialize the substituted formula
      let subFormula = cloneObj(formulaToSub)

      subMap.forEach(sub => {

        let checkForEqual = sub[0]
        let substituteFor = sub[1]

        if (checkEqual(formulaToSub, checkForEqual)) {
          subFormula = substituteFor
        } else if (isType(formulaToSub, logictype.unary)) {
          // formulas of type unary only have a formula inside
          subFormula.formula = formulaSub(subMap, formulaToSub.formula)
        } else if (isType(formulaToSub, logictype.binary)) {
          // binary formulas have 2 formulas inside that need the substitution to be applied
          subFormula.formulas[0] = formulaSub(subMap, formulaToSub.formulas[0])
          subFormula.formulas[1] = formulaSub(subMap, formulaToSub.formulas[1])
        }
      })

      return subFormula
    }

    /**
     * Substitute the variables within a formula for other variables.
     * 
     * I will admit this function is looking hella confusing. But to be honest, I can't be bothered to make it nicer right now.
     * @todo make this function readable
     * 
     * @param {Array.<Array.<Term>>} subMap 
     * @param {Formula} formulaToSub 
     * 
     * @returns {Formula}
     */
    function varSub(subMap, formulaToSub) {
      if (!Array.isArray(subMap)) throw 'LogicError: Substitution Map must be an array. Received: ' + typeof subMap
      else {
        // subMap may have to break in case of an error, so I used for instead of forEach
        for (let sub = 0; sub < subMap.length; sub++) {
          if (!Array.isArray(subMap[sub])) throw 'LogicError: Substitution Map must be composed of arrays. Received: ' + typeof subMap[sub]
          if (subMap[sub].length !== 2) throw 'LogicError: Substitution must be an array of length 2. Received length: ' + subMap[sub].length
          if (!isType(subMap[sub][0], logictype.var)) throw 'LogicError: Substitution[0] expected a variable. Received: ' + subMap[sub][0].type
          if (!isType(subMap[sub][1], logictype.var)) throw 'LogicError: Substitution[1] expected a variable. Received: ' + subMap[sub][1].type
        }
      }
      // from here, subMap is valid

      if (!isType(formulaToSub, logictype.formula)) throw 'varSub(..., formula) expects a formula. Received: ' + formulaToSub.type
      
      // from here, formulaToSub is valid

      // initialize the substituted formula
      let subFormula = cloneObj(formulaToSub)

      if (isType(subFormula, logictype.axiomatic)) {
        let oldTerms = subFormula.terms
        let newTerms = []
        let newVars = []

        oldTerms.forEach(term => {
          let termWasSubstituted = false
          let getIndex
          for (let subIndex = 0; subIndex < subMap.length; subIndex++) {
            if (checkEqual(subMap[subIndex][0], term)) {
              // look for the variable in .var.var
              let foundIndex = -1
              for (let index = 0; index < subFormula.var.length; index++) {
                if (checkEqual(subFormula.var[index].var, term)) {
                  foundIndex = index
                  break
                }
              }
              if (foundIndex !== -1) {
                newVars.push({isBound: subFormula.var[foundIndex].isBound, var: subMap[subIndex][1]})
                termWasSubstituted = true
                getIndex = subIndex
                break
              } else {
                throw 'LogicError: Could not find index of variable in .var'
              }
            }
          }
          if (termWasSubstituted) newTerms.push(subMap[getIndex][1])
          else newTerms.push(term)
        })

        subFormula.terms = newTerms
        subFormula.var = newVars
        // if (saveString) subFormula.string = logicString(subFormula)
      } else if (isType(subFormula, logictype.unary)) {
        let sub_subFormula = varSub(subMap, subFormula.formula)
        subFormula.terms = sub_subFormula.terms
        subFormula.var = sub_subFormula.var
        // if (saveString) subFormula.string = logicString(subFormula)
      } else if (isType(subFormula, logictype.binary)) {
        let sub_subFormula1 = varSub(subMap, subFormula.formulas[0])
        let sub_subFormula2 = varSub(subMap, subFormula.formulas[1])
        let allVariables = sub_subFormula1.var.concat(sub_subFormula2.var)
        
        subFormula.formulas = [sub_subFormula1, sub_subFormula2]
        subFormula.var = getVar(allVariables, true)
        // if (saveString) subFormula.string = logicString(subFormula)
      } 

      return subFormula
    }

    /**
     * Checks if the formula lookForFormula is one of the formulas inside listOfFormulas.
     * 
     * This function is similar to Array.includes(), as if we were doing listOfFormulas.includes(lookForFormula).
     * 
     * @param {Array.<Formula>} listOfFormulas 
     * @param {Formula} lookForFormula 
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

  // ARGUMENT FUNCTIONS

    /**
     * @typedef Argument
     * @property {string} type 
     * @property {Array.<Argument>} premise
     * @property {Array.<Argument>} reasoning 
     * @property {Formula} conclusion
     * @property {Argument} [assumption]
     */

    /**
     * Creates a new argument.
     * 
     * Arguments, in logic, are made up of premises (a set of arguments assumed to be true), lines of reasoning (arguments that can be concluded from previous lines),
     * and a conclusion, which is the conclusion from the last line of reasoning (unless it's a special type of argument, like an axiom).
     * 
     * The use of this function to create axioms, empty arguments, subproofs, etc is discouraged. Please look at the following functions:
     * @todo this
     * 
     * @param {string} argType 
     * @param {Array.<Argument>} argPremise 
     * @param {Array.<Argument>} argReasoning 
     * @param {Formula} argConclusion 
     * @param {Argument} argAssumption
     * 
     * @returns {Argument} an argument.
     */
    function newArgument(argType, argPremise, argReasoning, argConclusion, argAssumption) {
      
      // is argType valid?
      if (!isType(argType, logictype.arg)) throw 'LogicError: Expected an argument. Received: ' + argType

      // are premises valid?
      if (!validPremise(argType, argPremise)) throw 'LogicError: Argument premises are invalid.'

      // is the assumption valid?
      if (argAssumption) {
        if (!isType(argAssumption, logictype.assumption)) throw 'LogicError: Expected an assumption. Received: ' + argAssumption.type
      }

      // is the reasoning behind the argument valid?
      if (!validReasoning(argType, argPremise, argAssumption, argReasoning)) throw 'LogicError: Argument reasoning is invalid.'

      // is the conclusion valid?
      if (argConclusion) {
        if (!validConclusion(argType, argReasoning, argConclusion)) throw 'LogicError: Argument conclusion is invalid.'
      }

      // from here, the code knows all the inputs are valid

      let returnArg = {
        type: argType,
        premise: argPremise,
        reasoning: argReasoning,
        conclusion: argConclusion
      }

      if (argAssumption) returnarg[logictype.assumption] = argAssumption

      return returnArg
    }

    /**
     * Creates an empty argument.
     * 
     * Use this function to make proofs or subproofs line-by-line, instead of defining everything and calling newArgument
     * 
     * @returns {Argument} an empty argument
     */
    function startArgument(argType = logictype.proof) {
      return newArgument(argType, [], [])
    }

    /**
     * Adds a premise to an argument
     * 
     * @param {Argument} premise 
     * @param {Argument} argument 
     * 
     * @returns {Argument}
     */
    function addPremise(premise, argument) {
      if (!isType(premise, logictype.premise)) throw 'LogicError: Expected a premise to be added. Received: ' + premise.type

      if (!isType(argument, logictype.arg)) throw 'LogicError: Cannot add a premise to a non-argument object: ' + argument.type
      if (!isType(argument, logictype.assumption)) throw 'LogicError: Cannot add a premise to another premise or assumption.'

      // premise and argument are valid

      argument.premise.push(premise)

      return argument
    }

    function argSubstitution(substitutionMap, argument) {
      if (!isType(argument, logictype.arg)) throw 'LogicError: Cannot make a substitution on a non-argument object: ' + argument.type
      if (!(isType(argument, logictype.axiom) || isType(argument, logictype.proof))) {
        'LogicError: Substitutions may only be applied to axioms and proofs. Received: ' + argument.type
      }

      let newArgument = cloneObj(argument)

      newArgument.premise.forEach((prem, index) => {
        newArgument.premise[index] = toPremise(formulaSub(substitutionMap, prem.conclusion))
      })

      if (newArgument.assumption) {
        // newArgument.assumption = toAssumption(formulaSub(substitutionMap, assumption.conclusion))
      }

      newArgument.reasoning.forEach((line, index) => {
        newArgument.reasoning[index] = argSubstitution(substitutionMap, line)
      })

      if (isType(newArgument, logictype.axiom)) {
        newArgument.conclusion = formulaSub(substitutionMap, newArgument.conclusion)
      } else {
        newArgument.conclusion = newArgument.reasoning[newArgument.reasoning.length - 1].conclusion
      }

      newArgument.substitution = substitutionMap

      return newArgument
    }

    // ARGUMENT-VALIDATION FUNCTIONS

      /**
       * Verify an argument's premises based on its type.
       * 
       * @param {string} argType 
       * @param {Array.<Argument>} argPremises 
       * 
       * @returns {boolean} whether premises are valid or not.
       */
      function validPremise(argType, argPremises) {
        if (!Array.isArray(argPremises)) throw 'Premises should be within an array. Received: ' + typeof argPremises

        if (isType(argType, logictype.assumption) && argPremises.length > 0) {
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
       * @param {Array.<Argument>} argPremises 
       * @param {Argument} argAssumption
       * @param {Array.<Argument>} argReasoning 
       * 
       * @returns {boolean} whether the reasoning is valid or not.
       */
      function validReasoning(argType, argPremises, argAssumption, argReasoning) {

        if (!Array.isArray(argReasoning)) throw 'Reasoning should be within an array. Received: ' + typeof argReasoning

        // axioms are set to be true, so we can't reason around them
        if (argReasoning.length > 0 && isType(argType, logictype.axiom)) {
          console.error('Axioms must have no reasoning.')
          return false
        }

        // this array will store all conclusions up to some point in the argument
        let previousConclusions = []

        argPremises.forEach(premise => {
          previousConclusions.push(premise.conclusion)
        })

        // if the assumption isn't empty, add its conclusion to the list as well
        if (argAssumption) {
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
       * If the line is an axiom, it's set to be true. If it's not an axiom, its premises's conclusions must come from previousConclusions.
       * @see formulasInclude
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
            // verify if all premise conclusions are equal to any of the previous conclusion
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
        if (!isType(argConclusion, logictype.formula)) throw 'LogicError: Conclusions must be formulas. Received: ' + argConclusion.type
        // conclusions within axioms or assumptions are always true, no matter reasoning
        if (isType(argType, logictype.axiom) || isType(argType, logictype.assumption)) {
          return true
        } else {
          // get the last conclusion from reasoning
          let lastConclusion = argReasoning[argReasoning.length - 1].conclusion

          return checkEqual(lastConclusion, argConclusion)
        }
      }

  // FORMULA FUNCTIONS

    // PREDICATE FUNCTIONS

      /**
       * @typedef Term
       * @property {string} type
       * @property {string} symbol
       * 
       * @typedef Predicate
       * @property {string} type
       * @property {number} arity 
       * @property {Array.<string>} visual
       * 
       */

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
        if (typeof symbol !== 'string') throw 'LogicError: Terms must be composed of strings. Received: ' + typeof symbol
        if (typeof termType !== 'string') throw 'LogicError: Term types must be strings. Received: ' + typeof termType

        if (termType === logictype.var || termType === logictype.const) {
          return {'type': termType, 'symbol': symbol}
        } else {
          throw 'LogicError: Terms must be of type variable or constant. Received: ' + termType
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

    // AXIOMATIC FUNCTIONS

      /**
       * @typedef Axiomatic
       * @property {string} type
       * @property {Predicate} predicate
       * @property {Array.<Term>} terms
       * @property {Array.<Term>} var
       * @property {string} [string]
       */

      /**
       * Creates a statement based on a predicate and a list of terms.
       * 
       * The array terms must be only composed of terms and its size must match the predicate's arity.
       * @see newTerm
       * @see newPredicate
       * 
       * @param {Predicate} predicate 
       * @param {Array.<Term>} terms 
       * 
       * @returns {Axiomatic}
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
          throw 'LogicError: newStatement(..., terms) expects an array of valid terms.'
        }

        if (terms.length !== predicate.arity) throw 'LogicError: Expected ' + predicate.arity + 'terms. Received: ' + terms.length

        // from here, predicate is valid, terms are valid

        let variableList = getVar(terms)

        let returnObj = {}
        returnObj['type'] = logictype.state
        returnObj[logictype.pred] = predicate
        returnObj['terms'] = terms
        returnObj['var'] = variableList
        // if (saveString) returnObj['string'] = logicString(returnObj)

        return returnObj
      }

      /**
       * Creates a representation of a formula, which is useful for stating theorems.
       * 
       * @see newTerm
       * 
       * @param {string} symbol - The string representation
       * @param {Array.<Term>} [dependentTerms] - The terms the given formula should be depended on
       * 
       * @returns {Axiomatic} a well-formed-formula
       */
      function newWFF(symbol, dependentTerms = []) {
        if (typeof symbol !== 'string') throw 'LogicError: newWFF() expects a symbol of type string to represent it. Received: ' + typeof symbol
        if (!Array.isArray(dependentTerms)) throw 'LogicError: newWFF() terms expects an array. Received: ' + typeof terms

        let problematicIndexes = []
        let termsAreValid = true
        dependentTerms.forEach((term, index) => {
          if (!isType(term, logictype.term)) {
            if (termsAreValid) termsAreValid = false
            problematicIndexes.push(index)
          }
        })

        if (!termsAreValid) {
          problematicIndexes.forEach(termIndex => {
            console.error('Received an invalid term of type ' + dependentTerms[termIndex].type + ' in index ' + termIndex)
          })
          throw 'LogicError: newStatement(pred, terms) terms expects an array of valid terms.'
        }

        // from here, symbol is valid, terms (if any) are valid

        let variableList = getVar(dependentTerms)

        let returnObj = {}
        returnObj['type'] = logictype.wff
        returnObj['symbol'] = symbol
        returnObj['terms'] = dependentTerms
        returnObj['var'] = variableList
        // if (saveString) returnObj['string'] = logicString(returnObj)
        return returnObj
      }

        /**
         * Creates a list of variables based on a list of terms
         * 
         * @param {Array.<Term>} terms
         * @param {boolean} fromVar - whether "terms" are already a list of vars with isBound parameters
         * 
         * @returns {Array.<Term>} a list of variables 
         */
        function getVar(terms, fromVar = false) {
          let variableList = []

            terms.forEach((term) => {

              let newTerm
              if (fromVar) newTerm = term.var
              else newTerm = term

              if (isType(newTerm, logictype.var)) {
                let repeatedVar = false
  
                variableList.forEach(variable => {
                  if (checkEqual(newTerm, variable.var)) repeatedVar = true
                })
  
                if (!repeatedVar) variableList.push({isBound: false, var: newTerm})
              }
            })

          return variableList
        }
    
    // GENERAL FORMULA FUNCTIONS

      /**
       * @typedef {Axiomatic|Unary|Binary} Formula
       * 
       * @typedef Unary
       * @property {string} type           
       * @property {Formula} formula       
       * @property {Array.<Term>} var      
       * @property {Array.<string>} visual - length = 2
       * @property {string} [string]       
       */

      // UNARY FUNCTIONS

        /**
         * Creates a negation based on a formula.
         * 
         * @param {Axiomatic|Unary|Binary|Quantifier} formula 
         * 
         * @returns {Unary} !formula
         */
        function newNot(formula) {
          if (!isType(formula, logictype.formula)) throw 'LogicError: Negation expects a formula. Received: ' + formula.type

          let variables = formula.var

          let returnObj = {}
          returnObj['type'] = logictype.not
          returnObj['formula'] = formula
          returnObj['var'] = variables
          returnObj['visual'] = ['¬', '']
          // if (saveString) returnObj['string'] = logicString(returnObj)
          return returnObj
        }

      // BINARY FUNCTIONS

        /**
         * @typedef Binary
         * @property {string} type
         * @property {Array.<Formula>} formulas
         * @property {Array.<Term>} var
         * @property {Array.<string>} visual - length = 3
         * @property {string} [string]
         */

        /**
         * Creates a logical binary operation (like a conditional or a conjunction)
         * 
         * @param {string} binaryType        - must be a key in logic.formula.bin
         * @param {Array.<Formula>} formulas - A length-2 array composed of formulas (wff, statement, binary, etc.)
         * @param {Array.<string>} visual    - A length-3 array with the string representation of the given binary type.
         * 
         * @returns {Binary} a logical binary operation.
         */
        function newBinary(binaryType, formulas, visual) {
          if (!isType(binaryType, logictype.bin)) throw 'LogicError: Expected a binary-operation type. Received: ' + binaryType

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
          let allVariables = formulas[0].var.concat(formulas[1].var)
          let variables = getVar(allVariables, true)

          let returnObj = {}
          returnObj['type'] = binaryType
          returnObj['formulas'] = formulas
          returnObj['visual'] = visual
          returnObj['var'] = variables
          // if (saveString) returnObj['string'] = logicString(returnObj)

          return returnObj
        }

        function newConditional(condition, implication) {
          return newBinary(logictype.con, [condition, implication], ['(', '\\implies', ')'])
        }

  // FORMULA->ARGUMENT FUNCTIONS

    /**
     * Creates an axiom based on a formula and optional premises.
     * @param {Formula} formula 
     * @param {Array.<Argument>} optionalPremise
     * 
     * @returns {Argument} an axiom
     */
    function toAxiom(formula, optionalPremise = []) {
      if (!isType(formula, logictype.formula)) throw 'toAxiom() expects a formula as input. Received: ' + formula.type

      return newArgument(logictype.axiom, optionalPremise, [], formula)
    }

    /**
     * Creates a premise based on a formula.
     * @param {Formula} formula 
     * 
     * @returns {Argument} a premise
     */
    function toPremise(formula) {
      if (!isType(formula, logictype.formula)) throw 'toPremise() expects a formula as input. Received: ' + formula.type

      return newArgument(logictype.premise, [], [], formula)
    }

// UTILITY FUNCTIONS

  // These functions have general use and could be used by other programmers in other contexts.

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
   * Creates an array of length arraySize where index zero has the input string
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

  /**
   * Creates an object clone, allocating its information in a different part of memory.
   * 
   * @author {@link https://stackoverflow.com/users/35881/a-levy}
   * source: {@link https://stackoverflow.com/questions/728360/how-do-i-correctly-clone-a-javascript-object}
   * 
   * @param {Object} object
   * 
   * @returns {Object} its clone. 
   */
  function cloneObj(object) {
    var copy

    // Handle non-object types
    if (typeof object !== 'object') return object

    // Handle Array
    if (Array.isArray(object)) {
        copy = []
        for (let i = 0; i < object.length; i++) {
            copy[i] = cloneObj(object[i])
        }
        return copy
    }

    // Handle Object
    if (typeof object === 'object') {
        copy = {}
        for (var key in object) {
            if (object.hasOwnProperty(key)) copy[key] = cloneObj(object[key])
        }
        return copy
    }

    throw new Error("Unable to copy object! Its type isn't supported.");
  }
