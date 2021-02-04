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
    premise: {},
    axiom: {},
    assumption: {},
    proof: {},
    subproof: {},
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
  },
  // standalone object, representing strings for each type
  type: {
    argument: 'argument',
    premise: 'premise',
    axiom: 'axiom',
    assumption: 'assumption',
    proof: 'proof',
    subproof: 'subproof',
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
    uni: 'unary'
  }
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
   * @property {string} type   - Either logic.type.var or logic.type.def
   * @property {string} symbol - The string representation of the term.
   * 
   * @typedef Predicate
   * @property {string} type    - = logic.type.pred
   * @property {number} arity   - Integer greater or equal to zero.
   * @property {Array} visual   - Array of size (arity+1) storing the string representation of the given predicate.
   * 
   * @typedef Statement
   * @property {string} type         - = logic.type.state
   * @property {Predicate} predicate - A valid predicate.
   * @property {Array} terms         - An array composed of terms and size (arity of Predicate).
   * @property {Array} variables     - A list of objects with each variable in terms and wether they're bound or not.
   * @property {string} [string]     - Its string representation.
   * 
   * @typedef WFF
   * @property {string} type         - = logic.type.wff
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
   * It'll go through the object in logic.type and check if the type in typeToVerify is equal or parent of logicalObject.type
   * @see logic.type
   * 
   * @param {Object} logicalObject 
   * @param {string} typeToVerify 
   * 
   * @returns {boolean} whether the logical object is or isn't of type typeToVerify
   */
  function isType(logicalObject, typeToVerify) {
    let findType = findKey(logic.type, logicalObject.type)
    if (!findType.hasFound) throw 'LogicError: isType() expects a logical object.'
    else {
      // if we found a logical type, check if typeToVerify is itself or a parent type
      if (findType.path.includes(typeToVerify)) return true
      else return false
    }
  }

  /**
   * Creates a term that is represented by symbol.
   * 
   * Terms are the fundamental objects to build predicates and so any formulas in First Order Logic.
   * 
   * @param {string} symbol - The string representation of the term
   * @param {string} termType - Either logic.type.var or logic.type.def
   * 
   * @returns {Term} a term
   */
  function newTerm(symbol, termType) {
    if (typeof symbol === 'string') {
      if (termType === logic.type.var || termType === logic.type.def) {
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

    return {'type': logic.type.pred, 'arity': arity, 'visual': visual}
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
    if (!isType(predicate, logic.type.pred)) throw 'LogicError: newStatement(pred, terms) pred expects a predicate.'
    if (!Array.isArray(terms)) throw 'LogicError: newStatement(pred, terms) terms expects an array. Received: ' + typeof terms

    let problematicIndexes = []
    let termsAreValid = true
    terms.forEach((term, index) => {
      if (!isType(term, logic.type.term)) {
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
      if (isType(term, logic.type.var)) variableList.push({isBound: false, variable: term})
    })

    let returnObj = {}
    returnObj['type'] = logic.type.state
    returnObj[logic.type.pred] = predicate
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
      if (!isType(term, logic.type.term)) {
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
      if (isType(term, logic.type.var)) variableList.push({isBound: false, variable: term})
    })

    let returnObj = {}
    returnObj['type'] = logic.type.wff
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
    if (!isType(formula, logic.type.formula)) throw 'LogicError: Negation expects a formula. Received: ' + formula.type

    let variables = formula.variables

    let returnObj = {}
    returnObj['type'] = logic.type.not
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
    if (!isType({type: binaryType}, logic.type.bin)) throw 'LogicError: Expected a binary-operation type. Received: ' + binaryType

    if (!Array.isArray(formulas)) throw 'LogicError: Formulas must be within an array. Received: ' + typeof formulas
    else if (formulas.length !== 2) throw 'LogicError: Binary operations are composed of 2 formulas. Received: ' + formulas.length
    
    // I didn't use forEach because the loop may have to break
    for (let index = 0; index < 2; index++) {
      if (!isType(formulas[index], logic.type.formula)) throw 'LogicError: Binary formulas are composed of type formula objects. Received ' + formulas[index].type
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
    return newBinary(logic.type.con, formulas, ['(', '\implies', ')'])
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
    } else if (isType(logicalObject, logic.type.term)) {
      return logicalObject.symbol
    } else if (isType(logicalObject, logic.type.state)) {
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
    } else if (isType(logicalObject, logic.type.wff)) {
      let returnString = logicalObject.symbol
      logicalObject.forEach.terms(term => returnString = returnString.concat(logicString(term)))
      return returnString
    } else if (isType(logicalObject, logic.type.bin)) {
      let returnString = ''
      // returnString = visual[0] + formula[0] + visual[1] + formula[1] + visual[2]
      logicalObject.formulas.forEach((formula, index) => {
        returnString = returnString.concat(logicString(formula), logicalObject.visual[index])
      })
      returnString = returnString.concat(logicalObject.visual[2])
      return returnString
    } else if (isType(logicalObject, logic.type.uni)) {
      let visual = logicalObject.visual
      let formula = logicalObject.formula
      let returnString = visual[0] + logicString(formula) + visual[1]
      return returnString
    } else {
      throw 'LogicError: Could not identify the logic object type: ' + logicalObject.type
    }
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
