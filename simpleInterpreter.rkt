#lang racket

(require "functionParser.rkt")
(require racket/trace) ; Enables the use of the "trace" function (for debugging purposes)

; Interprets the code contained in the file with the inputted filename
(define interpret*
  (lambda (filename) (translate-booleans (call-main (interpret-raw-code* (parser filename) '() value-state)))))

; Replaces "#t" with "true" and "#f" with "false", but leaves the inputted value untouched otherwise
(define translate-booleans
  (lambda (output)
    (if (boolean? output) (if (eq? output #t) 'true 'false) output)))

; Calls the main() function and returns its output
(define call-main
  (lambda (layers)
    (if (and (var-exists*? 'main layers) (is-function? 'main layers))
        (call-function 'main '() layers value-state)
        (error "No main() function has been defined in the code!"))))

; Interprets the inputted pre-parsed code one statement at a time, or returns the value of the current statement if it is a "return" statement 
(define interpret-raw-code*
  (lambda (code layers return)
    (cond
      ((null? code) layers)
      (else (interpret-statement*
        (car code)
        layers
        (lambda (v) (interpret-raw-code* (cdr code) v return))
        return                          
        (lambda (layers) (error "Continue statements must be inside of a loop!"))
        (lambda (layers) (error "Break statements must be inside of a loop!"))
        (lambda (v s) (error "Uncaught exception:" v)))))))

; Shortcuts to get the 1st, 2nd, and 3rd arguments of a statement, whenever they exist
(define (arg1 statement) (car (cdr statement))) 
(define (arg2 statement) (if (empty? (cdr (cdr statement))) null (car (cdr (cdr statement)))))
(define (arg3 statement) (arg2 (cdr statement)))

(define (declaration? statement) (eq? 'var (car statement))) ; Checks if a statement declares a variable 
(define (assignment? statement) (eq? '= (car statement))) ; Checks if a statement assigns a value to a variable 
(define (return? statement) (eq? 'return (car statement))) ; Checks if a statement returns a value
(define (block? statement) (eq? 'begin (car statement))) ; Checks if a statement corresponds to a block of code
(define (if-statement? statement) (eq? 'if (car statement))) ; Checks if the inputted statement is an "if" statement
(define (while-statement? statement) (eq? 'while (car statement))) ; Checks if the inputted statement is a "while" statement
(define (continue? statement) (eq? 'continue (car statement))) ; Checks if the inputted statement is a "continue" statement
(define (break? statement) (eq? 'break (car statement))) ; Checks if the inputted statement is a "break" statement
(define (try? statement) (eq? 'try (car statement))) ; Checks if a statement corresponds to a try-catch block
(define (throw? statement) (eq? 'throw (car statement))) ; Checks if a statement is throwing a value/exception
(define (function-def? statement) (eq? 'function (car statement))) ; Checks if a statement is defining a function
(define (function-call? statement) (eq? 'funcall (car statement))) ; Checks if a statement is calling a function

; Adds a new layer to the front of the layers list
(define new-layer
  (lambda (layers) (cons '() layers)))

(define value-state (lambda (v s) v)) ; Default return/throw continuation function defined here for convenience

; Converts a set of function parameters into a list of variable bindings
(define bind-formal-params
  (lambda (formal-params)
    (if (null? formal-params)
        '()
        (cons (new-variable (car formal-params) '(())) (bind-formal-params (cdr formal-params))))))

; Returns an anonymous function that constructs a function's environment
(define construct-environment
  (lambda (formal-params body outer-state)
    (let ((param-layer (bind-formal-params formal-params))
          (global-layer (foldl (lambda (k acc)
                                 (if (and (atom? k)
                                          (not (member k formal-params))
                                          (not (var-exists? k acc))
                                          (var-exists*? k outer-state)
                                          (is-function? k outer-state)) ; only capture functions
                                     (cons (new-variable k (get-variable* k outer-state)) acc)
                                     acc))
                               '()
                               (append
                                 (flatten body)
                                 (foldl (lambda (layer acc)
                                          (append (map name layer) acc))
                                        '()
                                        outer-state)))))
      (lambda (call-time-state)
        (if (null? param-layer)
            (list global-layer)
            (list param-layer global-layer))))))

; Updates the program's variable layers by executing the inputted statement, or returning its associated value if it is a "return" statement
(define interpret-statement*
  (lambda (statement layers next return continue break throw)
    (cond
      ((null? statement) (next layers))
      ((block? statement) (execute-block (cdr statement) (new-layer layers) next return continue break throw))
      ((try? statement) (try-catch-block (arg1 statement) (arg2 statement) (arg3 statement) layers next return continue break throw))
      ((throw? statement) (return-value* (cdr statement) layers (lambda (k s) (throw k s))))
      ((continue? statement) (continue layers))
      ((break? statement) (break layers))
      ((function-call? statement) (call-function (arg1 statement) (cdr (cdr statement)) layers (lambda (v s) (next s))))
      ((declaration? statement) (return-value* (arg2 statement) layers (lambda (k s) (add-variable* (arg1 statement) k s next))))
      ((assignment? statement) (return-value* (arg2 statement) layers (lambda (k s) (set-variable* (arg1 statement) k s next))))
      ((if-statement? statement) (if-statement* (arg1 statement) (arg2 statement) (arg3 statement) layers next return continue break throw))
      ((while-statement? statement) (while-statement* (arg1 statement) (arg2 statement) layers next return continue break throw))
      ((return? statement) (return-value* (cdr statement) layers (lambda (k s) (return k s))))
      ((function-def? statement) (add-variable*
        (arg1 statement)
        (create-closure (arg2 statement) (arg3 statement) (construct-environment (arg2 statement) (arg3 statement) layers))
        layers
        next))
      (else (error "The following statement count not be parsed: " statement)))))

; Handles execution of code blocks, automatically removing the block's variable layer once execution is finished
(define execute-block
  (lambda (code layers next return continue break throw)
    (cond
      ((null? code) (next (cdr layers)))
      (else (interpret-statement*
        (car code)
        layers
        (lambda (v) (execute-block (cdr code) v next return continue break throw))
        return
        continue
        (lambda (v) (break (cdr v)))
        throw)))))

; Handles execution of try-catch blocks
(define try-catch-block
  (lambda (try catch finally layers next return continue break throw)
    (execute-block
      try
      (new-layer layers)
      (lambda (k) (run-finally finally k next return continue break throw))
      return
      continue
      break
      (if (null? catch)
        throw
        (catch-throw catch finally layers next return continue break throw)))))

; Helper function for executing the "finally" portion of the try-catch block, if it exists
(define run-finally
  (lambda (finally layers next return continue break throw)
    (if (null? finally)
        (next layers)
        (execute-block (arg1 finally) (new-layer layers) next return continue break throw))))

; Helper function that output the value-state continuation function that executes the "catch" portion of the try-catch block, if it exists
(define catch-throw
  (lambda (catch finally layers next return continue break throw)
    (lambda (v s)
      (add-variable* (car (arg1 catch)) v (new-layer (cdr s))
        (lambda (catch-env) (execute-block
          (arg2 catch)
          catch-env
          (lambda (k) (run-finally finally k next return continue break throw))
          return
          continue
          break
          throw))))))

; Executes the inputted "if" statement and updates the program's variable layers accordingly
(define if-statement*
  (lambda (condition if-true else layers next return continue break throw)
    (return-value* condition layers
      (lambda (condition-result side-effect) (if condition-result
        (interpret-statement* if-true side-effect next return continue break throw)
        (interpret-statement* else side-effect next return continue break throw))))))

; Executes the inputted "while" statement and updates the program's variable layers accordingly
(define while-statement*
  (lambda (condition body layers next return continue break throw)
    (return-value* condition layers
      (lambda (condition-result side-effect) (if condition-result
        (interpret-statement*
          body
          side-effect
          (lambda (new-layers) (while-statement* condition body new-layers next return continue break throw))
          return
          (lambda (new-layers) (while-statement* condition body new-layers next return continue break throw))
          next
          throw)
        (next side-effect))))))

; Interprets simple statements (i.e. expressions) and returns their results
(define return-value*
  (lambda (output layers cc)
    (cond
      ((null? output) (cc null layers))
      ((number? output) (cc output layers))
      ((boolean? output) (cc output layers))
      ((eq? 'true output) (cc #t layers))
      ((eq? 'false output) (cc #f layers))
      ((atom? output) (cc (get-variable* output layers) layers))
      ((math? output) (return-value* (arg1 output) layers (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (do-math (car output) k1 k2) s2))))))
      ((comparison? output) (return-value* (arg1 output) layers (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (compare (car output) k1 k2) s2))))))
      ((boolean-expression? output) (return-value* (arg1 output) layers (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (boolean (car output) k1 k2) s2))))))
      ((assignment? output) (return-value* (arg2 output) layers (lambda (k s) (set-variable* (arg1 output) k s (lambda (updated-layers) (cc k updated-layers))))))
      ((function-call? output) (call-function (arg1 output) (cdr (cdr output)) layers (lambda (v s) (cc v s))))
      (else (return-value* (car output) layers cc)))))

; Computes the values of the parameters inputted into a function call and binds them to the formal parameters in the function environment
(define compute-params
  (lambda (params inputs layers environment cc)
    (if (null? params)
        (cc environment)
        (return-value*
          (car inputs)
          layers
          (lambda (v s) (set-variable*
            (car params)
            v
            environment
            (lambda (updated-env) (compute-params (cdr params) (cdr inputs) layers updated-env cc))))))))

; Calls the function with the specified name and evaluates it with the specified values for its parameters
(define call-function
  (lambda (name inputs layers cc)
    (if (and (var-exists*? name layers) (is-function? name layers))
      (let* ((closure (get-variable* name layers)) (env (append (new-layer ((env-function closure) layers)) layers)))
        (if (= (length inputs) (length (params closure)))
          (compute-params
          (params closure)
          inputs
          layers
          env
          (lambda (e) (let ((result (interpret-raw-code* (func-body closure) e (lambda (v s) (cc v (propagate-mutations layers s))))))
            (if (list? result)
              (cc null (propagate-mutations layers result))
              result))))
          (error (string-append "Wrong number of parameters for \"" (symbol->string name) "(" (string-join (map symbol->string (params closure)) ", ") ")\"!"))))
      (error (string-append "The function \"" (symbol->string name) "()\" has not yet been defined!")))))

; Updates the caller's layers with any changes made to shared variables during the function call
(define propagate-mutations
  (lambda (caller-layers post-call-layers)
    (map (lambda (layer)
           (map (lambda (binding)
                  (if (and (pair? binding) (var-exists*? (name binding) post-call-layers))
                      (new-variable (name binding) (get-variable* (name binding) post-call-layers))
                      binding))
                layer))
         caller-layers)))

(define (atom? x) (and (not (null? x)) (not (pair? x)))) ; Checks if a list item is an atom (i.e. a non-null, non-list object)
(define (math? statement) (set-member? (set '+ '- '* '/ '%) (car statement))) ; Checks if the statement is just simple arithemetic 
(define (comparison? statement) (set-member? (set '== '!= '< '<= '> '>=) (car statement))) ; Checks if the statement is comparing two values
(define (boolean-expression? statement) (set-member? (set '&& '|| '!) (car statement))) ; Checks if the statement is a simple boolean expression

; Performs an arithemetic operation on the inputted integer(s) using the inputted operator
(define (do-math operator arg1 arg2)
  (cond
    ((or (null? arg1) (and (not (eq? operator '-)) (null? arg2))) (error "Too many null arguments. Ensure that values have been assigned to variables before using them!"))
    ((eq? operator '+) (+ arg1 arg2))
    ((eq? operator '-) (if (null? arg2) (* arg1 -1) (- arg1 arg2))) ; The "if" statement allows for instant negation of a single value
    ((eq? operator '*) (* arg1 arg2))
    ((eq? operator '/) (quotient arg1 arg2))
    ((eq? operator '%) (remainder arg1 arg2))
    (else null)))

; Performs a comparison between two values using the inputted comparator
(define (compare comparator arg1 arg2)
  (cond
    ((eq? comparator '==) (eq? arg1 arg2))
    ((eq? comparator '!=) (not (eq? arg1 arg2)))
    ((eq? comparator '<) (< arg1 arg2))
    ((eq? comparator '<=) (<= arg1 arg2))
    ((eq? comparator '>) (> arg1 arg2))
    ((eq? comparator '>=) (>= arg1 arg2))
    (else #f)))

; Evaluates the boolean expression formed by the boolean input(s) and the inputted connective
(define (boolean connective arg1 arg2)
  (cond
    ((eq? connective '&&) (and arg1 arg2))
    ((eq? connective '||) (or arg1 arg2))
    ((eq? connective '!) (not arg1)) ; Logical "not" only needs the first argument, so the second one is ignored if it exists
    (else #f)))

; Takes a name and a value and creates a binding between them
(define new-variable
  (lambda (var-name value) (cons var-name value)))

(define (var-exists? var-name variables) (if (assoc var-name variables) #t #f)) ; Checks if a variable with the inputted name exists within a given layer
(define (var-exists*? var-name layers) (ormap (lambda (k) (var-exists? var-name k)) layers)) ; Checks if a variable with the inputted name exists in general
(define (is-function? var-name layers) (list? (get-variable* var-name layers))) ; Checks if the "variable" with the inputted name is a function

; Creates a 3-tuple of a function's formal parameters, body, and environment function to represent its closure
(define create-closure
  (lambda (formal-params body env-func)
    (list (cons formal-params (cons body env-func)))))

(define (params closure) (car (car closure))) ; Gets the formal parameters from a function's closure
(define (func-body closure) (arg1 (car closure))) ; Gets the function body from a function's closure
(define (env-function closure) (cdr (cdr (car closure)))) ; Gets the environment function from a function's closure

; Adds a new variable with the inputted name and value if it doesn't already exist
(define add-variable
  (lambda (var-name value variables)
    (cond
      ((empty? variables) (list (new-variable var-name value)))
      ((var-exists? var-name variables) (error (string-append "The variable \"" (symbol->string var-name) "\" already exists!")))
      (else (cons (new-variable var-name value) variables)))))

; New version of add-varaible that works with the layers implementation of the program state
(define add-variable*
  (lambda (var-name value layers next)
    (cond
      ((empty? layers) (next (list (list (new-variable var-name value)))))
      ((var-exists? var-name (car layers)) (error (string-append "The variable \"" (symbol->string var-name) "\" already exists!")))
      (else (next (cons (cons (new-variable var-name value) (car layers)) (cdr layers)))))))

(define (value binding) (cdr binding)) ; Gets the "value" part of a name-value binding
(define (name binding) (car binding)) ; Gets the "name" part of a name-value binding

; Gets the value bound to a variable with the inputted name, if it exists
(define get-variable-cps
  (lambda (var-name variables return)
    (cond
      ((empty? variables) (error (string-append "The variable \"" (symbol->string var-name) "\" does not exist! Make sure it has been declared first!")))
      ((eq? (name (car variables)) var-name) (return (value (car variables))))
      (else (get-variable-cps var-name (cdr variables) return)))))
(define get-variable
  (lambda (var-name variables) (get-variable-cps var-name variables values)))

; New version of get-variable that works with the layers implementation of the program state
(define get-variable*
  (lambda (var-name layers)
    (cond
      ((empty? layers) (error (string-append "The variable \"" (symbol->string var-name) "\" does not exist! Make sure it has been declared first!")))
      ((var-exists? var-name (car layers)) (get-variable var-name (car layers)))
      (else (get-variable* var-name (cdr layers))))))    

; Takes the name of an existing variable and its new value and creates a new binding between them to replace the current one
(define set-variable-cps
  (lambda (var-name val variables return)
    (cond
      ((empty? variables) (error (string-append "The variable \"" (symbol->string var-name) "\" must be declared before it can be assigned a value!")))
      ((eq? (name (car variables)) var-name) (return (add-variable var-name val (cdr variables))))
      (else (set-variable-cps var-name val (cdr variables) (lambda (k) (return (cons (car variables) k))))))))
(define set-variable
  (lambda (var-name val variables) (set-variable-cps var-name val variables values)))

; New version of set-variable that works with the layers implementation of the program state
(define set-variable*
  (lambda (var-name val layers next)
    (cond
      ((empty? layers) (error (string-append "The variable \"" (symbol->string var-name) "\" must be declared before it can be assigned a value!")))
      ((var-exists? var-name (car layers)) (next (cons (set-variable var-name val (car layers)) (cdr layers))))
      (else (set-variable* var-name val (cdr layers) (lambda (k) (next (cons (car layers) k))))))))
