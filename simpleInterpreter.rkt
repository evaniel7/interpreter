#lang racket

(require "classParser.rkt")
(require racket/trace) ; Enables the use of the "trace" function (for debugging purposes)

; Interprets the code contained in the file with the inputted filename
(define interpret*
  (lambda (filename classname)
    (translate-booleans (call-main (interpret-raw-code* (parser filename) '() value-state values (lambda (v s) (error "Uncaught exception:" v))) classname))))

; Assembles the closure for the specified class
(define create-class-closure
  (lambda (superclass instance-fields functions)
    (cons superclass (cons instance-fields (list functions)))))

; Assembles the closure for an instance of the specified class
(define create-instance-closure
  (lambda (class instance-field-vals)
    (cons class (list instance-field-vals))))

(define (class-super class-closure) (car class-closure))
(define (class-fields class-closure) (cadr class-closure))
(define (class-functions class-closure) (caddr class-closure))

; Gets the name-closure binding of every function in the inputted class body
(define get-class-functions
  (lambda (class-body)
    (filter
      (lambda (k)
        (match (value k)
          [(list _ _ _) #t]
          [_ #f]))
      (car (interpret-raw-code* class-body '() value-state values
                                (lambda (v s) (error "Uncaught exception:" v)))))))
; Gets the name-value binding of every variable in the inputted class body
(define get-class-fields
  (lambda (class-body)
    (filter
      (lambda (k) (eq? (get-type (value k)) 'var))
      (car (interpret-raw-code* class-body '() value-state values (lambda (v s) (error "Uncaught exception:" v)))))))

; Replaces "#t" with "true" and "#f" with "false", but leaves the inputted value untouched otherwise
(define translate-booleans
  (lambda (output)
    (if (boolean? output) (if (eq? output #t) 'true 'false) output)))

; Calls the main() function of the inputted class and returns its output
(define call-main
  (lambda (classdefs classname)
    (if (var-exists*? classname classdefs)
        (let* ((class-contents (list (class-functions (car (get-variable* classname classdefs))))))
          (if (var-exists*? 'main class-contents)
            (call-function 'main '() (append class-contents classdefs) value-state (lambda (v s) (error "Uncaught exception:" v)))
            (error "No main() function has been defined in the code for class:" classname)))
        (error (string-append "The class \"" (symbol->string classname) "\" does not exist!")))))

; Interprets the inputted pre-parsed code one statement at a time, or returns the value of the current statement if it is a "return" statement 
(define interpret-raw-code*
  (lambda (code layers return fallthrough throw)
    (cond
      ((null? code) (fallthrough layers))
      (else (interpret-statement*
        (car code)
        layers
        (lambda (v) (interpret-raw-code* (cdr code) v return fallthrough throw))
        return
        (lambda (layers) (error "Continue statements must be inside of a loop!"))
        (lambda (layers) (error "Break statements must be inside of a loop!"))
        throw)))))

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

(define (class-def? statement) (eq? 'class (car statement))) ; Checks if a statement is defining a class
(define (static-f-def? statement) (eq? 'static-function (car statement))) ; Checks if a statement is defining a static function
(define (new? statement) (eq? 'new (car statement))) ; Checks if a statement is creating a new class instance
(define (dot-operator? statement) (eq? 'dot (car statement))) ; Checks if a statement is calling upon a class variable, function or inner class

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
    (let* ((body-atoms (flatten body))
           (written-vars (get-assigned-vars body)) ; variables assigned anywhere in body
           (param-layer (bind-formal-params formal-params))
           (func-layer (foldl (lambda (k acc)
                                (if (and (atom? k)
                                         (not (member k formal-params))
                                         (not (var-exists? k acc))
                                         (var-exists*? k outer-state)
                                         (or (is-function? k outer-state)
                                             (and (member k body-atoms)
                                                  (not (member k written-vars))))) ; read-only
                                    (cons (new-variable k (get-variable* k outer-state)) acc)
                                    acc))
                              '()
                              (append body-atoms (flatten outer-state)))))
      (lambda (call-time-state) (list param-layer func-layer)))))

; Helper function for getting only assigned variables from the function body
(define get-assigned-vars
  (lambda (body)
    (foldl (lambda (stmt acc)
             (cond
               ((and (pair? stmt) (assignment? stmt)) (cons (arg1 stmt) acc))
               ((pair? stmt) (append (get-assigned-vars stmt) acc))
               (else acc)))
           '()
           body)))

; Helper function that allows for statements of the form "this.[field name]" to be assigned a value
(define dot-assign
  (lambda (dot-expr new-val layers next)
    (let* ((instance-name (arg1 dot-expr))
           (field-name    (arg2 dot-expr))
           (instance      (get-variable* instance-name layers))
           (updated-instance (create-instance-closure
                               (car instance)
                               (set-variable field-name new-val (cadr instance)))))
      (set-variable* instance-name updated-instance layers next))))

; Updates the program's variable layers by executing the inputted statement, or returning its associated value if it is a "return" statement
(define interpret-statement*
  (lambda (statement layers next return continue break throw)
    (cond
      ((null? statement) (next layers))
      ((class-def? statement)
       (let* ([class-name (arg1 statement)]
        [parent-name (if (null? (arg2 statement))
                         null
                         (arg1 (arg2 statement)))]
        [class-closure
         (create-class-closure
          parent-name
          (get-class-fields (arg3 statement))
          (get-class-functions (arg3 statement)))])
         (add-variable* class-name
                  (list class-closure)
                  layers
                  next)))
      ((block? statement) (execute-block (cdr statement) (new-layer layers) next return continue break throw))
      ((try? statement) (try-catch-block (arg1 statement) (arg2 statement) (arg3 statement) layers next return continue break throw))
      ((throw? statement) (return-value* (cdr statement) layers (lambda (k s) (throw k s)) throw))
      ((continue? statement) (continue layers))
      ((break? statement) (break layers))
      ((function-call? statement) (call-function (arg1 statement) (cdr (cdr statement)) layers (lambda (v s) (next s)) throw))
      ((declaration? statement) (return-value* (arg2 statement) layers (lambda (k s) (add-variable* (arg1 statement) k s next)) throw))
      ((assignment? statement) (return-value*
        (arg2 statement)
        layers
        (lambda (k s) (if (pair? (arg1 statement))
          (dot-assign (arg1 statement) k s next)
          (set-variable* (arg1 statement) k s next)))
        throw))
      ((if-statement? statement) (if-statement* (arg1 statement) (arg2 statement) (arg3 statement) layers next return continue break throw))
      ((while-statement? statement) (while-statement* (arg1 statement) (arg2 statement) layers next return continue break throw))
      ((return? statement) (return-value* (cdr statement) layers (lambda (k s) (return k s)) throw))
      ((function-def? statement) (add-variable*
        (arg1 statement)
        (create-closure (arg2 statement) (arg3 statement) (construct-environment (arg2 statement) (arg3 statement) layers))
        layers
        next))
      ((static-f-def? statement) (add-variable*
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
    (return-value*
      condition
      layers
      (lambda (condition-result side-effect) (if condition-result
        (interpret-statement* if-true side-effect next return continue break throw)
        (interpret-statement* else side-effect next return continue break throw)))
      throw)))

; Executes the inputted "while" statement and updates the program's variable layers accordingly
(define while-statement*
  (lambda (condition body layers next return continue break throw)
    (return-value*
      condition
      layers
      (lambda (condition-result side-effect) (if condition-result
        (interpret-statement*
          body
          side-effect
          (lambda (new-layers) (while-statement* condition body new-layers next return continue break throw))
          return
          (lambda (new-layers) (while-statement* condition body new-layers next return continue break throw))
          next
          throw)
        (next side-effect)))
      throw)))

; Interprets simple statements (i.e. expressions) and returns their results
(define return-value*
  (lambda (output layers cc throw)
    (cond
      ((null? output) (cc null layers))
      ((number? output) (cc output layers))
      ((boolean? output) (cc output layers))
      ((eq? 'true output) (cc #t layers))
      ((eq? 'false output) (cc #f layers))
      ((eq? output 'super) (cc (get-variable* 'this layers) layers))
      ((atom? output) (cc (get-variable* output layers) layers))
      ((math? output) (return-value*
          (arg1 output)
          layers
          (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (do-math (car output) k1 k2) s2)) throw))
          throw))
      ((comparison? output) (return-value*
          (arg1 output)
          layers
          (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (compare (car output) k1 k2) s2)) throw))
          throw))
      ((boolean-expression? output) (return-value*
          (arg1 output)
          layers
          (lambda (k1 s1) (return-value* (arg2 output) s1 (lambda (k2 s2) (cc (boolean (car output) k1 k2) s2)) throw))
          throw))
      ((assignment? output) (return-value*
          (arg2 output)
          layers
          (lambda (k s) (if (pair? (arg1 output))
            (dot-assign (arg1 output) k s (lambda (updated-layers) (cc k updated-layers)))
            (set-variable* (arg1 output) k s (lambda (updated-layers) (cc k updated-layers)))))
          throw))
      ((function-call? output) (call-function (arg1 output) (cdr (cdr output)) layers (lambda (v s) (cc v s)) throw))
      ((new? output) (instantiate-class (arg1 output) layers cc throw))
      ((dot-operator? output) (access-class-field (arg1 output) (arg2 output) layers cc throw))
      (else (return-value* (car output) layers cc throw)))))

; Creates a new instance of the specified class and returns an error if the class does not exist
(define instantiate-class
  (lambda (classname layers cc throw)
    (if (var-exists*? classname layers)
        (cc (create-instance-closure classname (cadr (car (get-variable* classname layers)))) layers)
        (error (string-append "The class \"" (symbol->string classname) "\" does not exist!")))))

; Gets the value of a class instance field that is being accessed via the dot operator
(define access-class-field
  (lambda (instance-expression fieldname layers cc throw)
    (return-value*
      instance-expression
      layers
      (lambda (instance post-eval-layers)
        (let* ((field-vals (cadr instance)))
          (if (var-exists*? fieldname (list field-vals))
            (cc (get-variable fieldname field-vals) post-eval-layers)
            (error (string-append "Field \"" (symbol->string fieldname) "\" does not exist in this class instance!")))))
      throw)))

; Computes the values of the parameters inputted into a function call and binds them to the formal parameters in the function environment
(define compute-params
  (lambda (params inputs layers environment cc throw)
    (cond
      ((and (null? params) (null? inputs)) (cc environment))
      ((or (null? params) (null? inputs))
       (error "Mismatched number of arguments in function call!"))
      (else
        (return-value*
          (car inputs)
          layers
          (lambda (v s) (set-variable*
            (car params)
            v
            environment
            (lambda (updated-env) (compute-params (cdr params) (cdr inputs) layers updated-env cc throw))))
          throw)))))

; Calls the function with the specified name and evaluates it with the specified values for its parameters
(define call-function
  (lambda (name inputs layers cc throw)
    (if (pair? name) ; Detects dot operator-based function call (currently the only case where the name is a list)
      (return-value*
         (arg1 name)
         layers  
         (lambda (instance post-eval-layers)
           (let* ((class-closure (car (get-variable* (car instance) post-eval-layers)))
                  (method-layer (cons (new-variable 'this instance)
                  (class-functions class-closure))))
           (call-function
             (arg2 name)
             inputs
             (cons method-layer post-eval-layers)
             (lambda (v post-layers)
               (if (symbol? (arg1 name)) ; Only write back if instance was a named variable
                 (set-variable*
                   (arg1 name)
                   (get-variable* 'this post-layers)
                   (propagate-mutations post-eval-layers post-layers)
                   (lambda (final-layers) (cc v final-layers)))
                 (cc v (propagate-mutations post-eval-layers post-layers))))
             throw)))
         throw)
      (if (and (var-exists*? name layers) (is-function? name layers))
          (let* ((closure (get-variable* name layers))
                 (func-env ((env-function closure) layers))
                 (env (cons '() (append func-env layers))))
          (compute-params
            (params closure)
            inputs
            layers
            env
            (lambda (env)
              (interpret-raw-code* (func-body closure) (remove-param-placeholders env)
                (lambda (v s)
                  (cc v (propagate-mutations layers s)))
                (lambda (s)
                  (cc null (propagate-mutations layers s)))
                (lambda (v s)
                  (throw v (propagate-mutations layers s)))))
            throw))
        (error (string-append "The function \"" (symbol->string name) "()\" has not yet been defined!"))))))

; Removes parameter placeholder bindings created by bind-formal-params
(define remove-param-placeholders
  (lambda (layers)
    (map (lambda (layer)
           (filter (lambda (binding)
                     (not (equal? (cdr binding) '(()))))
                   layer))
         layers)))

; Updates the caller's layers with any changes made to shared variables during the function call
(define propagate-mutations
  (lambda (caller-layers post-call-layers)
    (if (or (null? caller-layers) (null? post-call-layers))
        caller-layers
        (let* ((caller-depth (length caller-layers))
               (post-depth (length post-call-layers))
               (offset (- post-depth caller-depth))
               (aligned-post (list-tail post-call-layers offset)))
          (map (lambda (caller-layer post-layer)
                 (map (lambda (binding)
                        (if (and (pair? binding) (var-exists? (name binding) post-layer))
                            (new-variable (name binding) (get-variable (name binding) post-layer))
                            binding))
                      caller-layer))
               caller-layers
               aligned-post)))))

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
(define (is-function? var-name layers) (eq? (get-type (get-variable* var-name layers)) 'function)) ; Checks if the "variable" with the inputted name is a function

; Gets the type of the variable associated with the inputted value based on the value's structure
(define (get-type var-value)
  (match var-value
    [(list _ _ _) 'function]
    [(list class _) class]
    [_ 'var]))

; Creates a 3-tuple of a function's formal parameters, body, and environment function to represent its closure
(define create-closure
  (lambda (formal-params body env-func)
    (list formal-params body env-func)))

(define (params closure) (car closure)) ; Gets the formal parameters from a function's closure
(define (func-body closure) (cadr closure)) ; Gets the function body from a function's closure
(define (env-function closure) (caddr closure)) ; Gets the environment function from a function's closure

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
(define get-variable*
  (lambda (var-name layers)
    (letrec ([lookup
              (lambda (ls)
                (cond
                  [(empty? ls)
                   (if (and (not (eq? var-name 'this))
                            (var-exists*? 'this layers)
                            (var-exists? var-name (cadr (get-variable* 'this layers))))
                       (get-variable var-name (cadr (get-variable* 'this layers)))
                       (error (string-append "The variable \""
                                             (symbol->string var-name)
                                             "\" does not exist! Make sure it has been declared first!")))]
                  [(var-exists? var-name (car ls))
                   (get-variable var-name (car ls))]
                  [else (lookup (cdr ls))]))])
      (lookup layers))))
(define get-variable
  (lambda (var-name variables)
    (get-variable* var-name (list variables))))

; Takes the name of an existing variable and its new value and creates a new binding between them to replace the current one
(define set-variable*
  (lambda (var-name val layers next)
    (letrec ([update-this-field
              (lambda ()
                (let* ([this-obj (get-variable* 'this layers)]
                       [updated-this
                        (create-instance-closure
                         (car this-obj)
                         (set-variable var-name val (cadr this-obj)))])
                  (set-variable* 'this updated-this layers next)))]
             [set-helper
              (lambda (ls rebuild)
                (cond
                  [(empty? ls)
                   (if (and (var-exists*? 'this layers)
                            (var-exists? var-name (cadr (get-variable* 'this layers))))
                       (update-this-field)
                       (error (string-append "The variable \""
                                             (symbol->string var-name)
                                             "\" must be declared before it can be assigned a value!")))]
                  [(var-exists? var-name (car ls))
                   (next (rebuild
                          (cons (set-variable var-name val (car ls))
                                (cdr ls))))]
                  [else
                   (set-helper
                    (cdr ls)
                    (lambda (rest) (rebuild (cons (car ls) rest))))]))])
      (set-helper layers values))))
(define set-variable
  (lambda (var-name val variables)
    (car (set-variable* var-name val (list variables) values))))

; Helper to run a single test safely
(define run-test
  (lambda (label filename classname)
    (begin
      (display label)
      (with-handlers ([exn? (lambda (e) (writeln (exn-message e)))])
        (writeln (interpret* filename classname))))))
