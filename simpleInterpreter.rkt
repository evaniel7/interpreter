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

(define (class-functions class-closure) (arg2 class-closure)) ; Gets the list of functions from a class closure

; Extracts bindings of the specified type (i.e. var or function) from the inputted class body
(define get-class-members-of-type
  (lambda (type class-body)
    (filter
      (lambda (k) (eq? (get-type (value k)) type))
      (car (interpret-raw-code* class-body '() value-state values (lambda (v s) (error "Uncaught exception:" v)))))))

(define (get-class-fields class-body)    (get-class-members-of-type 'var      class-body)) ; Gets the name-value binding of every variable in the inputted class body
(define (get-class-functions class-body) (get-class-members-of-type 'function class-body)) ; Gets the name-closure binding of every function in the inputted class body

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
           (written-vars (get-assigned-vars body))
           (param-layer (bind-formal-params formal-params))
           (func-layer (foldl (lambda (k acc)
           (if (and (atom? k)
                                         (not (member k formal-params))
                                         (not (var-exists? k acc))
                                         (var-exists*? k outer-state)
                                         (not (null? (get-variable* k outer-state)))
                                         (and (member k body-atoms)
                                              (not (member k written-vars))
                                              (not (is-function? k outer-state))))
                                    (cons (new-variable k (get-variable* k outer-state)) acc)
                                    acc))
                              '()
                              (append body-atoms (flatten outer-state)))))
      (lambda (call-time-state) (append (list param-layer func-layer) call-time-state)))))

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
           (instance      (get-variable* instance-name layers)))
      (set-variable-cps field-name 
                        new-val 
                        (cadr instance) 
                        (lambda (_) (next layers))))))

; Updates the program's variable layers by executing the inputted statement, or returning its associated value if it is a "return" statement
(define interpret-statement*
  (lambda (statement layers next return continue break throw)
    (cond
      ((null? statement) (next layers))
      ((class-def? statement) (add-variable*
        (arg1 statement)
        (list (create-class-closure
               (if (empty? (arg2 statement)) null (arg1 (arg2 statement)))
               (get-class-fields (arg3 statement))
               (get-class-functions (arg3 statement))))
        layers
        next))
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
      (else (error "The following statement could not be parsed: " statement)))))

; Collects ALL instance fields. Child fields are at the front, Parent fields at the back.
(define get-inherited-fields
  (lambda (classname layers)
    (if (null? classname)
        '()
        (let* ((class-closure  (car (get-variable* classname layers)))
               (parent-name    (car class-closure))
               (own-fields     (cadr class-closure))
               (parent-fields  (get-inherited-fields parent-name layers)))
            (append own-fields parent-fields)))))

; Collects all methods from the full class hierarchy. Own methods take priority
(define get-all-methods
  (lambda (classname layers)
    (if (null? classname)
        '()
        (let* ((class-closure   (car (get-variable* classname layers)))
               (parent-name     (car class-closure))
               (own-methods     (class-functions class-closure))
               (parent-methods  (get-all-methods parent-name layers)))
          (foldl (lambda (binding acc)
                   (if (var-exists? (name binding) acc)
                       acc
                       (append acc (list binding))))
                 own-methods
                 parent-methods)))))

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
      (lambda (brk-s) (run-finally finally brk-s (lambda (fs) (break fs)) return continue break throw))
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
          (lambda (ret-val ret-s) (run-finally finally ret-s (lambda (fs) (return ret-val fs)) return continue break throw))
          continue
          break
          (lambda (thr-val thr-s) (run-finally finally thr-s (lambda (fs) (throw thr-val fs)) return continue break throw))))))))

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
      (let ((fresh-fields (map (lambda (f) (new-variable (name f) (value f))) (get-inherited-fields classname layers))))
        (cc (create-instance-closure classname fresh-fields) layers))
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
              (error (string-append
                      "The field \"" (symbol->string fieldname)
                      "\" does not exist in the instance \"" (symbol->string instance-expression)
                      "\" of class " (symbol->string (get-type (get-variable* instance-expression layers))) "!")))))
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
    (if (pair? name)
      (call-dot-function name inputs layers cc throw)
      (if (and (var-exists*? name layers) (is-function? name layers))
        (let* ((closure  (get-variable* name layers))
               (func-env ((env-function closure) layers))
               (env      (cons '() func-env)))
          (compute-params
            (params closure)
            inputs
            layers
            env
            (lambda (env)
              (interpret-raw-code* (func-body closure) (remove-param-placeholders env)
                (lambda (v s) (cc v (propagate-mutations layers s)))
                (lambda (s)  (cc null (propagate-mutations layers s)))
                (lambda (v s) (throw v (propagate-mutations layers s)))))
            throw))
        (error (string-append "The function \"" (symbol->string name) "()\" has not yet been defined!"))))))

; Handles dot operator-based function calls of the form "super.[function]" (i.e. superclass function calls)
(define call-super-function
  (lambda (name inputs layers cc throw)
    (let* ((instance        (get-variable* 'this layers))
           (runtime-class   (car instance))
           (current-context (if (var-exists*? '%context layers) (get-variable* '%context layers) runtime-class))
           (parent-class    (car (car (get-variable* current-context layers))))
           (method-info     (find-method-in-chain name parent-class layers))
           (defining-class  (car method-info))
           (all-field-count (length (get-inherited-fields runtime-class layers)))
           (def-field-count (length (get-inherited-fields defining-class layers)))
           (scoped-fields   (list-tail (cadr instance) (- all-field-count def-field-count)))
           (runtime-methods  (get-all-methods runtime-class layers))
           (def-methods      (get-all-methods defining-class layers))
           (method-list      (cons (assoc name def-methods)
                               (filter (lambda (b) (not (eq? (car b) name)))
                                       runtime-methods)))
           (method-layer     (append scoped-fields
                                 (cons (new-variable 'this instance)
                                 (cons (new-variable '%context defining-class)
                                       method-list)))))
      (call-function name inputs (cons method-layer layers) cc throw))))

; Handles function calls of the form "this.[function]" (i.e. class function calls)
(define call-this-function
  (lambda (instance-expr name inputs layers cc throw)
    (return-value* instance-expr layers (lambda (instance post-eval-layers)
      (let* ((runtime-class   (car instance))
             (method-info     (find-method-in-chain name runtime-class post-eval-layers))
             (defining-class  (car method-info))
             (closure         (value (cdr method-info)))
             (all-field-count (length (get-inherited-fields runtime-class post-eval-layers)))
             (def-field-count (length (get-inherited-fields defining-class post-eval-layers)))
             (field-offset    (- all-field-count def-field-count))
             (scoped-fields   (list-tail (cadr instance) field-offset))
             (method-layer    (cons (new-variable 'this instance)
                               (cons (new-variable '%context defining-class)
                                     (get-all-methods runtime-class post-eval-layers))))
             (call-env        (cons (bind-formal-params (params closure))
                               (cons scoped-fields
                                 (cons method-layer post-eval-layers)))))
        (compute-params
          (params closure)
          inputs
          post-eval-layers
          call-env
          (lambda (env)
            (interpret-raw-code*
              (func-body closure)
              (remove-param-placeholders env)
              (lambda (return-val post-method-layers) (update-instance-and-return
                  return-val
                  post-method-layers
                  instance
                  instance-expr
                  scoped-fields
                  field-offset
                  all-field-count
                  runtime-class
                  post-eval-layers
                  cc))
              (lambda (s) (cc null (propagate-mutations post-eval-layers s)))
              (lambda (v s)
                (update-instance-and-throw v s instance instance-expr scoped-fields runtime-class post-eval-layers throw))))
          throw)))
    throw)))

; Helper function that ensures the proper updating of instance fields when a method returns normally
(define update-instance-and-return
  (lambda (return-val post-method-layers instance instance-expr scoped-fields field-offset all-field-count runtime-class post-eval-layers cc)
    (let* ((updated-fields   (append (take (cadr instance) field-offset)
                                     scoped-fields
                                     (list-tail (cadr instance) all-field-count)))
           (updated-instance (create-instance-closure runtime-class updated-fields))
           (propagated       (propagate-mutations post-eval-layers post-method-layers)))
      (cond
        ((atom? instance-expr)
         (set-variable* instance-expr updated-instance propagated
                        (lambda (s) (cc return-val s))))
        ((dot-operator? instance-expr)
         (dot-assign instance-expr updated-instance propagated
                     (lambda (s) (cc return-val s))))
        (else
         (cc return-val propagated))))))

; Helper function for call-this-function that ensures the proper updating of instance fields when an exception is thrown
(define update-instance-and-throw
  (lambda (v s instance instance-expr scoped-fields runtime-class post-eval-layers throw)
    (let* ((updated-instance  (create-instance-closure runtime-class scoped-fields))
           (propagated        (propagate-mutations post-eval-layers s)))
      (cond
        ((atom? instance-expr)
         (set-variable* instance-expr updated-instance propagated
                        (lambda (s2) (throw v s2))))
        ((dot-operator? instance-expr)
         (dot-assign instance-expr updated-instance propagated
                     (lambda (s2) (throw v s2))))
        (else
         (throw v propagated))))))

; Handles function calls that are performed via the dot operator
(define call-dot-function
  (lambda (name inputs layers cc throw)
    (if (eq? (arg1 name) 'super)
      (call-super-function (arg2 name) inputs layers cc throw)
      (call-this-function  (arg1 name) (arg2 name) inputs layers cc throw))))

; Returns (DefiningClassName . MethodBinding)
(define find-method-in-chain
  (lambda (name classname layers)
    (let* ((class-closure (car (get-variable* classname layers)))
           (parent        (car class-closure))
           (methods       (caddr class-closure)) 
           (match         (assoc name methods)))
      (cond
        (match (cons classname match)) 
        ((null? parent)
         (let ((fallback (assoc name (get-all-methods (car (get-variable* 'this layers)) layers))))
           (if fallback
               (cons (car (get-variable* 'this layers)) fallback)
               (error "Method not found:" name))))
        (else (find-method-in-chain name parent layers))))))

; Removes parameter placeholder bindings created by bind-formal-params
(define remove-param-placeholders
  (lambda (layers)
    (map (lambda (layer)
           (filter (lambda (binding)
                     (not (equal? (value binding) '(()))))
                   layer))
         layers)))

; Updates the caller's layers with any changes made to shared variables during the function call
(define propagate-mutations
  (lambda (caller-layers post-call-layers)
    (if (or (null? caller-layers) (null? post-call-layers))
        caller-layers
        (let* ((caller-depth (length caller-layers))
               (post-depth   (length post-call-layers))
               (offset       (- post-depth caller-depth))
               (aligned-post (list-tail post-call-layers offset)))
          (for-each
           (lambda (caller-layer post-layer)
             (for-each
              (lambda (binding)
                (when (and (pair? binding) (var-exists? (name binding) post-layer))
                  (set-box! (cdr binding)
                            (get-variable (name binding) post-layer))))
              caller-layer))
           caller-layers
           aligned-post)
          caller-layers))))

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

; New version of add-variable that works with the layers implementation of the program state
(define add-variable*
  (lambda (var-name value layers next)
    (cond
      ((empty? layers) (next (list (list (new-variable var-name value)))))
      ((var-exists? var-name (car layers)) (error (string-append "The variable \"" (symbol->string var-name) "\" already exists!")))
      (else (next (cons (cons (new-variable var-name value) (car layers)) (cdr layers)))))))

; Takes a name and a value and creates a binding between them
(define new-variable
  (lambda (var-name value) (cons var-name (box value))))

(define (value binding) (unbox (cdr binding))) ; Gets the "value" part of a name-value binding
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
      ((eq? (name (car variables)) var-name)
       (begin
         (set-box! (cdr (car variables)) val)
         (return variables))) 
      (else (set-variable-cps var-name val (cdr variables) (lambda (k) (return (cons (car variables) k))))))))

; New version of set-variable that works with the layers implementation of the program state
(define set-variable*
  (lambda (var-name val layers next)
    (cond
      ((empty? layers) 
       (error (string-append "The variable \"" (symbol->string var-name) "\" must be declared before it can be assigned a value!")))
      ((var-exists? var-name (car layers))
         (set-box! (cdr (get-binding var-name (car layers))) val)
         (next layers))
      (else 
       (set-variable* var-name val (cdr layers) 
                      (lambda (updated-layers) 
                        (next (cons (car layers) updated-layers))))))))

(define (get-binding var-name layer)
  (cond
    ((empty? layer) #f)
    ((eq? var-name (car (car layer))) (car layer))
    (else (get-binding var-name (cdr layer)))))

; Helper to run a single test safely
(define run-test
  (lambda (label filename classname)
    (display label)
      (with-handlers ([exn? (lambda (e) (writeln (exn-message e)))])
        (writeln (interpret* filename classname)))))

; Runs every test for Project 4 at once
(define test-all
  (lambda ()
      (run-test "Test 1: " "test4-1.rkt" 'A)
      (run-test "Test 2: " "test4-2.rkt" 'A)
      (run-test "Test 3: " "test4-3.rkt" 'A)
      (run-test "Test 4: " "test4-4.rkt" 'A)
      (run-test "Test 5: " "test4-5.rkt" 'A)
      (run-test "Test 6: " "test4-6.rkt" 'A)
      (run-test "Test 7: " "test4-7.rkt" 'C)
      (run-test "Test 8: " "test4-8.rkt" 'Square)
      (run-test "Test 9: " "test4-9.rkt" 'Square)
      (run-test "Test 10: " "test4-10.rkt" 'List)
      (run-test "Test 11: " "test4-11.rkt" 'List)
      (run-test "Test 12: " "test4-12.rkt" 'List)
      (run-test "Test 13: " "test4-13.rkt" 'C)))
