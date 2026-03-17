#lang racket

(require "simpleParser.rkt")

; Checks if a list item is an atom (i.e. a non-null, non-list object)
(define (atom? x)
  (and (not (null? x))
       (not (pair? x))))

; Interprets the code contained in the file with the inputted filename
(define interpret
  (lambda (filename) (interpret-raw-code (parser filename) '())))

; Replaces "#t" with "true" and "#f" with "false", but leaves the inputted value untouched otherwise
(define translate-booleans
  (lambda (output)
    (if (boolean? output) (if (eq? output #t) 'true 'false) output)))

; Interprets the inputted pre-parsed code one statement at a time, or returns the value of the current statement if it is a "return" statement 
(define interpret-raw-code
  (lambda (code variables)
    (cond
      ((null? code) variables)
      ((return? (car code)) (translate-booleans (return-value (interpret-statement (car code) variables) variables)))
      ((list? (car code)) (interpret-raw-code (cdr code) (interpret-statement (car code) variables)))
      (else code))))

; Shortcuts for checking if a statement declares a variable, assigns a value to one, or returns a value
(define (declaration? statement) (eq? 'var (car statement)))
(define (assignment? statement) (eq? '= (car statement)))
(define (return? statement) (eq? 'return (car statement)))

(define (math? statement) (set-member? (set '+ '- '* '/ '%) (car statement))) ; Checks if the statement is just simple arithemetic 
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

(define (boolean-expression? statement) (set-member? (set '&& '|| '!) (car statement))) ; Checks if the statement is a simple boolean expression
; Evaluates the boolean expression formed by the boolean input(s) and the inputted connective
(define (boolean connective arg1 arg2)
  (cond
    ((eq? connective '&&) (and arg1 arg2))
    ((eq? connective '||) (or arg1 arg2))
    ((eq? connective '!) (not arg1)) ; Logical "not" only needs the first argument, so the second one is ignored if it exists
    (else #f)))

(define (comparison? statement) (set-member? (set '== '!= '< '<= '> '>=) (car statement))) ; Checks if the statement is comparing two values
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

; Interprets simple statements (i.e. expressions) and returns their results
(define return-value
  (lambda (output variables)
    (cond
      ((null? output) null)
      ((number? output) output)
      ((boolean? output) output)
      ((eq? 'true output) #t)
      ((eq? 'false output) #f)
      ((atom? output) (get-variable output variables))
      ((math? output) (do-math (car output) (return-value (arg1 output) variables) (return-value (arg2 output) variables)))
      ((comparison? output) (compare (car output) (return-value (arg1 output) variables) (return-value (arg2 output) variables)))
      ((boolean-expression? output) (boolean (car output) (return-value (arg1 output) variables) (return-value (arg2 output) variables)))
      (else (return-value (car output) variables)))))

; Shortcuts to get the 1st, 2nd, and 3rd arguments of a statement, whenever they exist
(define (arg1 statement) (car (cdr statement))) 
(define (arg2 statement) (if (empty? (cdr (cdr statement))) null (car (cdr (cdr statement)))))
(define (arg3 statement) (arg2 (cdr statement)))

(define (if-statement? statement) (eq? 'if (car statement))) ;Checks if the inputted statement is an "if" statement
; Executes the inputted "if" statement and updates the program's variables accordingly
(define if-statement
  (lambda (condition if-true else variables)
    (if (not (list? condition))
        (error "Conditions in if statements must be enclosed in parentheses!")
        (if (return-value condition variables) (interpret-statement if-true variables) (interpret-statement else variables)))))

(define (while-statement? statement) (eq? 'while (car statement))) ; Checks if the inputted statement is a "while" statement
; Executes the inputted "while" statement and updates the program's variables accordingly
(define while-statement-with-break
  (lambda (condition body variables break)
    (if (not (list? condition))
        (error "Conditions in while statements must be enclosed in parentheses!")
        (if (return-value condition variables)
            (while-statement-with-break condition body (interpret-statement body variables) break)
            (break variables)))))

(define while-statement (lambda (condition body variables) (while-statement-with-break condition body variables (lambda (v) v))))

; Updates the program's variables by executing the inputted statement, or returning its associated value if it is a "return" statement
(define interpret-statement
  (lambda (statement variables)
    (cond
      ((null? statement) variables)
      ((declaration? statement) (add-variable (arg1 statement) (return-value (arg2 statement) variables) variables))
      ((assignment? statement) (set-variable (arg1 statement) (return-value (arg2 statement) variables) variables))
      ((if-statement? statement) (if-statement (arg1 statement) (arg2 statement) (arg3 statement) variables))
      ((while-statement? statement) (while-statement (arg1 statement) (arg2 statement) variables))
      ((return? statement) (return-value (cdr statement) variables))
      (else (error "Statement could not be parsed!")))))

; Takes a name and a value and creates a binding between them
(define new-variable
  (lambda (var-name value) (cons var-name value)))

(define (var-exists? var-name variables) (if (assoc var-name variables) #t #f)) ; Checks if a given variable exists

; Adds a new variable with the inputted name and value if it doesn't already exist
(define add-variable
  (lambda (var-name value variables)
    (cond
      ((empty? variables) (list (new-variable var-name value)))
      ((var-exists? var-name variables) (error "The variable you are trying to declare already exists!"))
      (else (cons (new-variable var-name value) variables)))))

(define (value binding) (cdr binding)) ; Gets the "value" part of a name-value binding
(define (name binding) (car binding)) ; Gets the "name" part of a name-value binding

; Gets the value bound to a variable with the inputted name, if it exists
(define get-variable-cps
  (lambda (var-name variables return)
    (cond
      ((empty? variables) (error "The variable does not exist! Make sure it has been declared first!"))
      ((eq? (name (car variables)) var-name) (return (value (car variables))))
      (else (get-variable-cps var-name (cdr variables) return)))))

(define get-variable
  (lambda (var-name variables) (get-variable-cps var-name variables (lambda (v) v))))

; Takes the name of an existing variable and its new value and creates a new binding between them to replace the current one
(define set-variable-cps
  (lambda (var-name val variables return)
    (cond
      ((empty? variables) (error "Variables must be declared before they can be assigned values!"))
      ((eq? (name (car variables)) var-name) (return (add-variable var-name val (cdr variables))))
      (else (set-variable-cps var-name val (cdr variables) (lambda (k) (return (cons (car variables) k))))))))

(define set-variable
  (lambda (var-name val variables) (set-variable-cps var-name val variables (lambda (v) v))))
