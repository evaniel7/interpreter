#lang racket
(require "classParser.rkt")
(provide (all-defined-out))

; Assembles the closure for the specified class
(struct cls (name super fields methods static-methods) #:transparent)
(struct mth (params body owner static?) #:transparent)
(struct obj (class fields) #:transparent)
(struct ret (v) #:transparent)
(struct brk () #:transparent)
(struct cont () #:transparent)
(struct thrown (v) #:transparent)
(struct lfun (params body env this current-class) #:transparent)

(define classes (make-hash))
; Evaluates boolean truth for control flow and logical operators
(define (truth v) (and v (not (eq? v 'false))))
; Replaces "#t" with "true" and "#f" with "false", but leaves the inputted value untouched otherwise
(define (out v) (cond ((eq? v #t) 'true) ((eq? v #f) 'false) (else v)))
(define (sym x) (if (string? x) (string->symbol x) x))
(define (binding v) (box v))
(define (new-env) (list (make-hash)))
(define (push env) (cons (make-hash) env))
; Takes a name and a value and creates a binding between them
(define (declare! env n v) (hash-set! (car env) n (binding v)))
(define (local-box env n)
  (let loop ((e env))
    (cond ((null? e) #f)
          ((hash-has-key? (car e) n) (hash-ref (car e) n))
          (else (loop (cdr e))))))
(define (class-of n)
  (hash-ref classes n (lambda () (error 'interpret (format "Unknown class ~a" n)))))

; Interprets the top-level parsed code, which should contain only class definitions
; Gets the name-value binding of every variable and function in each class body
(define (install-classes! ast)
  (set! classes (make-hash))
  (for ((c ast))
    (match c
      (`(class ,name ,ext ,body)
       (define super (and (pair? ext) (cadr ext)))
       (define fields '())
       (define methods (make-hash))
       (define statics (make-hash))
       (for ((s body))
         (match s
           (`(var ,n) (set! fields (append fields (list (cons n #f)))))
           (`(var ,n ,e) (set! fields (append fields (list (cons n e)))))
           (`(static-function ,n ,ps ,b) (hash-set! statics n (mth ps b name #t)))
           (`(function ,n ,ps ,b) (hash-set! methods n (mth ps b name #f)))
           (_ (void))))
       (hash-set! classes name (cls name super fields methods statics)))
      (_ (error 'interpret "Top level may contain only classes")))) )

; Builds the superclass-to-subclass chain used when creating object fields
(define (ancestor-chain cname)
  (if (not cname) '()
      (append (ancestor-chain (cls-super (class-of cname))) (list cname))))

; Creates a new instance of the specified class and returns an error if the class does not exist
; Assembles the closure for an instance of the specified class
(define (make-object cname)
  (define h (make-hash))
  (define o (obj cname h))
  (for ((cn (ancestor-chain cname)))
    (for ((f (cls-fields (class-of cn))))
      (hash-set! h (cons cn (car f)) (binding (if (cdr f) (eval-expr (cdr f) (new-env) o cn) 0)))))
  o)

; Looks up a method from a class, searching superclass definitions when needed
(define (find-method cname name (start cname))
  (cond ((not start) #f)
        ((hash-has-key? (cls-methods (class-of start)) name) (hash-ref (cls-methods (class-of start)) name))
        (else (find-method cname name (cls-super (class-of start))))))
; Calls the main() function of the inputted class and returns its output
(define (find-static cname name)
  (cond ((not cname) #f)
        ((hash-has-key? (cls-static-methods (class-of cname)) name) (hash-ref (cls-static-methods (class-of cname)) name))
        (else (find-static (cls-super (class-of cname)) name))))

; Gets the value of a class instance field that is being accessed via the dot operator
(define (field-key o fname start)
  (let loop ((c start))
    (cond ((not c) #f)
          ((hash-has-key? (obj-fields o) (cons c fname)) (cons c fname))
          (else (loop (cls-super (class-of c)))))))
(define (field-box o fname start)
  (define k (field-key o fname start))
  (and k (hash-ref (obj-fields o) k)))

; Gets the value bound to a variable with the inputted name, if it exists
(define (lookup env n this current-class)
  (cond ((eq? n 'this) (or this (error 'interpret "this outside instance method")))
        ((eq? n 'super) (or this (error 'interpret "super outside instance method")))
        ((local-box env n) => unbox)
        ((and this (field-box this n current-class)) => unbox)
        (else (error 'interpret (format "Undefined variable ~a" n)))))
; Takes the name of an existing variable and its new value and updates the current binding
(define (assign! env n v this current-class)
  (cond ((local-box env n) => (lambda (b) (set-box! b v)))
        ((and this (field-box this n current-class)) => (lambda (b) (set-box! b v)))
        (else (error 'interpret (format "Assignment to undeclared variable ~a" n))))
  v)

; Helper function for resolving the left side of a dot operator
(define (eval-dot-left e env this current-class)
  (cond ((eq? e 'super) (values this (cls-super (class-of current-class)) #t))
        ((eq? e 'this) (values this current-class #f))
        (else (define v (eval-expr e env this current-class))
              (unless (obj? v) (error 'interpret "Left side of dot is not an object"))
              (values v (obj-class v) #f))))

; Interprets simple statements (i.e. expressions) and returns their results
(define (eval-expr e env this current-class)
  (cond
    ((number? e) e)
    ((eq? e 'true) #t)
    ((eq? e 'false) #f)
    ((boolean? e) e)
    ((symbol? e) (lookup env e this current-class))
    ((not (pair? e)) e)
    (else
     (match e
       (`(new ,c . ,args) (make-object c))
       (`(dot ,lhs ,name)
        (define-values (o start super?) (eval-dot-left lhs env this current-class))
        (define b (field-box o name start))
        (if b (unbox b) (error 'interpret (format "No field ~a" name))))
       (`(funcall ,name . ,args) (call-any name args env this current-class))
       (`(= ,lhs ,rhs) (define v (eval-expr rhs env this current-class)) (assign-lhs! lhs v env this current-class))
       (`(! ,a) (not (truth (eval-expr a env this current-class))))
       (`(- ,a) (- (eval-expr a env this current-class)))
       (`(,op ,a ,b)
        (define av (eval-expr a env this current-class))
        (define bv (eval-expr b env this current-class))
        (case op
          ((+) (+ av bv)) ((-) (- av bv)) ((*) (* av bv)) ((/) (quotient av bv)) ((%) (remainder av bv))
          ((<) (< av bv)) ((<=) (<= av bv)) ((>) (> av bv)) ((>=) (>= av bv)) ((==) (equal? av bv)) ((!=) (not (equal? av bv)))
          ((&&) (and (truth av) (truth bv))) ((||) (or (truth av) (truth bv)))
          (else (error 'interpret (format "Bad expression ~a" e)))))
       (_ (error 'interpret (format "Bad expression ~a" e)))))))

; Helper function that allows for statements of the form "this.(field name)" to be assigned a value
(define (assign-lhs! lhs v env this current-class)
  (if (and (pair? lhs) (eq? (car lhs) 'dot))
      (let-values (((o start super?) (eval-dot-left (cadr lhs) env this current-class)))
        (define b (field-box o (caddr lhs) start))
        (unless b (error 'interpret (format "No field ~a" (caddr lhs))))
        (set-box! b v) v)
      (assign! env lhs v this current-class)))

; Calls the function with the specified name and evaluates it with the specified values for its parameters
(define (call-any name args env this current-class)
  (cond
    ((and (pair? name) (eq? (car name) 'dot))
     (define-values (o start super?) (eval-dot-left (cadr name) env this current-class))
     (define method (find-method (obj-class o) (caddr name) start))
     (unless method (error 'interpret (format "No method ~a" (caddr name))))
     (call-method method o args env current-class))
    (else
     (cond
       ((local-box env name) => (lambda (b)
                              (define f (unbox b))
                              (if (lfun? f)
                                  (call-lfun f args env this current-class)
                                  (error 'interpret (format "~a is not a function" name)))))
       (this (define method (find-method (obj-class this) name (obj-class this)))
             (unless method (error 'interpret (format "No method ~a" name)))
             (call-method method this args env current-class))
       (else (error 'interpret (format "No function ~a" name)))))))

; Computes the values of the parameters inputted into a function call and binds them to the formal parameters in the function environment
(define (call-lfun f arg-exprs caller-env caller-this caller-class)
  (define env (push (lfun-env f)))
  (for ((p (lfun-params f)) (a arg-exprs))
    (declare! env p (eval-expr a caller-env caller-this caller-class)))
  (with-handlers ((ret? (lambda (r) (ret-v r))))
    (exec-block (lfun-body f) env (lfun-this f) (lfun-current-class f))
    '()))

; Computes the values of the parameters inputted into a method call and binds them to the formal parameters in the method environment
(define (call-method method this-obj arg-exprs caller-env caller-class)
  (define env (new-env))
  (for ((p (mth-params method)) (a arg-exprs))
    (declare! env p (eval-expr a caller-env this-obj caller-class)))
  (with-handlers ((ret? (lambda (r) (ret-v r))))
    (exec-block (mth-body method) env this-obj (mth-owner method))
    '()))

; Handles execution of code blocks, automatically adding a block environment when needed
(define (exec-block body env this current-class)
  (for ((s body)) (exec-stmt s env this current-class)))

; Updates the program's variable layers by executing the inputted statement, or returning its associated value if it is a "return" statement
(define (exec-stmt s env this current-class)
  (match s
    (`(begin . ,body) (exec-block body (push env) this current-class))
    (`(var ,n) (declare! env n '()))
    (`(var ,n ,e) (declare! env n (eval-expr e env this current-class)))
    (`(= ,lhs ,rhs) (assign-lhs! lhs (eval-expr rhs env this current-class) env this current-class))
    (`(return ,e) (raise (ret (eval-expr e env this current-class))))
    (`(if ,c ,t) (when (truth (eval-expr c env this current-class)) (exec-stmt t env this current-class)))
    (`(if ,c ,t ,f) (if (truth (eval-expr c env this current-class)) (exec-stmt t env this current-class) (exec-stmt f env this current-class)))
    (`(while ,c ,body)
     (let loop ()
       (when (truth (eval-expr c env this current-class))
         (with-handlers ((brk? (lambda (x) (void)))
                         (cont? (lambda (x) (loop))))
           (exec-stmt body env this current-class)
           (loop)))))
    (`(break) (raise (brk)))
    (`(continue) (raise (cont)))
    (`(funcall . ,_) (eval-expr s env this current-class))
    (`(throw ,e) (raise (thrown (eval-expr e env this current-class))))
    (`(try ,tryb ,catchb ,finallyb)
     (define caught #f)
     (with-handlers ((thrown? (lambda (x)
                                (set! caught #t)
                                (when (pair? catchb)
                                  (define cenv (push env))
                                  (declare! cenv (caadr catchb) (thrown-v x))
                                  (exec-block (caddr catchb) cenv this current-class)))))
       (exec-block tryb (push env) this current-class))
     (when (pair? finallyb) (exec-block (cadr finallyb) (push env) this current-class)))
    (`(function ,n ,ps ,body) (declare! env n (lfun ps body env this current-class)))
    (_ (error 'interpret (format "Bad statement ~a" s)))))

; Interprets the code contained in the file with the inputted filename
(define (interpret filename classname)
  (install-classes! (parser filename))
  (define cn (sym classname))
  (define main (or (find-static cn 'main)
                 (find-method cn 'main)))
  (unless main (error 'interpret (format "No static main in class ~a" cn)))
  (out (call-method main #f '() (new-env) cn)))
(define interpret* interpret)
