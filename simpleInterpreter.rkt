#lang racket

(require "simpleParser.rkt")

; (file-exists? "test.txt")

(define interpret-raw-code
  (lambda (code)
    (cond
      ((null? code) (newline))
      ((list? (car code)) (car code))
      (else code))))

(define new-variable
  (lambda (var-name value) (list (cons var-name value))))

(define add-variable
  (lambda (var-name value variables)
    (cond
      ((empty? variables) (new-variable var-name value))
      ((and (pair? variables) (null? (cdr variables))) (cons (car variables) (new-variable var-name value)))
      (else (append variables (new-variable var-name value))))))

(define (value binding) (cdr binding))
(define (name binding) (car binding))

; need to add helper function with break functionality for this one
(define set-variable
  (lambda (var-name value variables)
    (cond
      ((empty? variables) (error "Variables must be declared before they can be assigned values!"))
      ((eq? (name (car variables)) var-name) (add-variable var-name value (cdr variables)))
      (else (append (car variables) (set-variable var-name value (cdr (list variables))))))))


; -------------------------
; STATE (alist of (name . value))
; use 'unassigned for declared-but-not-set
; -------------------------

(define empty-state
  (lambda () '()))

(define binding-name car)
(define binding-value cdr)

(define declared?
  (lambda (var state)
    (cond
      ((null? state) #f)
      ((eq? (binding-name (car state)) var) #t)
      (else (declared? var (cdr state))))))

(define state-declare
  (lambda (var val state)
    (cond
      ((declared? var state) (error "Variable already declared:" var))
      (else (cons (cons var val) state)))))

(define state-lookup
  (lambda (var state)
    (cond
      ((null? state) (error "Variable used before declaring:" var))
      ((eq? (binding-name (car state)) var)
       (let ((v (binding-value (car state))))
         (if (eq? v 'unassigned)
             (error "Variable used before assigning:" var)
             v)))
      (else (state-lookup var (cdr state))))))

(define state-update
  (lambda (var val state)
    (cond
      ((null? state) (error "Variable must be declared before assignment:" var))
      ((eq? (binding-name (car state)) var)
       (cons (cons var val) (cdr state)))
      (else (cons (car state) (state-update var val (cdr state)))))))

; -------------------------
; M_value / M_integer (expressions -> value)
; (for now: integers + variable references only)
; -------------------------

(define operator car)
(define operand1 cadr)
(define operand2 caddr)

(define M_integer
  (lambda (expression state)
    (cond
      ((number? expression) expression)
      ((symbol? expression) (state-lookup expression state))  ; variable reference

      ;; unary minus: (- x)
      ((and (pair? expression)
            (eq? (operator expression) '-)
            (= (length expression) 2))
       (- (M_integer (operand1 expression) state)))

      ;; binary ops: (+ a b), (- a b), (* a b), (/ a b), (% a b)
      ((and (pair? expression) (symbol? (operator expression)))
       (cond
         ((eq? '+ (operator expression))
          (+ (M_integer (operand1 expression) state)
             (M_integer (operand2 expression) state)))

         ((eq? '- (operator expression))
          (- (M_integer (operand1 expression) state)
             (M_integer (operand2 expression) state)))

         ((eq? '* (operator expression))
          (* (M_integer (operand1 expression) state)
             (M_integer (operand2 expression) state)))

         ((eq? '/ (operator expression))
          (quotient (M_integer (operand1 expression) state)
                    (M_integer (operand2 expression) state)))

         ((eq? '% (operator expression))
          (remainder (M_integer (operand1 expression) state)
                     (M_integer (operand2 expression) state)))

         (else (error "Invalid operator:" (operator expression)))))

      (else (error "Bad integer expression:" expression)))))

(define M_value
  (lambda (expr state)
    (cond
      ;; boolean literals
      ((or (eq? expr 'true) (eq? expr 'false))
       expr)

      ;; boolean operator forms
      ((and (pair? expr) (member (car expr) '(|| && ! < <= > >= == !=)))
       (M_boolean expr state))

      ;; otherwise treat as integer expression / variable / number
      (else
       (M_integer expr state)))))

; -------------------------
; M_boolean 
; -------------------------

(define (bool->lang b) (if b 'true 'false))

(define (lang-bool? v) (or (eq? v 'true) (eq? v 'false)))

(define (lang->bool v)
  (cond ((eq? v 'true) #t)
        ((eq? v 'false) #f)
        (else (error "Expected boolean, got:" v))))

(define M_boolean
  (lambda (c state)
    (cond
      ((eq? c 'true) 'true)
      ((eq? c 'false) 'false)
      ((symbol? c) (let ((v (state-lookup c state)))
                     (if (lang-bool? v) v (error "Expected boolean var:" c))))

      ;; (! cond)
      ((and (pair? c) (eq? (car c) '!))
       (bool->lang (not (lang->bool (M_boolean (cadr c) state)))))

      ;; (&& c1 c2), (|| c1 c2)
      ((and (pair? c) (eq? (car c) '&&))
       (bool->lang (and (lang->bool (M_boolean (cadr c) state))
                        (lang->bool (M_boolean (caddr c) state)))))
      ((and (pair? c) (eq? (car c) '||))
       (bool->lang (or (lang->bool (M_boolean (cadr c) state))
                       (lang->bool (M_boolean (caddr c) state)))))

      ;; comparisons: (< a b) etc. where a/b are int expressions
      ((and (pair? c) (member (car c) '(< <= > >= == !=)))
       (let ((a (M_integer (cadr c) state))
             (b (M_integer (caddr c) state))
             (op (car c)))
         (bool->lang
          (cond ((eq? op '<)  (< a b))
                ((eq? op '<=) (<= a b))
                ((eq? op '>)  (> a b))
                ((eq? op '>=) (>= a b))
                ((eq? op '==) (= a b))
                ((eq? op '!=) (not (= a b)))
                (else (error "bad compare"))))))
      (else (error "Bad condition:" c)))))

; -------------------------
; M_state (statements -> new state)
; statement list evaluation stops early if 'return is set
; -------------------------

(define returned?
  (lambda (state)
    (and (declared? 'return state)
         (not (eq? (state-lookup 'return state) 'unassigned)))))

(define M_state-stmt
  (lambda (stmt state)
    (cond
      ((and (pair? stmt) (eq? (car stmt) 'var))
        (let ((x (cadr stmt)))
          (if (= (length stmt) 2)
            (state-declare x 'unassigned state)
            (state-declare x (M_value (caddr stmt) state) state))))

      ;; (= x expr)
      ((and (pair? stmt) (eq? (car stmt) '=))
       (let ((x (cadr stmt))
             (e (caddr stmt)))
         (state-update x (M_value e state) state)))

      ;; (return expr)  -> store into special 'return variable
      ((and (pair? stmt) (eq? (car stmt) 'return))
       (let ((v (M_value (cadr stmt) state)))
         (if (declared? 'return state)
             (state-update 'return v state)
             (state-declare 'return v state))))

      ((and (pair? stmt) (eq? (car stmt) 'if))
        (let* ((cond-expr (cadr stmt))
            (then-stmt (caddr stmt))
            (else-stmt (if (= (length stmt) 4) (cadddr stmt) #f))
            (cond-val (lang->bool (M_boolean cond-expr state))))
          (if cond-val
            (M_state-stmt then-stmt state)
              (if else-stmt (M_state-stmt else-stmt state) state))))

      (else (error "Unknown statement:" stmt)))))

(define M_state-stmtlist
  (lambda (stmts state)
    (cond
      ((null? stmts) state)
      ((returned? state) state) ; stop executing after return
      (else (M_state-stmtlist (cdr stmts) (M_state-stmt (car stmts) state))))))


; -------------------------
; interpret
; -------------------------

(define interpret
  (lambda (filename)
    (let* ((tree (parser filename))
           (final (M_state-stmtlist tree (empty-state))))
      (state-lookup 'return final))))

(displayln (interpret "test15.txt"))
      