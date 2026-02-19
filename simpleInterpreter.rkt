#lang racket

(require "simpleParser.rkt")


(define interpret
  (lambda (filename) (interpret-raw-code (parser filename))))

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


      