#lang racket

;; CFGs are defined as a list of lists. Each inner list includes a name of the
;; block, and a terminator descriptor. Terminators can be (goto label),
;; (invoke normal_label catch_label) or (branch label_1 label_2).

(define simple-throwing-cfg
  '((a (invoke b c))
    (c (goto b))
    (b)))

;; The goal is now to generate something that resembles WASM bytecode in its
;; s-expr format. The result will follow the grammar:
;;
;; <expr> := (block (enter_exception_depth . exit_exception_depth) <expr> ...)
;;        |  (body label)
;;        |  (break depth)
;;        |  (if <expr> <expr>)
;;        |  (loop expr)
;;        |  (try <expr> (catch <expr>))
;;        |  (rethrow depth)
;;        |  (drop-exception)
;;
;; (body label) means the body of the CFG node with the given label
;;
;; Note that loops currently do not allow changes to the exception stack

;; Verifies the expression follows our type system for exceptions
;;
;; depth is #f if we're polymorphic
(define (verify-expr expr depth env)
  (match expr
    (`(block (,enter-depth . ,exit-depth)
             ,expr* ...)
     (if (depth-<= enter-depth depth)        
         (let ((env `((block ,enter-depth ,exit-depth) . ,env)))
           (let ((depth^
                  (foldl (λ (expr depth)
                           (verify-expr expr depth env))
                         enter-depth expr*)))
             (if (depth-eq? depth^ exit-depth)
                 (+ (- depth enter-depth) exit-depth)
                 (error 'verify-expr
                        "Incorrect exception depth in ~a, expected ~a, got ~a"
                        expr exit-depth depth^))))
         (error 'verify-expr "Exception depth at block entry is incorrect" expr)))
    (`(body ,label) depth)
    (`(break ,br-depth)
     (let ((target-depth (find-break-depth br-depth env)))
       (if (eq? target-depth depth)
           #f ;; we have an unconditional break, so we're polymorphic now.
           (error 'verify-expr "Target break depth does not match current exception depth"
                  expr))))
    (`(if ,conseq ,altern)
     (let ((conseq-depth (verify-expr conseq depth env)))
       ;; Make sure both branches end at the same exception depth
       (if (eq? conseq-depth (verify-expr altern depth env))
           conseq-depth
           (error 'verify-expr "If branches have different exit depths in ~a" expr))))
    (`(loop ,body)
     (if (depth-eq? depth (verify-expr body depth `((loop) . ,env)))
         depth
         (error 'verify-expr "Invalid loop body in ~a" expr)))
    (`(rethrow ,exn-depth)
     (if (depth-<= exn-depth depth)
         #f ;; An unconditional break, so the stack becomes polymorphic
         (error 'verify-expr "Invalid rethrow depth in ~a" expr)))
    (`(try ,body (catch ,catch))
     (if (and (depth-eq? (verify-expr body depth env) depth)
              (depth-eq? (verify-expr catch (add1 depth) env) (add1 depth)))
         depth
         (error 'verify-expr "Invalid try block in ~a" expr)))))
(define (find-break-depth depth env)
  (if (zero? depth)
      (match (car env)
        (`(block ,enter ,exit) exit)
        (`(loop) 0))
      (find-break-depth (sub1 depth) (cdr env))))
(define (depth-eq? d1 d2)
  (cond
    ((and d1 d2) (eq? d1 d2))
    ((or (not d1) (not d2)) #t)))
(define (depth-<= d1 d2)
  (cond
    ((and d1 d2) (<= d1 d2))
    ((not d2) #t)
    (else #f)))  


;; This is a manual translation of simple-throwing-cfg
(define simple-throwing-expr
  '(block (0 . 0)
          (try
           (body a)
           (catch
               (body c)))
          (body b)))
(verify-expr simple-throwing-expr 0 '())

(verify-expr '(block (0 . 0) (break 0)) 0 '())
(verify-expr '(if (body a) (body b)) 0 '())
(verify-expr '(block (0 . 0) (loop (break 1))) 0 '())
(verify-expr '(try (body a) (catch (rethrow 0))) 0 '())