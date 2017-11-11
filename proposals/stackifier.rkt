#lang racket

;; CFGs are defined as a list of lists. Each inner list includes a name of the
;; block, and a terminator descriptor. Terminators can be (goto label),
;; (invoke normal_label catch_label), (branch label_1 label_2), (return), or (rethrow).

(define simple-throwing-cfg
  '((a (invoke b c))
    (c (goto b))
    (b (return))))

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

(define (block-targets node)
  (match node
    (`(,_ (invoke ,a ,b)) (set a b))
    (`(,_ (goto ,a)) (set a))
    (`(,_ (branch ,a ,b)) (set a b))
    (`(,_ (return)) (set))
    (`(,_ (rethrow)) (set))))

(define (find-immediate-predecessors graph)
  (define (predecessors-of label)
    (foldl (λ (node predecessors)
             (if (set-member? (block-targets node) label)
                 (set-add predecessors (car node))
                 predecessors))
           (set)
           graph))
  (map (λ (node) (cons (car node) (predecessors-of (car node)))) graph))

(define (inline-single-entry-blocks/predecessors cfg predecessors)
  (define (single-entry? name)
    (= 1 (set-count (cdr (assq name predecessors)))))
  (define (inline-single-block label)
    (let ((node (assq label cfg)))
      (if (single-entry? label)
          (inline-body node)
          node)))
  (define (inline-body node)
    (let ((name (car node))
          (terminator (cadr node)))
      (match terminator
        (`(goto ,a)
         (if (single-entry? a)
             `(block
               (body ,a)
               ,(inline-body a (cadr (assq a cfg))))
             `(goto ,a)))
        (`(invoke ,normal ,except)
         `(invoke ,(inline-single-block normal) ,(inline-single-block except)))
        (`(branch ,conseq ,altern)
         `(if (block (body ,conseq) ,(inline-single-block conseq))
              (block (body ,altern) ,(inline-single-block altern))))
        (`(return) `(return)))))
  (foldr (λ (node cfg)
           (if (single-entry? (car node))
               ;; If there is only one predecessor, this block will be inlined into that block
               cfg
               (cons (list (car node) (inline-body node)) cfg)))
         (list)
         cfg))

(define (inline-single-entry-blocks cfg)
  (inline-single-entry-blocks/predecessors cfg (find-immediate-predecessors cfg)))

;; Create an intermediate representation that's more suitable for rewriting.
(define (cfg->expr-graph cfg)
  (define (node->expr node)
    (let ((label (car node))
          (terminator (cadr node)))
      (match terminator
        (`(invoke ,a ,b)
         `((try
            (body ,label)
            (catch
                (goto ,b)))
           (goto ,a)))
        (`(goto ,a)
         `((body ,label)
           (goto ,a)))
        (`(branch ,a ,b)
         `((body ,label)
           (if (goto ,a) (goto ,b))))
        (`(return)
         `((body ,label) (return)))
        (`(rethrow) `((body ,label) (rethrow))))))
  (foldr (λ (node cfg)
           (cons (cons (car node) (node->expr node)) cfg))
         '()
         cfg))

(cfg->expr-graph
 '((a (branch if else))
   (if (goto end))
   (else (goto end))
   (end (return))))

'(block
  (body a)
  (if
   (body if)
   (body else))
  (body end))

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
    (`(drop-exception)
     (if (depth-<= 1 depth)
         (depth-sub depth 1)
         (error 'verify-expr "No exception to drop")))
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
(define (depth-sub d1 d2)
  (and d1 (- d1 d2)))


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
(verify-expr '(block (0 . 0)
                     (block (0 . 1)
                            (try
                             (body a)
                             (catch
                                 (break 0)))
                            (break 1))
                     (drop-exception)) 0 '())



;; after exprifying
'((a (body a) (if (goto if) (goto else)))
  (if (body if) (goto end))
  (else (body else) (goto end))
  (end (body end) (return)))

;; merge-single-entry-blocks
'((a (body a) (if (block (body if) (goto end))
		  (block (body else) (goto end))))
  (end (body end) (return)))

;; merge-single-entry-blocks again
'((a (block
      (body a)
      (if (block (body if) (break 0))
	  (block (body else) (break 0))))
     (body end)
     (return)))
;; The trick is how we merge things.. Basically, if we have multiple gotos to a
;; block, we wrap with a block and replace gotos with breaks.

;; cleanup-fallthrough
'((a (block
      (body a)
      (if (block (body if))
	  (block (body else))))
     (body end)
     (return)))
;; This pass finds (break 0) in tail position in a block and removes them.  It
;; can be an optional cleanup pass at the end.


;; the goal:
'(block
  (body a)
  (if
   (body if)
   (body else))
  (body end))
