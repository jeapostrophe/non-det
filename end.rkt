#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list
         racket/stream
         syntax/parse/define)

;; This implements a form of non-determinism that is similar
;; syntactically to Racklog/etc but is written monadically and allows
;; a breadth-first search approach

(struct fail ())
(struct bind (x mx))
(struct *par (x y))
(struct ans (a))
(struct seq (s))

(struct kont:return ())
(struct kont:bind (mx k))
(struct kont:par (y k))

(struct state (p kont))

;; Implement a queue of problems --- and thus run with BFS ---
;; although we could instead use a functional priority queue and
;; get either DFS or something like A* if we could inspect the
;; states and make some decision.
(define (solutions st:in st:out)
  (match st:in
    [(cons (state p k) st:in)
     (match p
       ;; Do one step of work...
       [(bind x mx)
        (solutions st:in (list* (state x (kont:bind mx k)) st:out))]
       [(seq s)
        ;; xxx if it is inf, then put a par at the end? so we do
        ;; something like DFS --- maybe this is stupid.
        (cond
          [(stream-empty? s)
           (solutions st:in (list* (state (fail) k) st:out))]
          [else
           (solutions st:in (list* (state (*par (ans (stream-first s))
                                                (seq (stream-rest s)))
                                          k)
                                   st:out))])]
       [(*par x y)
        (solutions st:in (list* (state x (kont:par y k)) st:out))]
       ;; ...And when it ends in a result...
       [(fail)
        (match k
          ;; If it goes to a par, then ignore and choose the other
          [(kont:par y k)
           (solutions st:in (list* (state y k) st:out))]
          ;; If it goes to a bind, then ignore mx and fall to k
          [(kont:bind mx k)
           (solutions st:in (list* (state p k) st:out))]
          ;; If it goes to a return, then throw away the state
          [(kont:return)
           (solutions st:in st:out)])]
       [(ans a)
        (match k
          ;; When an answer goes to a par, fork the state and
          ;; duplicate the continuation
          [(kont:par y k)
           (solutions st:in (list* (state p k) (state y k) st:out))]
          ;; Call the function on a bind
          [(kont:bind mx k)
           (solutions st:in (list* (state (mx a) k) st:out))]
          ;; We found a solution!
          [(kont:return)
           (stream-cons a (solutions st:in st:out))])])]
    ['()
     (cond
       [(empty? st:out)
        empty-stream]
       [else
        (solutions (reverse st:out) empty)])]))

(define (stream-take k s)
  (for/list ([i (in-range k)]
             [sol (in-stream s)])
    sol))

(define (solve p #:k [k +inf.0])
  (stream-take k (solutions (list (state p (kont:return))) empty)))

;;;; Library
(define-syntax (ndo stx)
  (syntax-parse stx
    [(_) (syntax/loc stx (fail))]
    [(_ p) #'p]
    [(_ [pat:expr x] . more)
     (syntax/loc stx
       (bind x (match-lambda [pat (ndo . more)])))]))

(define (choice . l)
  (for/fold ([p (fail)]) ([sp (in-list l)])
    (*par p sp)))

(define (ans* v)
  (match v
    [(? list?) (ans* (in-list v))]
    [(? sequence?) (seq (sequence->stream v))]
    [(? stream?) (seq v)]))

;; XXX Implement some sort of `memo` operation that will safe work
;; that appears in multiple places in the search space.

;; XXX Write tests and contracts

(provide
 solve
 fail
 ndo
 choice
 ans*
 ans)
