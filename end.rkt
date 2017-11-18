#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list
         racket/stream
         racket/generic
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

(define-generics queue
  (qempty? queue)
  (qhead queue)
  (enq queue . v))

;; Implement a queue of problems --- and thus run with BFS ---
;; although we could instead use a functional priority queue and
;; get either DFS or something like A* if we could inspect the
;; states and make some decision.
(define solutions
  (match-lambda
    [(? qempty?) empty-stream]
    [(app qhead (cons (state p k) q))
     (match p
       ;; Do one step of work...
       [(bind x mx)
        (solutions (enq q (state x (kont:bind mx k))))]
       [(seq s)
        (cond
          [(stream-empty? s)
           (solutions (enq q (state (fail) k)))]
          [else
           (solutions (enq q (state (*par (ans (stream-first s))
                                          (seq (stream-rest s)))
                                    k)))])]
       [(*par x y)
        (solutions (enq q (state x (kont:par y k))))]
       ;; ...And when it ends in a result...
       [(fail)
        (match k
          ;; If it goes to a par, then ignore and choose the other
          [(kont:par y k)
           (solutions (enq q (state y k)))]
          ;; If it goes to a bind, then ignore mx and fall to k
          [(kont:bind mx k)
           (solutions (enq q (state p k)))]
          ;; If it goes to a return, then throw away the state
          [(kont:return)
           (solutions q)])]
       [(ans a)
        (match k
          ;; When an answer goes to a par, fork the state and
          ;; duplicate the continuation
          [(kont:par y k)
           (solutions (enq q (state p k) (state y k)))]
          ;; Call the function on a bind
          [(kont:bind mx k)
           (solutions (enq q (state (mx a) k)))]
          ;; We found a solution!
          [(kont:return)
           (stream-cons a (solutions q))])])]))

(define (stream-take k s)
  (for/list ([i (in-range k)]
             [sol (in-stream s)])
    sol))

(struct bfs-queue (in out)
  #:methods gen:queue
  [(define (qempty? q)
     (match-define (bfs-queue in out) q)
     (and (empty? in) (empty? out)))
   (define (qhead q)
     (match-define (bfs-queue in out) q)
     (match in
       [(cons v in)
        (cons v (bfs-queue in out))]
       ['()
        (if (empty? out)
          (error 'qhead "Queue is empty")
          (qhead (bfs-queue (reverse out) empty)))]))
   (define (enq q . v)
     (match-define (bfs-queue in out) q)
     (bfs-queue in (append v out)))])
(define (bfs . in) (bfs-queue in empty))

(define (solve p #:k [k +inf.0])
  (stream-take k (solutions (bfs (state p (kont:return))))))

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
