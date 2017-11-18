#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list
         racket/stream
         racket/contract
         racket/generic)

(struct nd ())
(struct *fail nd ())
(define fail (*fail))
(struct bind nd (x mx))
(struct *par nd (x y))
(struct ans nd (a))
(struct seq nd (s))

(struct kont:return ())
(struct kont:bind (mx k))
(struct kont:par (y k))

(struct st (p kont))

(define-generics queue
  (qempty? queue)
  (qhead queue)
  (enq queue . v))

(define sols
  (match-lambda
    [(? qempty?) empty-stream]
    [(app qhead (cons (st p k) q))
     (match p
       ;; Do one step of work...
       [(bind x mx) (sols (enq q (st x (kont:bind mx k))))]
       [(*par x y)  (sols (enq q (st x (kont:par y k))))]
       [(seq s)
        (cond
          [(stream-empty? s)
           (sols (enq q (st fail k)))]
          [else
           (sols (enq q (st (*par (ans (stream-first s)) (seq (stream-rest s))) k)))])]
       ;; ...And when it ends in a result...
       [(*fail)
        (match k
          ;; If it goes to a par, then ignore and choose the other
          [(kont:par y k)   (sols (enq q (st y k)))]
          ;; If it goes to a bind, then ignore mx and fall to k
          [(kont:bind mx k) (sols (enq q (st p k)))]
          ;; If it goes to a return, then throw away the st
          [(kont:return)    (sols q)])]
       ;; But if it is an answer...
       [(ans a)
        (match k
          ;; Fork the st and duplicate the continuation
          [(kont:par y k)   (sols (enq q (st p k) (st y k)))]
          ;; Call the function on a bind
          [(kont:bind mx k) (sols (enq q (st (mx a) k)))]
          ;; We found a solution!
          [(kont:return)    (stream-cons a (sols q))])])]))

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
(define (bfs v) (bfs-queue (list v) empty))

(struct dfs-queue (in)
  #:methods gen:queue
  [(define (qempty? q)
     (empty? (dfs-queue-in q)))
   (define (qhead q)
     (match (dfs-queue-in q)
       [(cons v in)
        (cons v (dfs-queue in))]
       ['()
        (error 'qhead "Queue is empty")]))
   (define (enq q . v)
     (dfs-queue (append v (dfs-queue-in q))))])
(define (dfs v) (dfs-queue (list v)))

(define (stream-take k s)
  (for/list ([i (in-range k)] [sol (in-stream s)])
    sol))
(define (solve p #:k [k +inf.0] #:mode [mode bfs])
  (stream-take k (sols (mode (st p (kont:return))))))

(define-syntax (ndo stx)
  (syntax-parse stx
    [(_) (syntax/loc stx fail)]
    [(_ p)
     #:declare p (expr/c #'nd? #:name "non-det problem")
     #'p.c]
    [(_ [pat:expr p] . more)
     #:declare p (expr/c #'nd? #:name "non-det problem")
     (syntax/loc stx
       (bind p.c (match-lambda [pat (ndo . more)])))]))

(define (choice . l)
  (for/fold ([p fail]) ([sp (in-list l)])
    (*par p sp)))

(define (ans* v)
  (match v
    [(? list?) (ans* (in-list v))]
    [(? sequence?) (seq (sequence->stream v))]
    [(? stream?) (seq v)]))

;; XXX Implement some sort of `memo` operation that will safe work
;; that appears in multiple places in the search space.

;; XXX Write tests

;; XXX compile *log to this

(provide
 ndo
 (contract-out
  [nd? (-> any/c boolean?)]
  [fail nd?]
  [choice (->* () #:rest (listof nd?) nd?)]
  [ans* (-> (or/c list? sequence? stream?) nd?)]
  [ans (-> any/c nd?)]
  [queue? (-> any/c boolean?)]
  [bfs (-> any/c queue?)]
  [dfs (-> any/c queue?)]
  [solve (->* (nd?) (#:k real? #:mode (-> any/c queue?)) list?)]))
