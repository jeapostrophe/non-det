#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list
         racket/stream
         racket/contract
         racket/generic)

(struct non-det ())
(struct *fail non-det ())
(define fail (*fail))
(struct bind non-det (x mx))
(struct *choice non-det (x y))
(struct ans non-det (a))
(struct seq non-det (s))
;; XXX Add a non-det generic

(struct kont:return ())
(struct kont:bind (mx k))
(struct kont:choice (y k))

(struct st (p kont))

(define-generics ndq
  (qempty? ndq)
  (qhead ndq)
  (enq ndq . v))

(define sols
  (match-lambda
    [(? qempty?) empty-stream]
    [(app qhead (cons (st p k) q))
     (match p
       ;; Do one step of work...
       [(bind x mx)   (sols (enq q (st x (kont:bind mx k))))]
       [(*choice x y) (sols (enq q (st x (kont:choice y k))))]
       [(seq s)
        (cond
          [(stream-empty? s)
           (sols (enq q (st fail k)))]
          [else
           (sols (enq q (st (*choice (ans (stream-first s))
                                     (seq (stream-rest s)))
                            k)))])]
       ;; ...And when it ends in a result...
       [(*fail)
        (match k
          ;; If it goes to a choice, then ignore and choose the other
          [(kont:choice y k) (sols (enq q (st y k)))]
          ;; If it goes to a bind, then ignore mx and fall to k
          [(kont:bind mx k)  (sols (enq q (st p k)))]
          ;; If it goes to a return, then throw away the st
          [(kont:return)     (sols q)])]
       ;; But if it is an answer...
       [(ans a)
        (match k
          ;; Fork the st and duplicate the continuation
          [(kont:choice y k) (sols (enq q (st p k) (st y k)))]
          ;; Call the function on a bind
          [(kont:bind mx k)  (sols (enq q (st (mx a) k)))]
          ;; We found a solution!
          [(kont:return)     (stream-cons a (sols q))])])]))

(struct bfs-ndq (in out)
  #:methods gen:ndq
  [(define (qempty? q)
     (match-define (bfs-ndq in out) q)
     (and (empty? in) (empty? out)))
   (define (qhead q)
     (match-define (bfs-ndq in out) q)
     (match in
       [(cons v in)
        (cons v (bfs-ndq in out))]
       ['()
        (if (empty? out)
          (error 'qhead "Non-det Queue is empty")
          (qhead (bfs-ndq (reverse out) empty)))]))
   (define (enq q . v)
     (match-define (bfs-ndq in out) q)
     (bfs-ndq in (append v out)))])
(define bfs (bfs-ndq empty empty))

(struct dfs-ndq (in)
  #:methods gen:ndq
  [(define (qempty? q)
     (empty? (dfs-ndq-in q)))
   (define (qhead q)
     (match-define (dfs-ndq in) q)
     (match in
       [(cons v in)
        (cons v (dfs-ndq in))]
       ['()
        (error 'qhead "Non-det Queue is empty")]))
   (define (enq q . v)
     (dfs-ndq (append v (dfs-ndq-in q))))])
(define dfs (dfs-ndq empty))

(define (mode->ndq m)
  (match m
    ['bfs bfs]
    ['dfs dfs]))

;; XXX add to racket/stream
(define (stream-take k s)
  (for/list ([i (in-range k)] [sol (in-stream s)])
    sol))
(define (solve p #:k [k +inf.0] #:mode [m 'bfs])
  (stream-take k (sols (enq (mode->ndq m) (st p (kont:return))))))

(define-syntax (ndo stx)
  (syntax-parse stx
    [(_) (syntax/loc stx fail)]
    [(_ p)
     #:declare p (expr/c #'non-det? #:name "non-det problem")
     #'p.c]
    [(_ [pat:expr p] . more)
     #:declare p (expr/c #'non-det? #:name "non-det problem")
     (syntax/loc stx
       (bind p.c (match-lambda [pat (ndo . more)])))]))

(define (choice . l)
  (for/fold ([p fail]) ([sp (in-list l)])
    (*choice p sp)))

(define (ans* v)
  (match v
    [(? list?) (ans* (in-list v))]
    [(? sequence?) (seq (sequence->stream v))]
    [(? stream?) (seq v)]))

;; XXX Implement some sort of `memo` operation that will save work
;; that appears in multiple places in the search space.

;; XXX Add once which calls solve inside of a problem to introduce a
;; cut point. (or does something else, because that is necessarily
;; DFS)

;; XXX Write tests & docs

(provide
 ndo
 (contract-out
  [non-det? (-> any/c boolean?)]
  [fail non-det?]
  [choice (->* () #:rest (listof non-det?) non-det?)]
  [ans* (-> (or/c list? sequence? stream?) non-det?)]
  [ans (-> any/c non-det?)]
  [solve (->* (non-det?) (#:k real? #:mode (or/c 'bfs 'dfs)) list?)]))
