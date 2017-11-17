#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list
         racket/stream
         syntax/parse/define)
(module+ test
  (require chk))

;;;; Exposed Non-determinism
(struct fail ())
(struct bind (x mx))
(struct *par (x y))
(struct *ans1 (a))
(struct *ans (inf? s))

(struct kont:return ())
(struct kont:bind (mx k))
(struct kont:par (y k))

(struct state (p kont))

(struct step:next-state (st:in st:out))
(struct step:work1 (st:in st:out p))
(struct step:solution (a k))
(struct step:done ())

(define step
  (match-lambda
    ;; Implement a queue of problems
    [(step:next-state in out)
     (match in
       [(cons next in)
        (step:work1 in out next)]
       ['()
        (cond
          [(empty? out)
           (step:done)]
          [else
           ;; XXX Could sort out based on something?
           (step:next-state (reverse out) empty)])])]
    ;; Do one unit of work for this problem
    [(step:work1 st:in st:out (state p k))
     (match p
       ;; Do one step of work...
       [(bind x mx)
        (step:next-state st:in (list* (state x (kont:bind mx k)) st:out))]
       [(*ans inf? s)
        ;; xxx if it is inf, then put a par at the end? so we do
        ;; something like DFS
        (cond
          [(stream-empty? s)
           (step:next-state st:in (list* (state (fail) k) st:out))]
          [else
           (step:next-state st:in (list* (state (par (*ans1 (stream-first s))
                                                     (*ans inf? (stream-rest s)))
                                                k)
                                         st:out))])]
       [(*par x y)
        (step:next-state st:in (list* (state x (kont:par y k)) st:out))]
       ;; ...And when it ends in a result...
       [(fail)
        (match k
          ;; When a fail goes to a par, then ignore it and choose the
          ;; other option
          [(kont:par y k)
           (step:next-state st:in (list* (state y k) st:out))]
          ;; If it goes to a bind, then ignore mx and fall to
          ;; continuation
          [(kont:bind mx k)
           (step:next-state st:in (list* (state p k) st:out))]
          ;; If it goes to a return, then throw away the state
          [(kont:return)
           (step:next-state st:in st:out)])]
       [(*ans1 a)
        (match k
          ;; When an answer goes to a par, fork the state and
          ;; duplicate the continuation
          [(kont:par y k)
           (step:next-state st:in (list* (state p k) (state y k) st:out))]
          [(kont:bind mx k)
           (step:next-state st:in (list* (state (mx a) k) st:out))]
          [(kont:return)
           (step:solution a (step:next-state st:in st:out))])])]
    ;; When a solution is stepped, move on
    [(step:solution _ k)
     k]
    ;; When done, fix
    [(? step:done? s)
     s]))

(define (query-done? q)
  (or (step:done? q)))
(define (query-return? q)
  (or (query-done? q)
      (step:solution? q)))

(define (solve1 q)
  (define qp (step q))
  (if (query-return? qp)
    qp
    (solve1 qp)))

(define (solve/k k q)
  (cond
    [(zero? k)
     empty]
    [else
     (define qp (solve1 q))
     (if (query-done? qp)
       empty
       (cons (step:solution-a qp) (solve/k (sub1 k) qp)))]))

(define (solve p #:k [k +inf.0])
  (solve/k k (step:next-state (list (state p (kont:return))) empty)))

;;;; Library
(define-syntax (mdo stx)
  (syntax-parse stx
    [(_) (syntax/loc stx (fail))]
    [(_ p) #'p]
    [(_ [pat:expr x] . more)
     (syntax/loc stx
       (bind x (match-lambda [pat (mdo . more)])))]))

(define (par . l)
  (for/fold ([p (fail)]) ([sp (in-list l)])
    (*par p sp)))

(define-simple-macro (join e:expr ...)
  #:with (v ...) (generate-temporaries #'(e ...))
  (mdo [v e] ...
       (answer (list v ...))))

(define (answer-seq s) (*ans #f (sequence->stream s)))
(define (answer-infseq s) (*ans #t (sequence->stream s)))
(define-simple-macro (answers as:expr)
  (answer-seq (in-list as)))
(define-simple-macro (answer a:expr)
  (*ans1 a))

;;;; Tests

;; This is the standard prover.
(module+ test
  (define (partitions-of l)
    (for/list ([i (in-range (length l))])
      (define-values (before after) (split-at l i))
      (cons before after)))

  ;; XXX Can we memoize this to not repeat work?

  ;; Here we try to prove things directly... essentially this means
  ;; using the introduction rules.
  (define (prove-direct Γ P)
    (par
     ;; First, try to use an assumption
     (match Γ
       [(list (== P))
        (answer (list 'LId))]
       [_ (fail)])
     ;; Next, try to look at the goal and go prove it directly
     (match P
       [(list 'tensor A B)
        (mdo [(cons Γ Δ) (answers (partitions-of Γ))]
             [(list A-pf B-pf) (join (prove-direct Γ A) (prove-direct Δ B))]
             (answer (list 'TensorIntro Γ Δ A-pf B-pf)))]
       ;; XXX WithIntro --- obvious, using join

       ;; XXX XorIntro --- obvious, using par

       ;; XXX LolliIntro --- must consider each place inside of Γ to insert A

       ;; XXX LolliElim --- I think this should be here and include an
       ;; embedded Exhange proof
       [_ (fail)])))
  ;; We permute here, rather than in the direct loop, because we don't
  ;; want to go into infinite loops consider permutations over and
  ;; over again.
  (define (permute-then-prove Γ P)
    (mdo [Γp (answer-seq (in-permutations Γ))]
         [pf (prove-direct Γp P)]
         (answer (list 'Exchange Γp pf))))
  ;; This strategy looks at the context and breaks everything up into
  ;; its constituent pieces. After we have all the pieces, then we
  ;; permute. Essentially, we are applying all of the elimination
  ;; forms.
  (define (breakup-assumptions Γin Γout P)
    (match Γin
      ['() (permute-then-prove Γout P)]
      [(cons (list 'tensor A B) Γin)
       (mdo [pf (breakup-assumptions (list* A B Γin) Γout P)]
            (answer (list 'TensorElim A B pf)))]
      ;; XXX WithElim --- This would provide two answers (so perhaps
      ;; we should sort these to the end so that they are split at the
      ;; end rather than early, but maybe it doesn't matter?)

      ;; XXX XorElim --- This would generate a join

      ;; XXX LolliElim --- I don't think this should be here because
      ;; it is not obvious how to eliminate.
      [(cons (? symbol? A) Γin)
       ;; XXX Technically this should have a proof that does an
       ;; exchange skipping over A
       (breakup-assumptions Γin (cons A Γout) P)]))
  ;; Start off the algorithm
  (define (proves-top Γ P)
    (breakup-assumptions Γ empty P))

  (solve #:k 1 (proves-top '(A) 'A))
  (solve #:k 1 (proves-top '(A B) '(tensor A B)))
  (solve #:k 1 (proves-top '(A B) '(tensor B A)))
  (solve #:k 1 (proves-top '((tensor A B)) '(tensor B A))))

;; XXX Implement the In -> Out version of assumptions too
