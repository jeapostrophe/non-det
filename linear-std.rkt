#lang racket/base
(require rclp/end
         racket/list
         racket/match)

;; This version of the linear logic prover uses the standard rules.

;; XXX It would be good to also implement "In -> Out" version too

(define (partitions-of l)
  (for/list ([i (in-range (length l))])
    (define-values (before after) (split-at l i))
    (cons before after)))

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

(module+ test
  (solve #:k 1 (proves-top '(A) 'A))
  (solve #:k 1 (proves-top '(A B) '(tensor A B)))
  (solve #:k 1 (proves-top '(A B) '(tensor B A)))
  (solve #:k 1 (proves-top '((tensor A B)) '(tensor B A))))
