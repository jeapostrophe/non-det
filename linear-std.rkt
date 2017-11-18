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

(struct prop () #:transparent)
(struct const prop (a) #:transparent)
(struct tensor prop (a b) #:transparent)

(struct pf () #:transparent)
(struct Lid pf () #:transparent)
(struct TensorIntro pf (Γ Δ A-pf B-pf) #:transparent)
(struct Exchange pf (Γp pf) #:transparent)
(struct TensorElim pf (A B pf) #:transparent)

;; Here we try to prove things directly... essentially this means
;; using the introduction rules.
(define (prove-direct Γ P)
  (choice
   ;; First, try to use an assumption
   (match Γ
     [(list (== P))
      (ans (Lid))]
     [_ fail])
   ;; Next, try to look at the goal and go prove it directly
   (match P
     [(tensor A B)
      (ndo [(cons Γ Δ) (ans* (partitions-of Γ))]
           [A-pf (prove-direct Γ A)]
           [B-pf (prove-direct Δ B)]
           (ans (TensorIntro Γ Δ A-pf B-pf)))]
     ;; XXX WithIntro --- obvious

     ;; XXX XorIntro --- obvious, using choice

     ;; XXX LolliIntro --- must consider each place inside of Γ to insert A

     ;; XXX LolliElim --- I think this should be here and include an
     ;; embedded Exhange proof
     [_ fail])))
;; We permute here, rather than in the direct loop, because we don't
;; want to go into infinite loops consider permutations over and
;; over again.
(define (permute-then-prove Γ P)
  (ndo [Γp (ans* (in-permutations Γ))]
       [pf (prove-direct Γp P)]
       (ans (Exchange Γp pf))))
;; This strategy looks at the context and breaks everything up into
;; its constituent pieces. After we have all the pieces, then we
;; permute. Essentially, we are applying all of the elimination
;; forms.
(define (breakup-assumptions Γin Γout P)
  (match Γin
    ['() (permute-then-prove Γout P)]
    [(cons (tensor A B) Γin)
     (ndo [pf (breakup-assumptions (list* A B Γin) Γout P)]
          (ans (TensorElim A B pf)))]
    ;; XXX WithElim --- This would provide two answers (so perhaps
    ;; we should sort these to the end so that they are split at the
    ;; end rather than early, but maybe it doesn't matter?)

    ;; XXX XorElim --- This would generate two Proofs

    ;; XXX LolliElim --- I don't think this should be here because
    ;; it is not obvious how to eliminate.
    [(cons (? const? A) Γin)
     ;; XXX Technically this should have a proof that does an
     ;; exchange skipping over A
     (breakup-assumptions Γin (cons A Γout) P)]))
;; Start off the algorithm
(define (proves-top Γ P)
  (breakup-assumptions Γ empty P))

(module+ test
  (define A (const 'A))
  (define B (const 'B))
  (solve #:mode dfs #:k 1 (proves-top (list A) A))
  (solve #:k 1 (proves-top (list A B) (tensor A B)))
  (solve #:k 1 (proves-top (list A B) (tensor B A)))
  (solve #:k 1 (proves-top (list (tensor A B)) (tensor B A))))
