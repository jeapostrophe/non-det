#lang racket/base
(require racket/match
         racket/list
         racket/contract/base
         racket/generic
         data/heap)

(struct opt (solution score branches-t))

(define (candidate bound branch data)
  (opt #f (bound data) (λ () (branch data))))
(define (solution value data)
  (opt data (value data) #f))

(define (optimize #:mode [mode 'min] entire-space heuristics)
  (define-values (order initial-sc)
    (match mode
      ['min (values <= +inf.0)]
      ['max (values >= -inf.0)]))
  (define (order-opts x y)
    (cond
      [(or (and (opt-solution x) (opt-solution y))
           (not (or (opt-solution x) (opt-solution y))))
       (order (opt-score x) (opt-score y))]
      [else
       (opt-solution x)]))
  (define Q (make-heap order-opts))
  (heap-add! Q entire-space)
  (heap-add-all! Q heuristics)
  (define BEST #f)
  (define BEST-sc initial-sc)
  (let/ec esc
    (for ([c (in-heap/consume! Q)])
      (match-define (opt solution score branches-t) c)
      (cond
        [solution
         (when (order score BEST-sc)
           (set! BEST c)
           (set! BEST-sc score))]
        [else
         (when (order BEST-sc score)
           (esc 'done))
         (for ([m (in-list (branches-t))])
           (define m-sc (opt-score m))
           (unless (order BEST-sc m-sc)
             (heap-add! Q m)))])))
  (and BEST
       (opt-solution BEST)))

(provide
 opt?
 opt-solution
 candidate
 solution
 optimize)
