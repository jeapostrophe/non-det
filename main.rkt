#lang racket/base

;; Tests
(module+ test
  (define-theory list-theory
    (constraint :remove (x xs o))

    (rule (remove-head x xs o)
          (:remove x (cons x xs) xs)
          #:=>
          :true)
    (rule (remove-tail x y ys o)
          (:remove x (cons y ys) (cons x o))
          #:=>
          (:=/= x y)
          (:member x ys o)))

  (with-theory list-theory
    (solve (goal (O) (:remove 'A '(B A C) O)))))
