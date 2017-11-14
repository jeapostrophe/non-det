#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         syntax/parse/define
         racket/hash
         racket/struct
         racket/match
         racket/list
         racket/pretty)

(struct *theory (rules))
(struct var (id) #:transparent)
(struct :false ())
(define empty-theory (*theory empty))

(struct *rule (name matcher))
(struct rule-succ (proof body maybe-subst))
(struct rule-guard-fail ())
(define the-rule-guard-fail (rule-guard-fail))
(struct rule-fail ())
(define the-rule-fail (rule-fail))

(define-syntax (rule stx)
  (syntax-parse stx
    [(_ (name:id v:id ...)
        head:expr
        (~optional (~seq #:when guard:expr)
                   #:defaults ([guard #'#t]))
        #:=> body:expr ...
        (~optional (~seq #:subst! subst-lhs:id subst-rhs:expr)
                   #:defaults ([subst-lhs #'#f] [subst-rhs #'#f])))
     (with-syntax ([(body-id ...) (generate-temporaries #'(body ...))])
       (syntax/loc stx
         (*rule 'name
                (λ (a-constraint)
                  (with-vars (v ...)
                    (match a-constraint
                      [head
                       (cond
                         [guard
                          (with-vars (body-id ...)
                            (rule-succ
                             (list 'name v ... body-id ...)
                             (make-immutable-hasheq (list (cons body-id body) ...))
                             (and subst-lhs subst-rhs
                                  (cons subst-lhs subst-rhs))))]
                         [else
                          the-rule-guard-fail])]
                      [_
                       the-rule-fail]))))))]))

(define (theory-flatten l)
  (flatten (map (λ (x) (if (*theory? x) (*theory-rules x) x)) l)))

(define-syntax (theory stx)
  (syntax-parse stx
    [(_ (~optional #:require) rules:expr ...)
     (syntax/loc stx
       (*theory (theory-flatten (list rules ...))))]))

(struct state (env goals proofs) #:transparent)
(struct state-tree (active solutions) #:transparent)

(define (apply-subst/hash lhs rhs ht)
  (for/hasheq ([(k v) (in-hash ht)])
    (values k (apply-subst/val lhs rhs v))))
(define (apply-subst/val lhs rhs v)
  (match v
    [(== lhs) rhs]
    [(cons a d)
     (cons (apply-subst/val lhs rhs a)
           (apply-subst/val lhs rhs d))]
    [(app prefab-struct-key (and (not #f) psk))
     (apply
      make-prefab-struct
      psk
      (apply-subst/val lhs rhs (struct->list v)))]
    [x x]))
(define (apply-subst maybe-subst st)
  (match maybe-subst
    [#f st]
    [(cons (? var? lhs) rhs)
     ;; XXX Occurs check
     (match-define (state env goals proofs) st)
     (when (hash-has-key? env lhs)
       (error 'subst "Duplicate binding for ~e" lhs))
     (state (apply-subst/hash lhs rhs env)
            (apply-subst/hash lhs rhs goals)
            (apply-subst/hash lhs rhs proofs))]))

(define (solution? st)
  ;; XXX It is okay if goals contains only unify/disunify
  (empty? (state-goals st)))

(define (solve/tree the-thy st done?)
  (match-define (*theory thy-rules) the-thy)
  (match-define (state-tree active sols) st)
  (printf "\n==========================\nACTIVE = ~e\nSOLS = ~e\n\n"
          (length active) (length sols))
  (for*/fold
      ([a-rule-succ? #f]
       [a-rule-guard-fail? #f]
       [new-active empty]
       [new-sols sols]
       #:result
       (cond
         ;; If there was a change
         [a-rule-succ?
          (or (done? new-sols)
              (solve/tree the-thy (state-tree new-active new-sols) done?))]
         [else
          ;; XXX Return the tree?
          #f]))
      (;; Look at every single state (i.e. the fringe of the search space)
       [s (in-list active)]
       ;; For each goal, try to advance it
       [(g gc) (in-hash (state-goals s))]
       ;; For each rule, try to apply it
       [r (in-list thy-rules)])
    (match-define (state env goals proofs) s)
    (match-define (*rule name matcher) r)
    (match (matcher gc)
      [(rule-fail)
       (values a-rule-succ? a-rule-guard-fail? new-active new-sols)]
      [(rule-guard-fail)
       (values a-rule-succ? #t new-active new-sols)]
      [(rule-succ proof more-goals more-subst)
       (eprintf "\t~a => ~a\n" gc proof)
       (define s-p
         (apply-subst
          more-subst
          (state env
                 ;; XXX Detect if any more-goals has already been seen
                 ;; XXX Detect if :false is one of the new goals?
                 (hash-union (hash-remove goals g) more-goals)
                 (hash-set proofs g proof))))
       #;(pretty-print s-p)
       (if (solution? s-p)
         (values #t a-rule-guard-fail? new-active (cons s-p new-sols))
         (values #t a-rule-guard-fail? (cons s-p new-active) new-sols))])))

(define (solve* #:theory [the-thy empty-theory]
                #:vars [query-vars '()]
                #:goals [initial-goals '()]
                #:count [k 1])
  (define (done? solutions)
    (and (< k (length solutions))
         (for/list ([sol (in-list solutions)])
           (match-define (state env goals proofs) sol)
           (for/hasheq ([k (in-list query-vars)])
             (values (var-id k) (hash-ref env k))))))
  (define st0
    (state-tree
     (list
      (state (hasheq)
             (for/hasheq ([g (in-list initial-goals)])
               (values (gensym 'initial) g))
             (hasheq)))
     (list)))
  (solve/tree the-thy st0 done?))

(define-simple-macro (with-vars (v:id ...) . body)
  (let ([v (var 'v)] ...) . body))
(define-simple-macro (solve (var:id ...) goal:expr ...)
  (with-vars (var ...)
    (solve* #:theory (current-theory)
            #:vars (list var ...)
            #:goals (list goal ...))))

(define-simple-macro (define-theory x:id . body)
  (define x (theory . body)))
(define current-theory (make-parameter empty-theory))
(define-simple-macro (with-theory x:id . body)
  (parameterize ([current-theory x]) . body))

(define ground?
  (match-lambda
    [(? var?) #f]
    [(cons a d) (and (ground? a) (ground? d))]
    [_ #t]))

;; Library
(struct :== (x y) #:prefab)
(struct :=/= (x y) #:prefab)
(define-theory std-theory
  ;; XXX It stinks that cons is so baked in, because it would be nice
  ;; to support any transparent or prefab struct

  (rule (unify-id X)
        (:== X Y)
        #:when (equal? X Y)
        #:=>)
  (rule (unify-var-lhs X Y)
        (:== X Y)
        #:when (and (var? X) (not (equal? X Y)))
        #:=>
        #:subst! X Y)
  (rule (unify-var-rhs X Y)
        (:== X Y)
        #:when (and (var? Y) (not (equal? X Y)))
        #:=> (:== Y X))
  (rule (unify-cons xA xD yA yD)
        (:== (cons xA xD) (cons yA yD))
        #:=>
        (:== xA yA)
        (:== xD yD))

  (rule (disunify-diff X Y)
        (:=/= X Y)
        #:when (and (ground? X) (ground? Y) (not (equal? X Y)))
        #:=>)
  #;(rule (disunify-id X)
          (:=/= X X)
          #:=> (:false))
  (rule (disunify-cons-car xA xD yA yD)
        (:=/= (cons xA xD) (cons yA yD))
        #:=> (:=/= xA yA))
  (rule (disunify-cons-cdr xA xD yA yD)
        (:=/= (cons xA xD) (cons yA yD))
        #:=> (:=/= xD yD))
  (rule (disunify-cons-lhs xA xD Y)
        (:=/= (cons xA xD) Y)
        #:when (and (not (var? Y)) (not (cons? Y)))
        #:=>)
  (rule (disunify-cons-rhs xA xD Y)
        (:=/= Y (cons xA xD))
        #:when (and (not (var? Y)) (not (cons? Y)))
        #:=> (:=/= (cons xA xD) Y)))

;; Tests
(module+ test
  (struct :remove (x xs o) #:prefab)
  (define-theory list-theory
    #:require std-theory

    (rule (remove-head x y ys o)
          (:remove x (cons y ys) o)
          #:=>
          (:== x y)
          (:== ys o))
    (rule (remove-tail x y ys o io)
          (:remove x (cons y ys) o)
          #:=>
          (:=/= x y)
          (:== o (cons y io))
          (:remove x ys io)))

  (with-theory list-theory
    (solve (O) (:remove 'A '(B A C) O))))
