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
                  ;; XXX It is weird that these v are logic variables here
                  (with-vars (v ...)
                    (match a-constraint
                      ;; XXX But the v are match variables here
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

;; XXX In these functions, it would be nice to know what was already
;; ground so we didn't always allocate and rebuild these things
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
     (state (hash-set (apply-subst/hash lhs rhs env) lhs rhs)
            (apply-subst/hash lhs rhs goals)
            (apply-subst/hash lhs rhs proofs))]))

(define (solution? st)
  ;; XXX It is okay if goals contains only unify/disunify which are
  ;; disconnected, because they are constraints on free variables
  (hash-empty? (state-goals st)))

(define (solve/tree the-thy st #:done? done? #:path [path #f])
  (match-define (*theory thy-rules) the-thy)
  (match-define (state-tree active sols) st)
  (printf "ACTIVE ~a // SOLS ~a\n"
          (length active) (length sols))
  (for*/fold
      ([a-rule-succ? #f]
       [new-active empty]
       [new-sols sols]
       #:result
       (cond
         ;; If there was a change
         [a-rule-succ?
          (or
           ;; XXX We could wrap up the state so we can resume in the
           ;; future
           (done? new-sols)
           (solve/tree the-thy (state-tree new-active new-sols)
                       #:done? done? #:path (and path (rest path))))]
         [else
          ;; We never finished and now rule applies, so there's no
          ;; work to be done.
          #f]))
      (;; Look at every single state (i.e. the fringe of the search space)
       [s (in-list active)]
       ;; For each goal, try to advance it
       [(g gc) (in-hash (state-goals s))]
       ;; For each rule, try to apply it
       [r (in-list thy-rules)]
       #:when (or (not path) (eq? (*rule-name r) (first path))))

    ;; XXX If two rules R1 and R2 apply in the same state, then there
    ;; will be two next states---R1 o R2 and R2 o R1---but most of the
    ;; time these are identical, so it is a waste of search
    ;; space. They should be separate if neither adds a substitution
    ;; and they don't use the same goal. (Or if it adds a subst but
    ;; there's no effect on R2)

    (match-define (state env goals proofs) s)
    (match-define (*rule name matcher) r)
    (match (matcher gc)
      [(or (rule-fail)
           (rule-guard-fail))
       (values a-rule-succ? new-active new-sols)]
      [(rule-succ proof more-goals more-subst)
       (define s-p
         (apply-subst
          more-subst
          (state env
                 ;; XXX Detect if any more-goals has already been seen
                 ;; XXX Detect if :false is one of the new goals?
                 (hash-union (hash-remove goals g) more-goals)
                 (hash-set proofs g proof))))
       (if (solution? s-p)
         (values #t new-active (cons s-p new-sols))
         (values #t (cons s-p new-active) new-sols))])))

(define (solve* #:theory [the-thy empty-theory]
                #:vars [query-vars '()]
                #:goals [initial-goals '()]
                #:path [path #f]
                #:count [k 1])
  (define (done? solutions)
    (and (<= k (length solutions))
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
  (solve/tree the-thy st0 #:done? done? #:path path))

(define-simple-macro (with-vars (v:id ...) . body)
  (let ([v (var (gensym 'v))] ...) . body))
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
  ;; to support any transparent or prefab struct (maybe make a prefab
  ;; match expression)

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
    (solve (O) (:remove 'A '(B A C) O)))

  #;
  (with-vars (O)
    (solve* #:theory list-theory
            #:vars (list O)
            #:goals (list (:remove 'A '(B A C) O))
            #:path '(remove-tail disunify-diff unify-var-lhs remove-head unify-id unify-var-rhs unify-var-lhs))))

#;([// (:remove 'A '(B A C) O)]
   => remove-tail
   [// (:=/= A B)
       (:== O (cons B io0))
       (:remove 'A '(A C) io0)]
   => disunify-diff
   [// (:== O (cons B io0))
       (:remove 'A '(A C) io0)]
   => unify-var-lhs
   [(:== O (cons B io0))
    //
    (:remove 'A '(A C) io0)]
   => remove-head
   [(:== O (cons B io0))
    //
    (:== 'A 'A)
    (:== '(C) io0)]
   => unify-id
   [(:== O (cons B io0))
    //
    (:== '(C) io0)]
   => unify-var-rhs
   [(:== O (cons B io0))
    //
    (:== io0 '(C))]
   => unify-var-lhs
   [(:== O '(B C))
    (:== io0 '(C))
    //])

(module+ test
  (struct :proves (Gamma Prop) #:prefab)
  (struct :append (X Y Z) #:prefab)
  (define-theory linear-logic
    #:require list-theory

    (rule (append-nil X Y Z)
          (:append X Y Z)
          #:=>
          (:== X '())
          (:== Y Z))
    (rule (append-cons A B C X XS Z)
          (:append A B C)
          #:=>
          (:== A (cons X XS))
          (:append XS B Z)
          (:== C (cons X Z)))
    
    (rule (assume A)
          (:proves G A)
          #:=>
          (:== G (list A)))
    (rule (tensor-elim A B C G D0 D1)
          (:proves G C)
          #:=>
          (:append D0 D1 G)
          (:proves D0 (list 'tensor A B))
          (:proves (list* A B D1) C))
    (rule (tensor-intro A B C D0 D1 G)
          (:proves G C)
          #:=>
          (:== (list 'tensor A B) C)
          (:append D0 D1 G)
          (:proves D0 A)
          (:proves D1 B)))

  #;(with-theory linear-logic
    (solve () (:proves '(A B) '(tensor A B))))
  )
