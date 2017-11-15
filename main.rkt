#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         syntax/parse/define
         racket/hash
         racket/format
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
                      ;; XXX But the v are match variables here, we
                      ;; should really build-in unify
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

;; Steps
(struct *query (thy extract step))
(struct step:next-state (in out) #:transparent)
(struct step:init-goalq (st:in st:out st st-progress?) #:transparent)
(struct step:next-goal1 (st:in st:out st st-progress? g:in g:br) #:transparent)
(struct step:next-rule1 (st:in st:out st st-progress? g:in g:br ag agt r:in r:out) #:transparent)
(struct step:next-goalN (st:in st:out st st-progress? g:br) #:transparent)
(struct step:next-ruleN (st:in st:out st st-progress? g:br ag agt r:in) #:transparent)
(struct step:end-state (st:in st:out st st-progress?) #:transparent)
(struct step:solution (sol next) #:transparent)
(struct step:done () #:transparent)

(define (format-st st)
  (match-define (state env goals proofs) st)
  (~a "S("(hash-count goals)")"))
(define format-step
  (match-lambda
    [(step:next-state in out)
     (~a "1: next-state " (length in) " -> " (length out))]
    [(step:init-goalq st:in st:out st st-progress?)
     (~a "2: init-goalq " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?)]
    [(step:next-goal1 st:in st:out st st-progress? g:in g:br)
     (~a "3: next-goal1 " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " G(" (length g:in) ", " (length g:br) ")")]
    [(step:next-rule1 st:in st:out st st-progress? g:in g:br ag agt r:in r:out)
     (~a "4: next-rule1 " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " G(" (length g:in) ", " (length g:br) ")"
         " " ag "=" agt
         " R(" (length r:in) ", " (length r:out) ")")]
    [(step:next-goalN st:in st:out st st-progress? g:br)
     (~a "5: next-goalN " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " GBR(" (length g:br) ")")]
    [(step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)
     (~a "6: next-ruleN " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " GBR(" (length g:br) ")"
         " " ag "=" agt
         " R(" (length r:in) ")")]
    [(step:end-state st:in st:out st st-progress?)
     (~a "7: end-state " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?)]
    [(step:solution sol next)
     (~a "8: solution " (~e sol) ", " (format-step next))]
    [(step:done)
     (~a "9: done")]))
(define (show-step s)
  (displayln (format-step s))
  (flush-output))

(define (step q)
  (match-define (*query thy extract s) q)
  (match-define (*theory rules) thy)
  (define sp
    (match s
      ;; 1) Select a state to look at
      [(step:next-state in out)
       (match in
         ;; If there is one, then start inspecting it
         [(cons next in)
          (step:init-goalq in out next #f)]
         ;; If there are no more states in the queue, then
         ['()
          (if (empty? out)
            ;; If there are no more period, then stop
            (step:done)
            ;; Otherwise, start again from the beginning
            (step:next-state (reverse out) empty))])]
      ;; 2) Initialize the goal queue
      [(step:init-goalq st:in st:out st st-progress?)
       (match-define (state env goals proofs) st)
       (step:next-goal1 st:in st:out st st-progress? (hash-keys goals) empty)]
      ;; 3) Work on goals by applying them to rules. If a goal has
      ;; multiple options, look at it later
      [(step:next-goal1 st:in st:out st st-progress? g:in g:br)
       (match g:in
         [(cons active-goal g:in)
          (match-define (state env goals proofs) st)
          ;; If there is a goal, then start trying to apply each rule
          (step:next-rule1 st:in st:out st st-progress?
                           g:in g:br
                           active-goal
                           (hash-ref goals active-goal)
                           rules empty)]
         ['()
          ;; Otherwise, switch and start working on goals with branches
          (step:next-goalN st:in st:out st st-progress? g:br)])]
      ;; 4) Consider each rule for the goal
      [(step:next-rule1 st:in st:out st st-progress? g:in g:br
                        active-goal active-goal-term r:in r:out)
       (match r:in
         ;; If there are rules left, then try to apply one
         [(cons active-rule r:in)
          (match (apply-rule active-rule active-goal-term)
            ;; If the rule doesn't apply, then move on
            ;;
            ;; XXX May want to remember that it was a guard that failed
            ;; and try this later
            [(or (rule-fail) (rule-guard-fail))
             (step:next-rule1 st:in st:out st st-progress? g:in g:br
                              active-goal active-goal-term r:in r:out)]
            ;; If it does apply then...
            [(? rule-succ? succ)
             (if (empty? r:out)
               ;; If this is the first success, remember it
               (step:next-rule1 st:in st:out st st-progress? g:in g:br
                                active-goal active-goal-term
                                r:in (list succ))
               ;; If this is the second, then move this goal to the
               ;; branch queue, we'll come back to it later
               (step:next-goal1 st:in st:out st st-progress? g:in
                                (cons active-goal g:br)))])]
         ;; If the are no more rules to apply, then
         ['()
          ;; If there were any successes...
          (match r:out
            ;; If there were none
            ['()
             (step:next-goal1 st:in st:out st st-progress? g:in g:br)]
            [(list succ)
             (step:next-goal1 st:in st:out (apply-succ st active-goal succ) #t
                              g:in g:br)])])]
      ;; 5) Now go back and fork on the goals with multiple options
      ;; (note, that they may not be multiple options any more because
      ;; an earlier single rule could have eliminated the one or more
      ;; of the options---that's why we didn't save the matcher
      ;; results)
      [(step:next-goalN st:in st:out st st-progress? g:br)
       (match g:br
         [(cons active-goal g:br)
          (match-define (state env goals proofs) st)
          ;; If there is a goal, then start trying to apply each rule
          (step:next-ruleN st:in st:out st st-progress?
                           g:br
                           active-goal (hash-ref goals active-goal)
                           rules)]
         ['()
          ;; Otherwise, finalize looking at a state
          (step:end-state st:in st:out st st-progress?)])]
      ;; 6) Consider each rule for branching goals
      [(step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)
       (match r:in
         ;; If there is a rule, try to apply it
         [(cons active-rule r:in)
          (match (apply-rule active-rule agt)
            ;; If the rule doesn't apply, then move on
            ;;
            ;; XXX May want to remember that it was a guard that failed
            ;; and try this later
            [(or (rule-fail) (rule-guard-fail))
             (step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)]
            ;; If it does apply then... and create a new child state
            [(? rule-succ? succ)
             (step:next-ruleN st:in (cons (apply-succ st ag succ) st:out)
                              ;; Because we are forking the state
                              ;; here, any progress that we made will
                              ;; be preserved in the forked state, so
                              ;; we set st-progress back to #f
                              st #f g:br ag agt r:in)])]
         ;; If there are no more rules, then go to next goal
         ['()
          (step:next-goalN st:in st:out st st-progress? g:br)])]
      ;; 7) When we are done looking at a state, then decide if we will
      ;; return it as a solution or put it on the out queue
      [(step:end-state st:in st:out st st-progress?)
       (cond
         [(solution? st)
          (step:solution st (step:next-state st:in st:out))]
         [st-progress?
          (step:next-state st:in (cons st st:out))]
         [else
          (step:next-state st:in st:out)])]
      ;; 8) If we are given a solution, throw it away and go to the next
      [(step:solution sol next)
       next]
      ;; 9) If we are done, then return
      [(step:done)
       s]))
  (show-step sp)
  (*query thy extract sp))

(define (apply-succ st active-goal succ)
  (match-define (state env goals proofs) st)
  (match-define (rule-succ proof more-goals more-subst) succ)
  (apply-subst
   more-subst
   (state env
          ;; XXX Detect if any more-goals has already been seen
          ;; XXX Detect if :false is one of the new goals?
          (hash-union (hash-remove goals active-goal) more-goals)
          (hash-set proofs active-goal proof))))
(define (apply-rule r t)
  (match-define (*rule name matcher) r)
  (matcher t))
(define (query-return? q)
  (match-define (*query thy extract step) q)
  (or (step:done? step)
      (step:solution? step)))
(define (query-done? q)
  (match-define (*query thy extract step) q)
  (or (step:done? step)))
(define (extract-solution q)
  (match-define (*query thy extract step) q)
  (match-define (step:solution sol k) step)
  (extract sol))

;; Main interface := Construct a query, step until you a reach a
;; solution, potentially ask for more solutions.
(define (query #:theory [the-thy empty-theory]
               #:extract [extract (λ (x) x)]
               #:goal initial-goal)
  (define initial-goal-id (gensym 'initial))
  (define initial-state
    (state (hasheq) (hasheq initial-goal-id initial-goal) (hasheq)))
  (*query the-thy extract
          (step:next-state (list initial-state) empty)))

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
       (cons (extract-solution qp) (solve/k (sub1 k) qp)))]))

(define (solve* q)
  (solve/k +inf.0 q))

(define (extract-vars vs)
  (λ (sol)
    (match-define (state env goals proofs) sol)
    (for/hasheq ([k (in-list vs)])
      (values (var-id k) (hash-ref env k)))))
(define-simple-macro (with-vars (v:id ...) . body)
  (let ([v (var (gensym 'v))] ...) . body))
(define-simple-macro (solve (var:id ...) goal:expr)
  (with-vars (var ...)
    (solve*
     (query #:theory (current-theory)
            #:extract (extract-vars (list var ...))
            #:goal goal))))

(define-simple-macro (define-theory x:id . body)
  (define x (theory . body)))
(define current-theory (make-parameter empty-theory))
(define-simple-macro (with-theory x:id . body)
  (parameterize ([current-theory x]) . body))

;; XXX Maybe make these a structure so we cache the result
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
    (solve (O) (:remove 'A '(B A C) O))))

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
