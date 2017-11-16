#lang racket/base
(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/generic
         syntax/parse/define
         racket/hash
         racket/format
         racket/struct
         racket/match
         racket/list
         racket/pretty)

;; Unification
(struct var (id) #:transparent)

(define-generics unifiable
  (unifiable-pred unifiable)
  (unifiable-out unifiable)
  (unifiable-in unifiable l))

(define (unbound-var? env q1)
  (and (var? q1)
       (not (hash-has-key? env q1))))
(define (bound-var? env q1)
  (and (var? q1)
       (hash-has-key? env q1)))

(define prefab? prefab-struct-key)
(define (unify env q1 q2)
  (cond
    [(equal? q1 q2)
     env]
    [(unbound-var? env q1)
     (hash-set env q1 q2)]
    [(unbound-var? env q2)
     (hash-set env q2 q1)]
    [(bound-var? env q1)
     (unify env (hash-ref env q1) q2)]
    [(bound-var? env q2)
     (unify env q1 (hash-ref env q2))]
    [(and (pair? q1) (pair? q2))
     (define new-env (unify env (car q1) (car q2)))
     (and new-env
          (unify new-env (cdr q1) (cdr q2)))]
    [(and (prefab? q1) (prefab? q2))
     (define psk1 (prefab-struct-key q1))
     (define psk2 (prefab-struct-key q2))
     (if (equal? psk1 psk2)
       (unify env (struct->list q1) (struct->list q2))
       #f)]
    [(and (unifiable? q1) (unifiable? q2))
     (define q1? (unifiable-pred q1))
     (define q2? (unifiable-pred q2))
     (if (and (q1? q2) (q2? q1))
       (unify env (unifiable-out q1) (unifiable-out q2))
       #f)]
    [else #f]))

(define (env-deref env v)
  (cond
    [(bound-var? env v)
     (env-deref env (hash-ref env v))]
    [(cons? v)
     (cons (env-deref env (car v))
           (env-deref env (cdr v)))]
    [(prefab? v)
     (define psk (prefab-struct-key v))
     (apply make-prefab-struct psk
            (env-deref env (struct->list v)))]
    [(unifiable? v)
     (unifiable-in v (env-deref env (unifiable-out v)))]
    [else
     v]))

;; Rules and Constraints
(define-syntax (rule stx)
  (raise-syntax-error 'rule "Illegal outside define-constraint" stx))

(define-generics constraint
  (constraint-rules constraint))

(struct rule-succ (new-env proof body))
(struct rule-fail ())
(define the-rule-fail (rule-fail))

;; XXX :=/= , racket function calls

(begin-for-syntax
  (define-syntax-class constraint-rule
    #:description "constraint rule"
    #:attributes (defn matcher)
    #:literals (rule)
    (pattern (rule (rname:id v:id ...)
                   head:expr #:=> body:expr ...)
             #:with (body-id ...)
             (for/list ([i (in-naturals)]
                        [b (in-list (syntax->list #'(body ...)))])
               (format-id b "sg~a" i))
             #:with rname? (format-id #'rname "~a?" #'rname)
             #:attr defn
             (syntax/loc this-syntax
               (struct rname (v ... body-id ...)
                 #:transparent
                 #:methods gen:unifiable
                 [(define (unifiable-pred u) rname?)
                  (define (unifiable-out u)
                    (match-define (rname v ... body-id ...) u)
                    (list v ... body-id ...))
                  (define (unifiable-in u l)
                    (apply rname l))]))
             #:attr matcher
             (syntax/loc this-syntax
               (λ (env a-constraint)
                 (with-vars (v ...)
                   (cond
                     [(unify env a-constraint head)
                      => (λ (new-env)
                           (with-vars (body-id ...)
                             (rule-succ
                              new-env
                              (rname v ... body-id ...)
                              (make-immutable-hasheq
                               (list (cons body-id body) ...)))))]
                     [else
                      the-rule-fail])))))))
(define-syntax (define-constraint stx)
  (syntax-parse stx
    [(_ (cname:id v:id ...) r:constraint-rule ...)
     (with-syntax ([cname? (format-id #'cname "~a?" #'cname)])
       (syntax/loc stx
         (begin
           r.defn ...
           (define cname-rules
             (list r.matcher ...))
           (struct cname (v ...)
             #:transparent
             #:methods gen:constraint
             [(define (constraint-rules c)
                cname-rules)]
             #:methods gen:unifiable
             [(define (unifiable-pred u) cname?)
              (define (unifiable-out u)
                (match-define (cname v ...) u)
                (list v ...))
              (define (unifiable-in u l)
                (apply cname l))]))))]))

;; Search Algorithm
(struct state (env goals) #:transparent)
(struct *query (extract step))
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
  (match-define (state env goals) st)
  (~a "S("(hash-count goals)")"))
(define (format-term st t)
  (match-define (state env goals) st)
  (~e (env-deref env t)))
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
         " " (format-term st agt)
         " R(" (length r:in) ", " (length r:out) ")")]
    [(step:next-goalN st:in st:out st st-progress? g:br)
     (~a "5: next-goalN " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " GBR(" (length g:br) ")")]
    [(step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)
     (~a "6: next-ruleN " (length st:in) " -> " (length st:out)
         " / " (format-st st) " " st-progress?
         " GBR(" (length g:br) ")"
         " " (format-term st agt)
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

(define step
  (match-lambda
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
     (match-define (state env goals) st)
     ;; XXX Sort the goals based on how ground they are
     (step:next-goal1 st:in st:out st st-progress? (hash-keys goals) empty)]
    ;; 3) Work on goals by applying them to rules. If a goal has
    ;; multiple options, look at it later
    [(step:next-goal1 st:in st:out st st-progress? g:in g:br)
     (match g:in
       [(cons active-goal g:in)
        (match-define (state env goals) st)
        (define active-goal-term (hash-ref goals active-goal))
        ;; If there is a goal, then start trying to apply each rule
        (step:next-rule1 st:in st:out st st-progress?
                         g:in g:br
                         active-goal
                         active-goal-term
                         (constraint-rules active-goal-term) empty)]
       ['()
        ;; Otherwise, switch and start working on goals with branches
        (step:next-goalN st:in st:out st st-progress? g:br)])]
    ;; 4) Consider each rule for the goal
    [(step:next-rule1 st:in st:out st st-progress? g:in g:br
                      active-goal active-goal-term r:in r:out)
     (match r:in
       ;; If there are rules left, then try to apply one
       [(cons active-rule r:in)
        (match-define (state env goals) st)
        (match (apply-rule env active-rule active-goal-term)
          ;; If the rule doesn't apply, then move on
          [(rule-fail)
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
        (match-define (state env goals) st)
        (define active-goal-term (hash-ref goals active-goal))
        ;; If there is a goal, then start trying to apply each rule
        (step:next-ruleN st:in st:out st st-progress?
                         g:br
                         active-goal active-goal-term
                         (constraint-rules active-goal-term))]
       ['()
        ;; Otherwise, finalize looking at a state
        (step:end-state st:in st:out st st-progress?)])]
    ;; 6) Consider each rule for branching goals
    [(step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)
     (match r:in
       ;; If there is a rule, try to apply it
       [(cons active-rule r:in)
        (match-define (state env goals) st)
        (match (apply-rule env active-rule agt)
          ;; If the rule doesn't apply, then move on
          [(rule-fail)
           (step:next-ruleN st:in st:out st st-progress? g:br ag agt r:in)]
          ;; If it does apply then... and create a new child state
          [(? rule-succ? succ)
           ;; XXX It might end that now there is only one rule that matches
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
       [(st-solution? st)
        (step:solution st (step:next-state st:in st:out))]
       [st-progress?
        (step:next-state st:in (cons st st:out))]
       [else
        (step:next-state st:in st:out)])]
    ;; 8) If we are given a solution, throw it away and go to the next
    [(step:solution sol next)
     next]
    ;; 9) If we are done, then return
    [(? step:done? s)
     s]))

(define (st-solution? st)
  ;; XXX It is okay if goals contains only unify/disunify which are
  ;; disconnected, because they are constraints on free variables
  (hash-empty? (state-goals st)))
(define (apply-succ st active-goal succ)
  (match-define (state env goals) st)
  (match-define (rule-succ new-env proof more-goals) succ)
  (state (hash-set new-env active-goal proof)
         ;; XXX Detect if any more-goals has already been seen
         (hash-union (hash-remove goals active-goal) more-goals)))
(define (apply-rule env matcher t)
  (matcher env t))
(define (query-return? q)
  (match-define (*query extract step) q)
  (or (step:done? step)
      (step:solution? step)))
(define (query-done? q)
  (match-define (*query extract step) q)
  (or (step:done? step)))
(define (extract-solution q)
  (match-define (*query extract step) q)
  (match-define (step:solution sol k) step)
  (extract sol))

;; Main interface := Construct a query, step until you a reach a
;; solution, potentially ask for more solutions.
(define initial-goal-id (var (gensym 'initial)))
(define (query #:extract [extract (λ (x) x)]
               #:goal initial-goal)
  (define initial-state
    (state (hasheq) (hasheq initial-goal-id initial-goal)))
  (*query extract (step:next-state (list initial-state) empty)))

(define (solve1 q)
  (match-define (*query extract s) q)
  (define sp (step s))
  (show-step sp)
  (define qp (*query extract sp))
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
    (match-define (state env goals) sol)
    (for/hasheq ([k (in-list vs)])
      (values (var-id k) (env-deref env k)))))
(define extract-proof
  (λ (sol)
    (match-define (state env goals) sol)
    (env-deref env initial-goal-id)))
(define-simple-macro (with-vars (v:id ...) . body)
  (let ([v (var (gensym 'v))] ...) . body))
(define-simple-macro (run (~optional (~and #:proof
                                           (~bind [proof? #'#t]))
                                     #:defaults ([proof? #'#f]))
                          solve* arg ... (var:id ...) goal:expr)
  (with-vars (var ...)
    (solve*
     arg ...
     (query #:extract (if proof? extract-proof
                          (extract-vars (list var ...)))
            #:goal goal))))

;; Library

;;; XXX Test :false
(define-constraint (:false))

;;; XXX Test :true
(define-constraint (:true)
  (rule (R:true-id)
        (:true) #:=>))

;;; XXX Test :==
(define-constraint (:== X Y)
  (rule (R:==-refl X)
        (:== X X) #:=>))

;; XXX Make this right
(provide (all-defined-out))

;; Tests
(module+ test
  (define-constraint (:remove x xs o)
    (rule (R:remove-head x xs)
          (:remove x (cons x xs) xs)
          #:=>)
    (rule (R:remove-tail x y ys o)
          (:remove x (cons y ys) (cons y o))
          #:=>
          (:remove x ys o)))

  (run solve* (O) (:remove 'A '(B A C) O)))

;; Linear Logic --- Version 1
(module+ test
  (when #f
    (define-constraint (:append X Y Z)
      (rule (R:append-nil Y)
            (:append '() Y Y)
            #:=>)
      (rule (R:append-cons X XS B Z)
            (:append (cons X XS) B (cons X Z))
            #:=>
            (:append XS B Z)))

    (define-constraint (:proves Gamma Prop)
      (rule (R:assume A)
            (:proves (list A) A)
            #:=>)
      (rule (R:tensor-elim A B C G D0 D1)
            (:proves G C)
            #:=>
            (:append D0 D1 G)
            (:proves D0 (list 'tensor A B))
            (:proves (list* A B D1) C))
      (rule (R:tensor-intro A B D0 D1 G)
            (:proves G (list 'tensor A B))
            #:=>
            (:append D0 D1 G)
            (:proves D0 A)
            (:proves D1 B))
      (rule (R:swap D0 D1 G H C)
            (:proves G C)
            #:=>
            (:append D0 D1 G)
            (:append D1 D0 H)
            (:proves H C)))

    (run solve* (X Y) (:append X Y '(A B)))
    (run #:proof solve/k 1 () (:proves '(A) 'A))
    (run #:proof solve/k 1 () (:proves '(A B) '(tensor A B)))
    ;; Diverges
    #;(run #:proof solve/k 1 () (:proves '(B A) '(tensor A B)))
    #;(run #:proof solve/k 1 () (:proves '((tensor A B)) '(tensor B A)))))

;; Linear Logic --- Version 2
(module+ test
  (when #t
    (define-constraint (:proves In Prop Out)
      (rule (R:assume In A Out)
            (:proves In A Out)
            #:=>
            (:remove A In Out))
      (rule (R:tensor-intro In A B Tmp Out)
            (:proves In (list 'tensor A B) Out)
            #:=>
            (:proves In A Tmp)
            (:proves Tmp B Out))
      (rule (R:tensor-elim In A B C Tmp Out)
            (:proves In C Out)
            #:=>
            (:proves In (list 'tensor A B) Tmp)
            (:proves (list* A B Tmp) C Out)))

    (run #:proof solve/k 1 () (:proves '(A) 'A '()))
    (run #:proof solve/k 1 () (:proves '(A B) '(tensor A B) '()))
    #;(run #:proof solve/k 1 () (:proves '(B A) '(tensor A B) '()))
    ;; Diverges
    #;
    (run #:proof solve/k 1 () (:proves '((tensor A B)) '(tensor B A) '()))))

;; XXX Write and check proofs
