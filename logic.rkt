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
         racket/pretty
         racket/contract
         non-det)

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
     (ans env)]
    [(unbound-var? env q1)
     (ans (hash-set env q1 q2))]
    [(unbound-var? env q2)
     (ans (hash-set env q2 q1))]
    [(bound-var? env q1)
     (unify env (hash-ref env q1) q2)]
    [(bound-var? env q2)
     (unify env q1 (hash-ref env q2))]
    [(and (pair? q1) (pair? q2))
     (ndo [new-env (unify env (car q1) (car q2))]
          (unify new-env (cdr q1) (cdr q2)))]
    [(and (prefab? q1) (prefab? q2))
     (define psk1 (prefab-struct-key q1))
     (define psk2 (prefab-struct-key q2))
     (if (equal? psk1 psk2)
       (unify env (struct->list q1) (struct->list q2))
       fail)]
    [(and (unifiable? q1) (unifiable? q2))
     (define q1? (unifiable-pred q1))
     (define q2? (unifiable-pred q2))
     (if (and (q1? q2) (q2? q1))
       (unify env (unifiable-out q1) (unifiable-out q2))
       fail)]
    [else fail]))

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

;; Logic Results
(struct log-res (env pf) #:transparent)

(define-syntax (rule stx)
  (raise-syntax-error 'rule "Illegal outside define-relation" stx))

;; XXX :=/= , racket function calls

(begin-for-syntax
  (define-syntax-class relation-rule
    #:description "relation rule"
    #:attributes (defn matcher)
    #:literals (rule)
    (pattern (rule (rname:id v:id ...) head:expr #:=> body ...)
             #:declare body (expr/c #'(-> hash? non-det?) #:name "non-det problem")
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
               (λ (env a-conc)
                 (with-vars (v ...)
                   (ndo [new-env (unify env a-conc head)]
                        [(log-res new-env body-id) (body.c new-env)]
                        ...
                        (ans (log-res new-env (rname v ... body-id ...))))))))))

(define-syntax (define-relation stx)
  (syntax-parse stx
    [(_ (cname:id v:id ...) r:relation-rule ...)
     (with-syntax ([cname? (format-id #'cname "~a?" #'cname)])
       (syntax/loc stx
         (begin
           r.defn ...
           (struct cname (v ...)
             #:transparent
             #:methods gen:unifiable
             [(define (unifiable-pred u) cname?)
              (define (unifiable-out u)
                (match-define (cname v ...) u)
                (list v ...))
              (define (unifiable-in u l)
                (apply cname l))]
             #:property prop:procedure
             (λ (a-conc env) (choice (r.matcher env a-conc) ...))))))]))

(define (extract-vars env vs)
  (for/hasheq ([k (in-list vs)])
    (values (var-id k) (env-deref env k))))

(define-simple-macro (with-vars (v:id ...) . body)
  (let ([v (var 'v)] ...) . body))

(define-simple-macro (lsolve (v:id ...) arg ... an-nd)
  #:declare an-nd (expr/c #'(-> hash? non-det?) #:name "non-det problem")
  (with-vars (v ...)
    (solve arg ...
           (ndo [(log-res env pf) (an-nd.c (hasheq))]
                (ans (log-res (extract-vars env (list v ...))
                              (env-deref env pf)))))))

;; Library

;;; XXX Test :false
(define-relation (:false))

;;; XXX Test :true
(define-relation (:true)
  (rule (R:true-id)
        (:true) #:=>))

;;; XXX Test :==
(define-relation (:== X Y)
  (rule (R:==-refl X)
        (:== X X) #:=>))

;; XXX Define interface
(provide (all-defined-out))

;; Tests
(module+ test
  (define-relation (:remove x xs o)
    (rule (R:remove-head x xs)
          (:remove x (cons x xs) xs)
          #:=>)
    (rule (R:remove-tail x y ys o)
          (:remove x (cons y ys) (cons y o))
          #:=>
          (:remove x ys o)))

  (lsolve (O) (:remove 'A '(B A C) O)))

;; Linear Logic --- Version 1
(module+ test
  (when #t
    (define-relation (:append X Y Z)
      (rule (R:append-nil Y)
            (:append '() Y Y)
            #:=>)
      (rule (R:append-cons X XS B Z)
            (:append (cons X XS) B (cons X Z))
            #:=>
            (:append XS B Z)))

    (lsolve (X Y) #:k 1 (:append X Y '(A B)))

    (define-relation (:proves Gamma Prop)
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

    (lsolve () #:k 1 (:proves '(A) 'A))
    (lsolve () #:k 1 (:proves '(A B) '(tensor A B)))
    ;; Diverges
    #;(lsolve () #:k 1 (:proves '(B A) '(tensor A B)))
    #;(lsolve () #:k 1 (:proves '((tensor A B)) '(tensor B A)))))

;; Linear Logic --- Version 2
(module+ test
  (when #t
    (define-relation (:proves In Prop Out)
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

    (lsolve () #:k 1 #:mode 'dfs (:proves '(A) 'A '()))
    (lsolve () #:k 1 (:proves '(A B) '(tensor A B) '()))
    (lsolve () #:k 1 (:proves '(B A) '(tensor A B) '()))
    (lsolve () #:k 1 (:proves '((tensor A B)) '(tensor B A) '()))))

;; XXX Write and check proofs
