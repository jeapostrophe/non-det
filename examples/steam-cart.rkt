#lang racket/base
(require racket/list
         racket/match
         racket/format
         racket/file
         racket/set
         racket/pretty
         non-det/opt
         text-table)

;; Instructions:
;; - Add stuff you are thinking about to your cart.
;; - Copy from the bottom of the screen up to the first item
;; - Paste into steam-cart.txt
;; - Remove the boiler-plate at the bottom.
;; - Enter parameters
;; - Run!
(module+ main
  ;; How much cash do you want to spend?
  (define BUDGET 100)
  ;; Do you want to answer a questionaire first?
  ;; $ cut -f 2 -d '?' FILE | 
  (define RESCALE? #t)
  ;; Do you want to run the optimizer? (Takes about 15 seconds) Or
  ;; just use a heuristic?
  (define OPTIMIZE? #f))

(define (group-in n l)
  (cond
    [(empty? l) empty]
    [else
     (define-values (one more) (split-at l n))
     (cons one (group-in n more))]))

(define (->n s)
  (/ (string->number (regexp-replace (regexp-quote ".") (substring s 1) "")) 100))

(struct item (title actual original discounted) #:transparent)
(define (item-surplus i)
  (- (item-original i) (item-discounted i)))
(define (item-discount% i)
  (- 1 (/ (item-discounted i) (item-original i))))

(define (total-f f l)
  (for/sum ([i (in-list l)]) (f i)))
(define (total-surplus l) (total-f item-surplus l))

(define parse
  (match-lambda
    [(list original discount _ title)
     (item title (->n original) #f (->n discount))]))

(struct cart-state (heuristic? budget-left potential bought surplus surplus-bound))

(define (optimize-order budget optimize? items)
  ;; Problem Instance
  (define (branch cs)
    (match-define (cart-state _ budget-left potential bought surplus surplus-bound) cs)
    (match potential
      ['() empty]
      [(cons (and i (item _ _ _ discounted)) next-potential)
       (define the-surplus (item-surplus i))
       (cons
        ;; Don't include it
        (candidate* (cart-state #f budget-left next-potential bought surplus
                                (- surplus-bound the-surplus)))
        ;; Try to include it
        (cond
          [(<= discounted budget-left)
           (define new-budget-left (- budget-left discounted))
           (define new-potential
             (filter (λ (i) (<= (item-discounted i) new-budget-left))
                     next-potential))
           (define new-surplus (+ surplus the-surplus))
           (list
            (candidate*
             (cart-state #f new-budget-left
                         new-potential
                         (cons i bought)
                         new-surplus
                         surplus-bound)))]
          [else
           empty]))]))
  (define (candidate* st)
    (if (empty? (cart-state-potential st))
      (solution cart-state-surplus st)
      (candidate cart-state-surplus-bound branch st)))

  ;; Problem Setup
  (define (cart-state* heuristic? budget-left potential bought)
    (define the-surplus (total-surplus bought))
    (cart-state heuristic? budget-left potential bought
                the-surplus
                (+ the-surplus (total-surplus potential))))
  (define initial-st (cart-state* #f budget items '()))
  (define heuristics
    (for/list ([heur (list (vector "Max Surplus" >= item-surplus)
                           (vector "Max Discount%" >= item-discount%)
                           (vector "Max Original" >= item-original)
                           (vector "Min Discounted" <= item-discounted))])
      (match-define (vector name sort-<= sort-key) heur)
      (for/fold ([budget-left budget]
                 [buy '()]
                 #:result
                 (candidate* (cart-state* name budget-left '() buy)))
                ([i (in-list (sort items sort-<= #:key sort-key))])
        (match-define (item _ _ original discounted) i)
        (cond
          [(<= discounted budget-left)
           (values (- budget-left discounted)
                   (cons i buy))]
          [else
           (values budget-left buy)]))))

  (define sol
    (if optimize?
      (optimize #:mode 'max (candidate* initial-st)
                heuristics)
      (opt-solution (list-ref heuristics 1))))

  ;; Render solution
  (cond
    [(not sol)
     (printf "No feasible solution found!\n")]
    [else
     (match-define (cart-state name budget-left '() buy surplus _) sol)
     (define buy-set (list->seteq buy))

     (define (~$ n)
       (~a "$" (real->decimal-string n)))
     (define (~% n)
       (~a (real->decimal-string (* 100 n)) "%"))
     (displayln
      (table->string
       (cons (list "" "Name" "Actual" "Original" "Discounted" "%" "Surplus")
             (append
              (for/list ([i (in-list items)])
                (match-define (item name actual original discounted) i)
                (list (if (set-member? buy-set i) "" "Remove")
                      name
                      (~$ actual) (~$ original)
                      (~$ discounted)
                      (~% (item-discount% i)) (~$ (item-surplus i))))
              (let ()
                (define total-a (total-f item-actual buy))
                (define total-o (total-f item-original buy))
                (define total-d (total-f item-discounted buy))
                (list
                 (list "" "TOTAL"
                       (~$ total-a)
                       (~$ total-o)
                       (~$ total-d)
                       (~% (- 1 (/ total-d total-o)))
                       (~$ (- total-o total-d)))))))
       #:border-style 'double
       #:framed? #t
       #:row-sep? #t
       #:align '(left left right right right center right)))
     (when name
       (printf "\nOptimal is heuristic: ~a\n" name))]))

(define (rescale l)
  (struct bst (left val right))
  (define (update-orig left-orig v)
    (match-define (item title actual _ discounted) v)
    (define new-orig
      (cond
        [(<= actual left-orig)
         (+ left-orig 1)]
        [else
         actual]))
    (values new-orig (item title actual new-orig discounted)))
  (define (bst->list smallest-orig t)
    (match t
      [#f
       (values smallest-orig empty)]
      [(bst left v right)
       (define-values (right-orig right-l) (bst->list smallest-orig right))
       (define-values (v-orig new-v) (update-orig right-orig v))
       (define-values (left-orig left-l) (bst->list v-orig left))
       (values left-orig (append right-l (cons new-v left-l)))]))
  (define (bst-ins x < a-bst)
    (match a-bst
      [#f
       (bst #f x #f)]
      [(bst left y right)
       (if (< x y)
         (bst (bst-ins x < left) y right)
         (bst left y (bst-ins x < right)))]))

  (define (ask< x y)
    (let loop ()
      (printf "[A] ~a vs [D] ~a? " (item-title x) (item-title y))
      (match (read-line)
        [(or " a" "a") #t]
        [(or " d" "d") #f]
        [_ (loop)])))

  (define t
    (for/fold ([t #f]) ([i (in-list l)])
      (bst-ins i ask< t)))

  (define-values (max-orig new-l) (bst->list 0 t))
  new-l)

(module+ main
  (require racket/runtime-path)
  (define-runtime-path in "steam-cart.txt")
  (define the-cart
    (map parse (group-in 4 (file->lines in))))
  (define rescaled-cart
    (if RESCALE?
      (rescale the-cart)
      the-cart))
  (newline)
  (optimize-order BUDGET
                  OPTIMIZE?
                  rescaled-cart))
