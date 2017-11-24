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
;; - Enter a budget
;; - Run!
(module+ main
  (define BUDGET 100))

(define (group-in n l)
  (cond
    [(empty? l) empty]
    [else
     (define-values (one more) (split-at l n))
     (cons one (group-in n more))]))

(define (->n s)
  (/ (string->number (regexp-replace (regexp-quote ".") (substring s 1) "")) 100))

(struct item (title original discounted) #:transparent)
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
     (item title (->n original) (->n discount))]))

(struct cart-state (heuristic? budget-left potential bought surplus surplus-bound))

(define (optimize-order budget items)
  ;; Problem Instance
  (define (branch cs)
    (match-define (cart-state _ budget-left potential bought surplus surplus-bound) cs)
    (match potential
      ['() empty]
      [(cons (and i (item _ _ discounted)) next-potential)
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
        (match-define (item _ original discounted) i)
        (cond
          [(<= discounted budget-left)
           (values (- budget-left discounted)
                   (cons i buy))]
          [else
           (values budget-left buy)]))))

  (define sol
    #;(opt-solution (list-ref heuristics 1))
    (optimize #:mode 'max (candidate* initial-st)
              heuristics))

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
       (cons (list "" "Name" "Original" "Discounted" "%" "Surplus")
             (append
              (for/list ([i (in-list items)])
                (match-define (item name original discounted) i)
                (list (if (set-member? buy-set i) "" "Remove")
                      name (~$ original) (~$ discounted)
                      (~% (item-discount% i)) (~$ (item-surplus i))))
              (let ()
                (define total-o (total-f item-original buy))
                (define total-d (total-f item-discounted buy))
                (list
                 (list "" "TOTAL"
                       (~$ total-o)
                       (~$ total-d)
                       (~% (- 1 (/ total-d total-o)))
                       (~$ (- total-o total-d)))))))
       #:border-style 'double
       #:framed? #t
       #:row-sep? #t
       #:align '(left left right right center right)))
     (when name
       (printf "\nOptimal is heuristic: ~a\n" name))]))

(module+ main
  (require racket/runtime-path)
  (define-runtime-path in "steam-cart.txt")
  (define the-cart
    (map parse (group-in 4 (file->lines in))))
  (optimize-order BUDGET the-cart))
