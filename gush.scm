(use-modules (oop goops)
             (clone)
             (srfi srfi-1)
             (srfi srfi-9)
             (srfi srfi-111)
             (fash)
             (ice-9 match)
             (ice-9 control))


;;; Generics and environments

(define-record-type <gush-generic>
  (%make-gush-generic sym methods docstring cost)
  gush-generic?
  ;; What "symbol" this maps to for read/write
  (sym gush-generic-sym)
  ;; List of methods that implement this generic
  (methods gush-generic-methods set-gush-generic-methods!)
  ;; A docstring, if any
  (docstring gush-generic-docstring)
  ;; How many cpu "steps" invoking this method costs
  (cost gush-generic-cost))

(define* (make-gush-generic defined-sym
                            #:optional docstring
                            #:key (cost 1)
                            (methods '())
                            (sym defined-sym))
  (%make-gush-generic sym methods docstring cost))

(define-record-type <gush-method>
  (%make-gush-method param-preds proc)
  gush-method?
  (param-preds gush-method-param-preds)
  (proc gush-method-proc))

(define-syntax-rule (define-gush-generic sym args ...)
  (define sym
    (make-gush-generic (quote sym) args ...)))

;; emacs: (put 'gush-method 'scheme-indent-function 1)
(define-syntax-rule (gush-method ((param pred) ...)
                      body ...)
  (%make-gush-method (list pred ...)
                     (lambda (param ...)
                       body ...)))

(define-syntax-rule (define-gush-method (generic (param pred) ...)
                      body ...)
  "Append a gush method to the generic SYM"
  (set-gush-generic-methods!
   generic (cons (gush-method ((param pred) ...) body ...)
                 (gush-generic-methods generic))))

(define (make-gush-env . generics)
  (let ((env (make-hash-table)))
    (for-each (lambda (generic)
                (hashq-set! env (gush-generic-sym generic)
                            generic))
              generics)
    env))

(define-inlinable (get-generic gush-env sym)
  (hashq-ref gush-env sym))


;; Some example methods

(define-gush-generic gush:+
  "Add two numbers on the stack"
  #:sym '+)

(define-gush-method (gush:+ (x number?) (y number?))
  (+ x y))

(define-gush-generic gush:*
  "Multiply two numbers on the stack"
  #:sym '*)

(define-gush-method (gush:* (x number?) (y number?))
  (* x y))

(define-gush-generic gush:-
  "Subtract two numbers on the stack"
  #:sym '-)

(define-gush-method (gush:- (x number?) (y number?))
  (- x y))

(define-gush-generic gush:dup
  "Duplicate the top item on the stack"
  #:sym 'dup)

(define-gush-method (gush:dup (var (const #t)))
  (values var var))

(define-gush-generic gush:drop
  "Drop the top item on the stack"
  #:sym 'drop)

(define-gush-method (gush:drop (var (const #t)))
  (values))

(define *default-gush-env*
  (make-gush-env gush:+ gush:* gush:-
                 gush:drop gush:dup))



(define* (find-stack-matches preds program #:optional limiter)
  "Returns either:
 - #f: matches not found.
 - (items new-stack): a list of items matching PRED from the
   STACK and a new stack with those items removed."
  (define stack (.values program))
  (let lp ((preds preds)
           (stack stack)
           (vals '())
           (re-append '()))
    (cond
     ;; We've reached the end of our preds... horray!
     ;; return the vals we found and the new stack
     ((eq? preds '())
      (values (reverse vals)
              ;; faster version of (append (reverse re-append) stack)
              (fold cons stack re-append)))
     ;; We've reached the end of the stack without finding
     ;; matches... return false
     ((eq? stack '())
      #f)
     (else
      (match stack
        ((stack-item rest-stack ...)
         (match preds
           ((this-pred rest-preds ...)
            (if (this-pred stack-item)
                ;; Nice, we found a match!  cdr down the preds
                (lp rest-preds rest-stack
                    (cons stack-item vals)
                    re-append)
                ;; No match, keep searching the stack
                (begin
                  (limiter-decrement-maybe-abort! limiter program)
                  (lp preds rest-stack
                      vals
                      (cons stack-item re-append))))))))))))

(define* (gush-generic-apply-stack gush-generic program #:optional limiter)
  "Returns a new stack with GUSH-GENERIC applied to it"
  (define methods
    (gush-generic-methods gush-generic))

  (call/ec
   (lambda (return)
     (for-each
      (lambda (method)
        (define preds (gush-method-param-preds method))
        (call-with-values
            (lambda ()
              (find-stack-matches preds program limiter))
          (match-lambda*
            ((vals new-stack)
             (call-with-values
                 (lambda ()
                   (apply (gush-method-proc method) vals))
               (lambda return-values
                 (return
                  (append return-values new-stack)))))
            ;; no match, keep looping
            ((#f) #f))))
      methods)
     ;; We didn't find anything...
     (.values program))))



;; A gush program in progress.
(define-class <program> ()
  ;; The initial program that gets put on the eval stack
  (code #:init-keyword #:code
        #:accessor .code)

  ;; @@: In the future, maybe both the value stack and eval stack
  ;;   will just be stacks on the memories mapping?
  ;; Maybe users will be able to "switch" what's the current eval stack
  ;;   and what's the current value stack?
  ;; That might be dangerous though.
  (eval #:init-value '()
        #:accessor .eval)
  (values #:init-value '()
          #:accessor .values)

  ;; memories is a mapping of keywords -> stacks
  (memories #:init-value (make-fash #:equal eq?)
            #:accessor .memories))

(define-record-type <limiter>
  (make-limiter countdown prompt-tag)
  limiter?
  (countdown limiter-countdown set-limiter-countdown!)
  (prompt-tag limiter-prompt-tag))

(define* (limiter-decrement! limiter #:optional (cost 1))
  (when limiter
    (set-limiter-countdown! limiter (- (limiter-countdown limiter) cost))))

(define* (limiter-hit? limiter)
  (and limiter (negative? (limiter-countdown limiter))))

(define (limiter-abort-to-prompt limiter program)
  (abort-to-prompt (limiter-prompt-tag limiter) program limiter))

(define* (limiter-decrement-maybe-abort! limiter program
                                         #:optional (cost 1))
  (limiter-decrement! limiter cost)
  (when (limiter-hit? limiter)
    (limiter-abort-to-prompt limiter program)))

(define* (run-program program
                      #:key (limit 10000) (env *default-gush-env*)
                      (reset-stacks #t))
  "Run PROGRAM (a <program> object).

With RESET-STACKS set to #t (the default), the value stack will be
cleared out and the exec stack will be loaded with the current state
of the program.

LIMIT is an integer (which will be converted into a <limiter>), or #f.
If LIMIT runs out, will return four values to its continuation: #f, a
continuation to resume execution, the current state of the program at
the time it ended, and the limiter.  The user can then adjust the rate
of the limiter by using (set-limiter-countdown!) then resume the
continuation."
  (let* ((prompt (make-prompt-tag))
         (limiter (and limit (make-limiter limit prompt)))
         ;; Maybe reset the eval/value stacks
         (program (if reset-stacks
                      (clone program
                             ((.eval) (.code program))
                             ((.values) '()))
                      program)))
    (call-with-prompt prompt
      (lambda ()
        (let loop ((program program))
          (match (.eval program)
            ;; program over!
            (() program)
            ((p-item p-rest ...)
             (let ((program (clone program ((.eval) p-rest))))
               (match p-item
                 ;; A symbol? We treat that as a core procedure...
                 ((? symbol? generic-sym)
                  (cond ((get-generic env generic-sym) =>
                         (lambda (generic)
                           (limiter-decrement-maybe-abort!
                            limiter program
                            (gush-generic-cost generic))
                           (loop (clone program
                                        ((.values)
                                         (gush-generic-apply-stack
                                          generic program
                                          limiter))))))
                        ;; @@: For now this kinda logs symbols we don't
                        ;;   know, but maybe that isn't the right approach
                        (else
                         (pk 'unknown-gush-method generic-sym)
                         (loop program))))
                 ;; TODO: list stuff here...
                 ;; We got just a value, so append it to the value stack
                 (val
                  (loop (clone program
                               ((.values)
                                (cons val (.values program))))))))))))
      (lambda (kont program limiter)
        (values #f kont program limiter)))))

(define (run code . extra-args)
  (call-with-values
      (lambda ()
        (apply run-program (make <program> #:code code)
               extra-args))
    (match-lambda*
      (((? (lambda (x) (is-a? x <program>)) prog))
       (.values prog))
      ;; Otherwise, return the values we got
      (vals (apply values vals)))))
