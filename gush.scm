(use-modules (oop goops)
             (srfi srfi-1)
             (srfi srfi-9)
             (srfi srfi-111)
             (ice-9 match)
             (ice-9 control))

;; mapping of symbol -> <gush-generic>
(define %gush-env (make-parameter (make-hash-table)))

(define-inlinable (get-generic sym gush-env)
  (hashq-ref gush-env sym))

(define-inlinable (set-generic! sym val gush-env)
  (hashq-set! gush-env sym val))

(define (gush-env-add-generic! gush-env sym . args)
  (define generic-args
    (match args
      (((? string? docstring) rest-args ...)
       (cons* #:docstring docstring
              rest-args))))
  (define generic
    (apply make <gush-generic>
         #:sym sym
         generic-args))
  (set-generic! sym generic gush-env))

(define (gush-env-add-method! gush-env gush-method)
  (let* ((sym (.sym gush-method))
         (generic (or (get-generic sym gush-env)
                      (let ((new-generic (make <gush-generic> #:sym sym)))
                        (set-generic! sym new-generic gush-env)
                        new-generic))))
    (set! (.methods generic)
          (cons gush-method (.methods generic)))))

(define-class <gush-generic> ()
  ;; What "symbol" this maps to for read/write
  (sym #:getter .sym
       #:init-keyword #:sym)
  ;; List of methods that implement this generic
  (methods #:accessor .methods
           #:init-value '()
           #:init-keyword #:methods)
  ;; A docstring, if any
  (docstring #:init-value #f
             #:init-keyword #:docstring
             #:accessor .docstring)
  ;; How many cpu "steps" invoking this method costs
  (cost #:init-value 1
        #:init-keyword #:cost
        #:getter .cost))

(define-class <gush-method> ()
  ;; What "symbol" this maps to for read/write
  (sym #:getter .sym
       #:init-keyword #:sym)
  ;; List of predicates mapping to parameters passed to
  ;; this procedure
  (param-preds #:getter .param-preds
               #:init-keyword #:param-preds)
  ;; The actual procedure run
  (proc #:getter .proc
        #:init-keyword #:proc))

(define-syntax-rule (define-gush-generic* gush-env sym
                      args ...)
  (gush-env-add-generic! gush-env (quote sym) args ...))

(define-syntax-rule (define-gush-generic sym
                      args ...)
  (define-gush-generic* (%gush-env) sym
    args ...))

;; emacs: (put 'gush-method 'scheme-indent-function 1)
(define-syntax-rule (gush-method (sym (param pred) ...)
                      body ...)
  (make <gush-method>
    #:sym (quote sym)
    #:param-preds (list pred ...)
    #:proc (lambda (param ...)
             body ...)))

(define-syntax-rule (define-gush-method* gush-env (sym (param pred) ...)
                      body ...)
  "Add a gush method to GUSH-ENV"
  (gush-env-add-method! (%gush-env)
                        (gush-method (sym (param pred) ...) body ...)))

(define-syntax-rule (define-gush-method (sym (param pred) ...)
                      body ...)
  "Add a gush method to the default %gush-env"
  (define-gush-method* (%gush-env) (sym (param pred) ...) body ...))


(define* (find-stack-matches preds stack #:optional limiter)
  "Returns either:
 - #f: matches not found.
 - (items new-stack): a list of items matching PRED from the
   STACK and a new stack with those items removed."
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
                  (limiter-decrement-maybe-abort! limiter)
                  (lp preds rest-stack
                      vals
                      (cons stack-item re-append))))))))))))

(define* (gush-generic-apply-stack gush-generic stack #:optional limiter)
  "Returns a new stack with GUSH-GENERIC applied to it"
  (define methods
    (.methods gush-generic))

  (call/ec
   (lambda (return)
     (for-each
      (lambda (method)
        (define preds (.param-preds method))
        (call-with-values
            (lambda ()
              (find-stack-matches preds stack))
          (match-lambda*
            ((vals new-stack)
             (call-with-values
                 (lambda ()
                   (apply (.proc method) vals))
               (lambda return-values
                 (return
                  (append return-values new-stack)))))
            ;; no match, keep looping
            ((#f) #f))))
      methods)
     ;; We didn't find anything...
     stack)))



;; Some example methods

(define-gush-generic +
  "Foo bar baz"
  #:cost 1)

(define-gush-method (+ (x number?) (y number?))
  (+ x y))



;;; WIP

;; @@: This whole damn thing could be made functional, and maybe
;;   (despite a lot of garbage churn) that would be for the best.
;;   But the main problem is, we'd need a fast hashmap for the
;;   memories... probably fash would do?

;; A gush program in progress.
(define-class <program> ()
  ;; The initial program that gets put on the eval stack
  (code #:init-keyword #:code
        #:getter .code)

  ;; @@: In the future, maybe both the value stack and eval stack
  ;;   will just be stacks on the memories mapping?
  ;; Maybe users will be able to "switch" what's the current eval stack
  ;;   and what's the current value stack?
  ;; That might be dangerous though.
  (eval-stack #:init-value '()
              #:accessor .eval-stack)
  (value-stack #:init-value '()
               #:accessor .value-stack)

  ;; memories is a mapping of keywords -> stacks
  (memories #:init-thunk make-hash-table
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
  (and limiter (positive? (limiter-countdown limiter))))

(define (limiter-abort-to-prompt limiter)
  (abort-to-prompt (limiter-prompt-tag limiter)))

(define* (limiter-decrement-maybe-abort! limiter #:optional (cost 1))
  (limiter-decrement! limiter cost)
  (when (limiter-hit? limiter)
    (limiter-abort-to-prompt limiter)))

(define *current-program*
  (make-parameter #f))

(define* (run-program! program
                       #:key (limit 10000) (env (%gush-env))
                       (reset-stacks #t))
  (when reset-stacks
    ;; Copy code to eval-stack
    (set! (.eval-stack program) (.code program))
    ;; Clear the value stack, if anything is there
    (set! (.value-stack program) '()))
  (let* ((prompt (make-prompt-tag))
         (limiter (and limit (make-limiter limit prompt))))
    (parameterize ((*current-program* program))
      (call-with-prompt prompt
        (lambda ()
          (define (loop)
            (match (.eval-stack program)
              ;; program over!
              (() program)
              ((p-item p-rest ...)
               (match p-item
                 ;; A symbol? We treat that as a core procedure...
                 ((? symbol? generic-sym)
                  (cond ((get-generic generic-sym env) =>
                         (lambda (generic)
                           (set! (.value-stack program)
                                 (gush-generic-apply-stack generic (.value-stack program)))
                           (set! (.eval-stack program)
                                 p-rest)
                           (loop)))
                        ;; Ignore symbols we don't know?
                        ;; @@: Maybe we should no-op, which would
                        ;;   maybe be closer to Push
                        (else
                         (throw 'unknown-gush-method
                                #:sym generic-sym))))
                 ;; TODO: list stuff here...
                 ;; We got just a value, so append it to the value stack
                 (val
                  (set! (.eval-stack program)
                        p-rest)
                  (set! (.value-stack program)
                        (cons val (.value-stack program)))
                  (loop))))))
          (loop)
          (values program #t))
        (lambda ()
          (values program #f))))))

(define (run code . extra-args)
  (.value-stack
   (apply run-program! (make <program> #:code code)
          extra-args)))
