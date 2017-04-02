(use-modules (oop goops)
             (clone)
             (srfi srfi-1)
             (srfi srfi-9)
             (srfi srfi-111)
             (fash)
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
    (.methods gush-generic))

  (call/ec
   (lambda (return)
     (for-each
      (lambda (method)
        (define preds (.param-preds method))
        (call-with-values
            (lambda ()
              (find-stack-matches preds program limiter))
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
     (.values program))))



;; Some example methods

(define-gush-generic +
  "Add two numbers on the stack"
  #:cost 1)

(define-gush-method (+ (x number?) (y number?))
  (+ x y))

(define-gush-method (* (x number?) (y number?))
  (* x y))

(define-gush-method (- (x number?) (y number?))
  (- x y))

(define-gush-method (dup (var (const #t)))
  (values var var))

(define-gush-method (drop (var (const #t)))
  (values))



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
                      #:key (limit 10000) (env (%gush-env))
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
                  (cond ((get-generic generic-sym env) =>
                         (lambda (generic)
                           (limiter-decrement-maybe-abort! limiter program
                                                           (.cost generic))
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
