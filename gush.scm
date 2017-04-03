(use-modules (oop goops)
             (clone)
             (srfi srfi-1)
             (srfi srfi-9)
             (srfi srfi-111)
             (fash)
             (ice-9 match)
             (ice-9 control))


;;; Procedures, generics, and environments
;;; ======================================

;; Abstract "procedure" to operate on a stack.
;; (Generics are a specialization of this.)
(define-class <applicable> ()
  ;; What "symbol" this maps to in gush code
  (sym #:accessor .sym
       #:init-keyword #:sym)
  ;; Procedure to run... (applicable, program, limiter) -> (program, limiter)
  (proc #:init-keyword #:proc
        #:accessor .proc)
  ;; Optional docstring
  (docstring #:init-keyword #:docstring
             #:init-value #f
             #:getter .docstring)
  ;; How many cpu "steps" invoking this method costs
  (cost #:init-keyword #:cost
        #:init-value 1
        #:getter .cost))

(define-record-type <gush-method>
  (%make-gush-method param-preds proc)
  gush-method?
  (param-preds gush-method-param-preds)
  (proc gush-method-proc))

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

(define* (gush-generic-apply-stack gush-generic program limiter)
  "Returns a new stack with GUSH-GENERIC applied to it"
  (define methods
    (.methods gush-generic))

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
                 (return (clone program ((.values)
                                         (append return-values new-stack)))
                         limiter))))
            ;; no match, keep looping
            ((#f) #f))))
      methods)
     ;; We didn't find anything...
     (values program limiter))))

(define-class <gush-generic> (<applicable>)
  ;; We use gush-generic-apply as a very specific meta-procedure
  ;; for generics
  (proc #:accessor .proc
        #:allocation #:class
        #:init-value gush-generic-apply-stack)
  ;; List of methods that implement this generic
  (methods #:accessor .methods
           #:init-value '()
           #:init-keyword #:methods))

;; @@: We could deprecate this and just put into define-gush-generic?
(define* (make-gush-generic defined-sym
                            #:optional docstring
                            #:key (cost 1)
                            (methods '())
                            (sym defined-sym))
  (make <gush-generic>
    #:sym sym #:methods methods
    #:docstring docstring #:cost cost))

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
  (set! (.methods generic)
        (cons (gush-method ((param pred) ...) body ...)
              (.methods generic))))

;;; Environment stuff
(define (make-gush-env . applicables)
  (let ((env (make-hash-table)))
    (for-each (lambda (applicable)
                (hashq-set! env (.sym applicable)
                            applicable))
              applicables)
    env))

(define-inlinable (gush-env-get-proc gush-env sym)
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

;; @@: Dangerous?  Equiv to EXEC.FLUSH in Push anyway
(define gush:exit
  (make <applicable>
    #:sym 'exit
    #:cost 0
    #:proc (lambda (applicable program limiter)
             (values (clone program ((.exec) '()))
                     limiter))))

(define *default-gush-env*
  (make-gush-env gush:+ gush:* gush:-
                 gush:drop gush:dup
                 gush:exit))



;; A gush program in progress.
(define-class <program> ()
  ;; The initial program that gets put on the exec stack
  (code #:init-keyword #:code
        #:accessor .code)

  ;; @@: In the future, maybe both the value stack and exec stack
  ;;   will just be stacks on the memories mapping?
  ;; Maybe users will be able to "switch" what's the current exec stack
  ;;   and what's the current value stack?
  ;; That might be dangerous though.
  (exec #:init-value '()
        #:accessor .exec)
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
         ;; Maybe reset the exec/value stacks
         (program (if reset-stacks
                      (clone program
                             ((.exec) (.code program))
                             ((.values) '()))
                      program)))
    (call-with-prompt prompt
      (lambda ()
        (let loop ((program program))
          (match (.exec program)
            ;; program over!
            (() program)
            ((p-item p-rest ...)
             (let ((program (clone program ((.exec) p-rest))))
               (match p-item
                 ;; A symbol? We treat that as a core procedure...
                 ((? symbol? proc-sym)
                  (cond ((gush-env-get-proc env proc-sym) =>
                         (lambda (applicable)
                           (let ((run-proc (.proc applicable)))
                             (limiter-decrement-maybe-abort!
                              limiter program
                              (.cost applicable))
                             (loop (run-proc applicable program
                                             limiter)))))
                        ;; @@: For now this kinda logs symbols we don't
                        ;;   know, but maybe that isn't the right approach
                        (else
                         (pk 'unknown-gush-method proc-sym)
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
