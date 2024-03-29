;;;; Gush -- stack based language and genetic programming environment
;;;; Copyright (C) 2017 Christopher Allan Webber
;;;;
;;;; This library is free software; you can redistribute it and/or
;;;; modify it under the terms of the GNU Lesser General Public
;;;; License as published by the Free Software Foundation; either
;;;; version 3 of the License, or (at your option) any later version.
;;;;
;;;; This library is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; Lesser General Public License for more details.
;;;;
;;;; You should have received a copy of the GNU Lesser General Public
;;;; License along with this library; if not, write to the Free Software
;;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

(define-module (gush)
  #:use-module (oop goops)
  #:use-module (clone)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-111)
  #:use-module (fash)
  #:use-module (ice-9 match)
  #:use-module (ice-9 control)
  ;; A whole lot more to export...
  #:export (run run-program

            <operation>
            .sym .proc .docstring .cost

            <gush-method> gush-method?
            gush-method-param-preds gush-method-proc

            find-stack-matches
            <gush-generic> .proc .methods

            define-gush-generic
            stack-method define-stack-method
            program-method define-program-method

            op:+ op:- op:* op:/
            op:= op:< op:<= op:> op:>=
            op:drop op:dup
            op:halt op:quote
            op:if op:when

            op:define op:forget op:var-set-stack
            op:var-push op:var-pop op:var-ref
            op:var-quote-pop op:var-quote-ref op:var-quote-stack

            *default-gush-env*

            <program>
            .code .exec .values .vars

            run-program run))


;;; The limiter
;;; ===========

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


;;; Procedures, generics, and environments
;;; ======================================

;; Abstract "procedure" to operate on a stack.
;; (Generics are a specialization of this.)
(define-class <operation> ()
  ;; What "symbol" this maps to in gush code
  (sym #:accessor .sym
       #:init-keyword #:sym)
  ;; Procedure to run... (operation, program, limiter) -> (program, limiter)
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
             (return (apply (gush-method-proc method)
                            (clone program ((.values) new-stack))
                            vals)
                     limiter))
            ;; no match, keep looping
            ((#f) #f))))
      methods)
     ;; We didn't find anything...
     (values program limiter))))

(define-class <gush-generic> (<operation>)
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

;; Construct a wrapper around the method
(define (stack-method-wrapper proc)
  (lambda (program . args)
    (call-with-values (lambda ()
                        (apply proc args))
      (lambda return-values
        (clone program
               ((.values)
                (append return-values (.values program))))))))

;; emacs: (put 'gush-method 'scheme-indent-function 1)
(define-syntax-rule (stack-method ((param pred) ...)
                      body ...)
  (%make-gush-method (list pred ...)
                     (stack-method-wrapper
                      (lambda (param ...)
                        body ...))))

(define-syntax-rule (define-stack-method (generic (param pred) ...)
                      body ...)
  "Append a gush method to the generic SYM"
  (set! (.methods generic)
        (cons (stack-method ((param pred) ...) body ...)
              (.methods generic))))

;;; This annoyingly duplicates the above.  De-dupe it!
(define-syntax-rule (program-method (program (param pred) ...)
                      body ...)
  (%make-gush-method (list pred ...)
                     (lambda (program param ...)
                       body ...)))

(define-syntax-rule (define-program-method (generic program (param pred) ...)
                      body ...)
  "Append a gush method to the generic SYM"
  (set! (.methods generic)
        (cons (program-method (program (param pred) ...) body ...)
              (.methods generic))))


;;; Environment stuff
(define (make-gush-env . operations)
  (let ((env (make-hash-table)))
    (for-each (lambda (operation)
                (hashq-set! env (.sym operation)
                            operation))
              operations)
    env))

(define-inlinable (gush-env-get-proc gush-env sym)
  (hashq-ref gush-env sym))


;; Some example methods

(define anything? (const #t))

(define-gush-generic op:+
  "Add two numbers on the stack"
  #:sym '+)

(define-stack-method (op:+ (x number?) (y number?))
  (+ x y))

(define-gush-generic op:*
  "Multiply two numbers on the stack"
  #:sym '*)

(define-stack-method (op:* (x number?) (y number?))
  (* x y))

(define-gush-generic op:/
  "Divide two numbers on the stack"
  #:sym '/)

(define-stack-method (op:/ (x number?) (y number?))
  (/ x y))

(define-gush-generic op:-
  "Subtract two numbers on the stack"
  #:sym '-)

(define-stack-method (op:- (x number?) (y number?))
  (- x y))

(define-gush-generic op:=
  "(values: x <number>, y <number>) check if X and Y are numerically equivalent"
  #:sym '=)

(define-stack-method (op:= (x number?) (y number?))
  (= x y))

(define-gush-generic op:<
  "(values: x <number>, y <number>) check if X is less than Y"
  #:sym '<)

(define-stack-method (op:< (x number?) (y number?))
  (< x y))

(define-gush-generic op:<=
  "(values: x <number>, y <number>) check if X is less than or equal to Y"
  #:sym '<=)

(define-stack-method (op:<= (x number?) (y number?))
  (<= x y))

(define-gush-generic op:>
  "(values: x <number>, y <number>) check if X is greater than Y"
  #:sym '>)

(define-stack-method (op:> (x number?) (y number?))
  (> x y))

(define-gush-generic op:>=
  "(values: x <number>, y <number>) check if X is greater than or equal to Y"
  #:sym '>=)

(define-stack-method (op:>= (x number?) (y number?))
  (>= x y))

(define-gush-generic op:dup
  "Duplicate the top item on the stack"
  #:sym 'dup)

(define-stack-method (op:dup (var anything?))
  (values var var))

(define-gush-generic op:drop
  "Drop the top item on the stack"
  #:sym 'drop)

(define-stack-method (op:drop (var anything?))
  (values))

;; @@: Dangerous?  Equiv to EXEC.FLUSH in Push anyway
(define op:halt
  (make <operation>
    #:sym 'halt
    #:cost 0
    #:docstring "Stop the program completely by wiping the exec stack."
    #:proc (lambda (operation program limiter)
             (values (clone program ((.exec) '()))
                     limiter))))

;; Memory things
(define op:quote
  (make <operation>
    #:sym 'quote
    #:docstring
    "Push the next item from the exec stack onto the value stack, without applying."
    #:proc (lambda (operation program limiter)
             (match (.exec program)
               ;; Quote the item as-is onto the values stack
               ((exec-item exec-rest ...)
                (values (clone program
                               ((.values) (cons exec-item
                                                (.values program)))
                               ((.exec) exec-rest))
                        limiter))
               ;; nothing to do, so just return the program as-is
               (() (values program limiter))))))

;;; Conditionals
(define op:if
  (make <operation>
    #:sym 'if
    #:docstring
    "Checks if last item on values stack is truthy (ie, not #f).  If so,
executes top item on exec stack; otherwise execs second item on exec
stack.  If nothing is on the values stack, this no-ops."
    #:proc (lambda (operation program limiter)
             (match (.values program)
               ;; no-op if nothing is on the values stack
               ;; @@: Should we instead execute the truthy or falsey option?
               ;;   probably not?
               (() program)
               ;; if the top item is false, then we execute the second
               ;; option on the exec stack (by simply preserving it)
               ((#f rest-vals ...)
                (match (.exec program)
                  ;; if there's only one variable on the exec stack
                  ;; we just pop the #f from the values stack
                  ;; (but we always clear the exec stack)
                  ;; @@: For some reason or in (ice-9 match) doesn't want
                  ;;   to work with this, so... we duplicate it for each
                  ;;   possible match
                  (()
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) '())))
                  ((if-exec)
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) '())))
                  ;; Whoo, everything we need!  We're going for else-exec!
                  ((if-exec else-exec rest-exec ...)
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) (cons else-exec rest-exec))))))
               ;; Otherwise, it must be true!
               ((truthy-val rest-vals ...)
                (match (.exec program)
                  ;; if there's only one variable on the exec stack
                  ;; or a truthy value, we just pop the truthy value
                  ;; from the values stack
                  (()
                   (clone program
                          ((.values) rest-vals)))
                  ((if-exec)
                   (clone program
                          ((.values) rest-vals)))
                  ;; Whoo, everything we need!  We're going for if-exec!
                  ((if-exec else-exec rest-exec ...)
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) (cons if-exec rest-exec))))))))))

(define op:when
  (make <operation>
    #:sym 'when
    #:docstring
    "Checks if last item on values stack is truthy (ie, not #f).  If so,
executes top item on exec stack, otherwise drops it.  (There is no else branch
in when.)"
    #:proc (lambda (operation program limiter)
             (match (.values program)
               ;; no-op if nothing is on the values stack
               (() program)
               ;; if the top item is false, then we remove the top exec
               ;; item
               ((#f rest-vals ...)
                (match (.exec program)
                  ;; If there's nothing on the stack, just pop
                  ;; #f from the values stack
                  (()
                   (clone program
                          ((.values) rest-vals)))
                  ;; if there's only one variable on the exec stack
                  ;; we just pop the #f from the values stack
                  ((if-exec)
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) '())))
                  ;; If there are multiple items, we drop the if
                  ((if-exec rest-exec ...)
                   (clone program
                          ((.values) rest-vals)
                          ((.exec) rest-exec)))))
               ;; Otherwise, it must be true!
               ;; And in this case, that means we leave the exec stack
               ;; as-is (since we're keeping the top item) but we drop
               ;; the top item from the stack regardless.
               ((truthy-val rest-vals ...)
                (clone program ((.values) rest-vals)))))))


;;; Variable operations

(define-gush-generic op:define
  "(values: var <symbol>, val <any>) Set the memory stack of VAR to VAL,
erasing any other content previously on the stack"
  #:sym 'define)

(define-program-method (op:define program (var-sym symbol?) (val anything?))
  (clone program
         ((.vars)
          (fash-set (.vars program) var-sym (list val)))))

(define-gush-generic op:forget
  "(values: var <symbol>) Forget the value of VAR altogether"
  #:sym 'forget)

;; @@: Not ideal, we lack a fash-delete
(define-program-method (op:forget program (var-sym symbol?))
  (clone program
         ((.vars)
          (fash-set (.vars program) var-sym '()))))

(define-gush-generic op:var-set-stack
  "(values: var <symbol>, stack <list>) Replace contents of VAR with STACK (a list)"
  #:sym 'var-set-stack)

(define-program-method (op:var-set-stack program (var-sym symbol?)
                                           (stack proper-list?))
  (clone program
         ((.vars)
          (fash-set (.vars program) var-sym
                    stack))))


(define-gush-generic op:var-push
  "(values: var <symbol>, val <any>) Push VAL onto VAR's stack"
  #:sym 'var-push)

(define-program-method (op:var-push program (var-sym symbol?) (val anything?))
  (let ((current-var-stack (fash-ref (.vars program) var-sym (const '()))))
    (clone program
           ((.vars)
            (fash-set (.vars program) var-sym
                      (cons val current-var-stack))))))

(define-gush-generic op:var-pop
  "(values: var <symbol>) Pop value of VAR from its stack onto the exec stack"
  #:sym 'var-pop)

(define-program-method (op:var-pop program (var-sym symbol?))
  (match (fash-ref (.vars program) var-sym)
    ;; Nothing there, or an empty stack; return program as-is
    ((or #f ()) program)
    ;; Otherwise, pull first value off the stack
    ((stack-val rest-stack ...)
     (clone program
            ;; Pop item off of the vars stack
            ((.vars) rest-stack)
            ;; Put it on the exec stack
            ((.exec) (cons stack-val (.exec program)))))))

(define-gush-generic op:var-ref
  "(values: var <symbol>) Put top value of VAR onto the exec stack"
  #:sym 'var-ref)

(define-program-method (op:var-ref program (var-sym symbol?))
  (match (fash-ref (.vars program) var-sym)
    ;; Nothing there, or an empty stack; return program as-is
    ((or #f ()) program)
    ;; Otherwise, reference first value from stack
    ((stack-val rest-stack ...)
     (clone program
            ;; Put it on the exec stack
            ((.exec) (cons stack-val (.exec program)))))))

(define-gush-generic op:var-quote-pop
  "(values: var <symbol>) Pop value of VAR from its stack onto the values stack without evaluating"
  #:sym 'var-quote-pop)

(define-program-method (op:var-quote-pop program (var-sym symbol?))
  (match (fash-ref (.vars program) var-sym)
    ;; Nothing there, or an empty stack; return program as-is
    ((or #f ()) program)
    ;; Otherwise, pull first value off the stack
    ((stack-val rest-stack ...)
     (clone program
            ;; Pop item off of the vars stack
            ((.vars) rest-stack)
            ;; Put it on the vals stack
            ((.values) (cons stack-val (.values program)))))))

(define-gush-generic op:var-quote-ref
  "(values: var <symbol>) Put top value of VAR onto the values stack without evaluating"
  #:sym 'var-quote-ref)

(define-program-method (op:var-quote-ref program (var-sym symbol?))
  (match (fash-ref (.vars program) var-sym)
    ;; Nothing there, or an empty stack; return program as-is
    ((or #f ()) program)
    ;; Otherwise, reference first value from stack
    ((stack-val rest-stack ...)
     (clone program
            ;; Put it on the vals stack
            ((.values) (cons stack-val (.values program)))))))

;; @@: Why no var-stack but a var-quote-stack?  Referencing a defined
;;   variable does what var-stack would do anyway!

(define-gush-generic op:var-quote-stack
  "(values: var <symbol>) Put entire contents of VAR onto the values stack without evaluating"
  #:sym 'var-quote-stack)

(define-program-method (op:var-quote-stack program (var-sym symbol?))
  (match (fash-ref (.vars program) var-sym)
    ;; Nothing there, or an empty stack; return program as-is
    ((or #f ()) program)
    ;; Otherwise, reference the entire stack
    (stack
     (clone program
            ;; Put it on the vals stack
            ((.values) (cons stack (.values program)))))))

(define *default-gush-env*
  (make-gush-env op:+ op:- op:* op:/
                 op:= op:< op:<= op:> op:>=
                 op:drop op:dup
                 op:halt op:quote
                 op:if op:when

                 op:define op:forget op:var-set-stack
                 op:var-push op:var-pop op:var-ref
                 op:var-quote-pop op:var-quote-ref op:var-quote-stack))



;; A gush program in progress.
(define-class <program> ()
  ;; The initial program that gets put on the exec stack
  (code #:init-keyword #:code
        #:accessor .code)

  ;; Program instructions queued to be executed (also a stack)
  (exec #:init-value '()
        #:accessor .exec)
  ;; Values this program has built up; aka "the stack"
  ;; (even though there multiple stacks)
  (values #:init-value '()
          #:accessor .values)

  ;; vars is a mapping of keywords -> stacks
  (vars #:init-value (make-fash #:equal eq?)
        #:accessor .vars))

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
                         (lambda (operation)
                           (let ((run-proc (.proc operation)))
                             (limiter-decrement-maybe-abort!
                              limiter program
                              (.cost operation))
                             (loop (run-proc operation program
                                             limiter)))))
                        (else
                         ;; Insert a variable onto the exec stack if appropriate.
                         ;; Note that variables are themselves stacks, so the default
                         ;; fash-ref value of #f is fine even, since the "value" of #f
                         ;; would be '(#f)
                         (let* ((var-val (fash-ref (.vars program)
                                                   proc-sym)))
                           (if var-val
                               ;; Put the variable's value on the exec stack
                               (loop (clone program
                                            ((.exec) (cons var-val
                                                           (.exec program)))))
                               ;; We haven't defined this, so put quoted variable
                               ;; on the values stack
                               (loop (clone program
                                            ((.values) (cons proc-sym
                                                             (.values program))))))))))
                 ;; Unwrap lists to be applied to the exec stack
                 ((? proper-list? lst)
                  (limiter-decrement-maybe-abort! limiter program)
                  (loop (clone program
                               ((.exec) (append lst (.exec program))))))
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
