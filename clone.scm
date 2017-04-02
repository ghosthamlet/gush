;; Copyright (C) 2017 Christopher Allan Webber

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

;;; GOOPS cloning library.

;; Inspired by a conversation with Jan Nieuwenhuizen... thanks for the
;; help, Jan!

(define-module (clone)
  #:use-module (oop goops)
  #:use-module (ice-9 match)
  #:export (clone
            do-clone))

(define (do-clone obj adjust-fields)
  (define new (shallow-clone obj))
  ;; The following two procedures allow us to support both
  ;; slot-ref/set! for quoted fields and accessors
  (define (field-set! field new-obj val)
    (match field
      ((? symbol? slot-name)
       (slot-set! new-obj slot-name val))
      ((? procedure? accessor)
       (set! (accessor new-obj) val))))
  (define (field-ref field new-obj)
    (match field
      ((? symbol? slot-name)
       (slot-ref new-obj slot-name ))
      ;; @@: We could use procedure-with-setter? but only on guile 2.2
      ((? procedure? accessor)
       (accessor new-obj))))
  (for-each
   (match-lambda
     ;; Apply just this one field
     (((field) val)
      (field-set! field new val))
     ;; Recursively apply fields
     (((field recur-fields ...) val)
      (field-set! field new
                  (do-clone (field-ref field new)
                            (list (list recur-fields val))))))
   adjust-fields)
  new)

(define-syntax-rule (clone obj ((fields ...) val) ...)
  "Clone GOOPS object with fields adjusted to new values.

Interface is similar to (srfi srfi-9 gnu)'s set-fields.

For example:

  (define-class <address> ()
    (street #:init-keyword #:street
            #:accessor .street)
    (city #:init-keyword #:city
          #:accessor .city)
    (country #:init-keyword #:country
             #:accessor .country))

  (define-class <person> ()
    (age #:init-keyword #:age
         #:accessor .age)
    (email #:init-keyword #:email
           #:accessor .email)
    (address #:init-keyword #:address
             #:accessor .address))

  (define fsf-address
    (make <address>
      #:street \"Franklin Street\"
      #:city \"Boston\"
      #:country \"USA\"))

  (define rms
    (make <person>
      #:age 30
      #:email \"rms@gnu.org\"
      #:address fsf-address))

  (define new-rms
    (clone rms
           (('age) 60)                            ; can use quoted slots
           ((.address .street) \"Temple Place\")))  ; or accessors"
  (do-clone obj
            (list (list (list fields ...) val) ...)))
