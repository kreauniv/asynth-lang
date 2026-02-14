#lang typed/racket

#|
In this file, we'll incrementally build up an interpreter for
the "audio synth language" for which an implementation has been
provided in the "asynth.rkt" file in this directory. To follow
its evolution, look at the git history of this file along with
the commit comments and the comments here. The text here will
leave out details and the rationale behind the design of the
asynth.rkt module itself ... but we'll discuss that in class.
Use this as a reminder or "sign posts" for where to go from
wherever you landed.
|#

(require
  (prefix-in a: "./asynth.rkt") ; Prefix the exports with a: to
                                ; avoid name clashes.
  racket/match)

#|
We start with limited expressions in the language, which we
express as a grammar. Expression languages are generally simple
since every expression is expected to be reducible to a "value"
of some sort and expressions are composed of other expressions.
The lambda calculus is itself an expression language.
|#

#|  The Grammar:

SigExpr -> konst <real>
SigExpr -> oscil SigExpr
SigExpr -> phasor SigExpr
SigExpr -> mix SigExpr SigExpr
SigExpr -> mod SigExpr SigExpr

|#

(define-type SigExpr (U konst oscil phasor mix mod))

(struct konst ([val : Real]) #:transparent)
(struct oscil ([freq : SigExpr]) #:transparent)
(struct phasor ([freq : SigExpr]) #:transparent)
(struct mix ([a : SigExpr] [b : SigExpr]) #:transparent)
(struct mod ([a : SigExpr] [b : SigExpr]) #:transparent)

#|
Notice how the structure is recursively defined. This is a common trait in
every programming language because the intent of a language is to permit a
wide variety of *compositions* of the constructs of the language and recursive
structures permit an (countably) infinite set of possibilities.
|#

#|
The interpreter's job here is to take a SigExpr and produce a a:Gen type value.
Notice that the recursive structure of the expression means our interpreter itself
can use structural recursion to compute its result.

|#

(: interp (-> SigExpr a:Gen))
(define (interp expr)
  (match expr
    [(konst v) (a:konst v)]
    [(oscil f) (a:oscil (interp f))]
    [(phasor f) (a:phasor (interp f))]
    [(mix a b) (a:mix (interp a) (interp b))]
    [(mod a b) (a:mod (interp a) (interp b))]
    [_ (error 'interp "Unknown expression ~a" expr)]))

#|
Try some of the following sample expressions. Run each through the
interpreter and supply the resultant gen to a:write-wav-file like
this - `(a:write-wav-file "filename.wav" result-gen dur-secs gain 48000)`.
|#

(define sig1 (oscil (konst 300.0)))
(define sig2 (mix (oscil (konst 300.0))
                  (mix (oscil (konst 450.0))
                       (oscil (konst 600.0)))))
(define sig3 (phasor (mix (konst 300.0)
                          (mod (konst 15.0)
                               (oscil (konst 5.0))))))
           



