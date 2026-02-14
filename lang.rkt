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

-- change --
In our context, it is cumbersome to have to write (konst 3.0) whenever
we want to use a fixed value for a particular SigExpr position. If we
have to make this change in the underlying library, every operator will
have to implement it. However, if we declare that in our language that
"a real number used in a SigExpr stands for a value that remains unchanged
over time", we can simplify our expressions.

SigExpr -> <real>
SigExpr -> (oscil SigExpr)
SigExpr -> (phasor SigExpr)
SigExpr -> (mix SigExpr SigExpr)
SigExpr -> (mod SigExpr SigExpr)

-- added terms --
SigExpr -> (line <real> <real> <real>)
SigExpr -> (expon <real> <real> <real>)

|#


; konst is replaced with Real in the line below.
(define-type SigExpr (U Real oscil phasor mix mod line expon))

(struct oscil ([freq : SigExpr]) #:transparent)
(struct phasor ([freq : SigExpr]) #:transparent)
(struct mix ([a : SigExpr] [b : SigExpr]) #:transparent)
(struct mod ([a : SigExpr] [b : SigExpr]) #:transparent)

; -- added terms --
; These help expand what we can do in our language through addition
; of new "primitives". Note that here the Real values do not stand
; for "signals". Only when a real number is present in a SigExpr position
; is it considered to be a constant signal. Here, Real numbers are just
; uninterpreted real values we pass on as is to the asynth.rkt module.
(struct line ([start : Real] [dur : Real] [end : Real]) #:transparent)
(struct expon ([start : Real] [dur : Real] [end : Real]) #:transparent)

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
    ; This ? syntax for the pattern here says that this pattern matches
    ; if the `(real? expr)` evaluates to `#t`. You can see in the definition
    ; of the type SigExpr above that `Real` is also a possible expression.
    ; This one line adds a new interpretation for real numbers used in SigExpr
    ; positions as "a signal yielding a value constant in time".
    [(? real?) (a:konst expr)]
    [(oscil f) (a:oscil (interp f))]
    [(phasor f) (a:phasor (interp f))]
    [(mix a b) (a:mix (interp a) (interp b))]
    [(mod a b) (a:mod (interp a) (interp b))]
    [(line start dur end) (a:line start dur end)] ; Note the args remain uninterpreted.
    [(expon start dur end) (a:expon start dur end)]
    [_ (error 'interp "Unknown expression ~a" expr)]))

#|
Try some of the following sample expressions. Run each through the
interpreter and supply the resultant gen to a:write-wav-file like
this - `(a:write-wav-file "filename.wav" result-gen dur-secs gain 48000)`.
|#

; -- changes --
; Note that the expressions are now simpler to write since we adopted a new
; meaning for real numbers used in SigExpr positions.
(define sig1 (oscil 300.0))
(define sig2 (mix (oscil 300.0)
                  (mix (oscil 450.0)
                       (oscil 600.0))))
(define sig3 (phasor (mix 300.0
                          (mod 15.0
                               (oscil 5.0)))))
(define sig4 (mod (line 1.0 2.0 0.0)
                  (oscil (mix 300.0 (mod 15.0 (oscil 5.0))))))




