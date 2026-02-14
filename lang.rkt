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

After the step of adding the two "syntactic sugar" terms
`after` and `cut` which expand to `stitch`, we've in fact split
our grammar into two languages - a "core language" and "sugar language".
Here is what we have in principle -

# The core language

SigExprC -> <real>
SigExprC -> (oscil SigExprC)
SigExprC -> (phasor SigExprC)
SigExprC -> (mix SigExprC SigExprC)
SigExprC -> (mod SigExprC SigExprC)
SigExprC -> (line <real> <real> <real>)
SigExprC -> (expon <real> <real> <real>)
SigExprC -> (stitch SigExprC <real> SigExprC)

In this "core language", all the core terms can only contain
other core terms.

# The sugar language

SigExprS -> <real>
SigExprS -> (oscil SigExprS)
SigExprS -> (phasor SigExprS)
SigExprS -> (mix SigExprS SigExprS)
SigExprS -> (mod SigExprS SigExprS)
SigExprS -> (line <real> <real> <real>)
SigExprS -> (expon <real> <real> <real>)
SigExprS -> (stitch SigExprS <real> SigExprS)

; The new sugar terms that differ from the core language.
SigExprS -> (after <real> SigExprS)
SigExprS -> (cut <real> SigExprS)

Our type SigExpr does not capture this difference. The difference is
important because our interpreter's actual type is (-> SigExprC a:Gen)
and `desugar`'s actual type is (-> SigExprS SigExprC).
|#

#|
There is much redundancy in the two grammars since we have to now invent different
names like oscilC and oscilS to distinguish whether the oscil can contain only
core terms or also permits sugar terms. To avoid this redundancy, we
parameterize the term types so we can decide what they can contain later on.
Racket permits this. If (T e) is a type, where e is a type, then T is called
a "type constructor" much like a function is a "value constructor" that transforms
a given argument value into a result value.
|#

(struct (e) oscil ([freq : e]) #:transparent)
(struct (e) phasor ([freq : e]) #:transparent)
(struct (e) mix ([a : e] [b : e]) #:transparent)
(struct (e) mod ([a : e] [b : e]) #:transparent)
(struct line ([start : Real] [dur : Real] [end : Real]) #:transparent)
(struct expon ([start : Real] [dur : Real] [end : Real]) #:transparent)
(struct (e) stitch ([a : e] [dur : Real] [b : e]) #:transparent)
(struct (e) after ([dur : Real] [sig : e]) #:transparent)
(struct (e) cut ([dur : Real] [sig : e]) #:transparent)

#| --change--
In this step, we introduce a real biggie - functions!
The general theme of language development is that a feature that we might
rely on while implementing a language is beneficial at the language
level, at least for general purpose programming languages. For specialist
languages, the restrictions placed will need to be carefully chosen.
First the new (core) terms we need to introduce are the notion of
a "function expression", a reference to an identifier, and an
expression that applies a function to an argument.

SigExprC -> (Fn arg:Symbol expr:SigExprC)
SigExprC -> (id s:Symbol)
SigExprC -> (app SigExprC SigExprC)

So we restrict ourselves to single-argument functions as we know
how to reduce multiple-argument functions as nested single argument
functions and so we can treat them as syntactic sugar.

There are some constraints here we can't impost using our type system
at the moment.

1. When our interpreter evaluates an (id s:Symbol) expression, the
   identifier has to be well defined and have a valid bound value. So
   there is this notion of "an identifier being bound to a value"
   that is also introduced.

2. The first slot of an `app` term must evaluate to a function-value
   so that it can be applied to the second. `app` in essence is expected
   match the LHS of the β-reduction rule of lambda calculus.
|#

(struct (e) fn ([arg : Symbol] [expr : e]) #:transparent)
(struct id ([sym : Symbol]) #:transparent)
(struct (e) app ([fn : e] [arg : e]) #:transparent)

(define-type (SigCoreTerm e) (U Real
                                (oscil e)
                                (phasor e)
                                ; Note that `mix` here refers to the
                                ; type constructor and not the struct's
                                ; value constructor. So it only takes
                                ; one argument as declared in the (struct ...)
                                (mix e)
                                (mod e)
                                line
                                expon
                                (stitch e)
                                (fn e)
                                id
                                (app e)))

; The pure Sugar terms.
(define-type (SigSugarTerm e) (U (after e)
                                 (cut e)))

; Now we're ready to define the SigExprC and SigExprS grammars.

; Here we're saying SigExprC is all the SigCore terms which can only contain
; other SigExprC terms.
(define-type SigExprC (SigCoreTerm SigExprC))

; Here we're saying SigExprS can be any core term that permits other sugar
; terms within it, or any of the sugar terms that also permit other sugar terms
; within them.
(define-type SigExprS (U (SigCoreTerm SigExprS) (SigSugarTerm SigExprS)))

; We introduce the idea of "desugaring" the `after` and `cut` terms
; in terms of `stitch`. What we're saying here is that no matter where
; these terms occur, we want to rewrite those terms in terms of `stitch`.
; One option is to leave the interpreter as is, but it hinders evolving
; the language because now when we add a new term we need to consider the
; correctness of our interpreter with two additional terms to reckon with.
; Hence we declare that `after` and `cut` as "syntactic sugar" and rewrite
; expressions into "core terms" before passing them on to the interpreter.

#| --changes--
So far, the only kind of value the interpreter dealt with was `a:Gen`.
With functions introduced, an expression is no longer constrained to
evaluate to an `a:Gen` value but might also be a function-value which
can be applied to some other value to produce, say, an `a:Gen` or even
another function.

So in this iteration, we make the kinds of values that our interpreter can
produce explicit. This is, in a way, the beginnings of a type system.
Though our language itself has no facility to express types yet, an expression
in our language is only correct as long as the above two mentioned
constraints hold for every (id..) and (app..) sub-expression in a given
expression.
|#

(define-type Val (U GenV FnV))

(struct GenV ([gen : a:Gen]) #:transparent)
(struct FnV ([argname : Symbol] [expr : SigExprC]) #:transparent)



; Now the type of desugar becomes more tight. It must be (-> SigExprS SigExprC)

(: desugar (-> SigExprS SigExprC))
(define (desugar expr)
  (match expr
    [(after dur sig) (stitch 0.0 dur (desugar sig))]
    [(cut dur sig) (stitch (desugar sig) dur 0.0)]

    [(oscil f) (oscil (desugar f))]
    [(phasor f) (phasor (desugar f))]
    [(mix a b) (mix (desugar a) (desugar b))]
    [(mod a b) (mod (desugar a) (desugar b))]
    [(stitch a dur b) (stitch (desugar a) dur (desugar b))]
    [(fn argname expr) (fn argname (desugar expr))]
    [(app fexpr vexpr) (app (desugar fexpr) (desugar vexpr))]
    
    ; We now need to be explicit about the remaining expressions
    [(? real?) expr]
    [(line start dur end) expr]
    [(expon start dur end) expr]
    [(id sym) expr]
    [_ (error 'desugar "Unknown sugar term ~a" expr)]
    ))
#|
The interpreter's job here is to take a SigExpr and produce a a:Gen type value.
Notice that the recursive structure of the expression means our interpreter itself
can use structural recursion to compute its result.
|#

; Useful in circumstances where it is a runtime error for a value
; to be anything other than a GenV.
(: genv (-> Val a:Gen))
(define (genv v)
  (if (GenV? v)
      (GenV-gen v)
      (error 'genv "GenV expected. Got ~a" v)))

; --changes--
; Now our interperter's type also tightens up to (-> SigExprC a:Gen)
(: interp (-> SigExprC Val))
(define (interp expr)
  (match expr
    ; --change--
    ; We now need to wrap the result value appropriately.
    [(? real?) (GenV (a:konst expr))]
    [(oscil f) (GenV (a:oscil (genv (interp f))))]
    [(phasor f) (GenV (a:phasor (genv (interp f))))]
    [(mix a b) (GenV (a:mix (genv (interp a)) (genv (interp b))))]
    [(mod a b) (GenV (a:mod (genv (interp a)) (genv (interp b))))]
    [(line start dur end) (GenV (a:line start dur end))]
    [(expon start dur end) (GenV (a:expon start dur end))]
    [(stitch a dur b) (GenV (a:stitch (genv (interp a)) dur (genv (interp b))))]
    [(id sym) (error 'interp "How to find out symbol value?")]
    [(fn argname expr)
     ; We can't do anything with expr right now until the function
     ; is applied to a value.
     (FnV argname expr)]
    [(app fexpr vexpr) (let ([fval (interp fexpr)]
                             [argval (interp vexpr)])
                         (error 'interp "How to apply FnV to a value?"))]
    [_ (error 'interp "Unknown expression ~a" expr)]))

#|
Try some of the following sample expressions. Run each through the
interpreter and supply the resultant gen to a:write-wav-file like
this - `(a:write-wav-file "filename.wav" result-gen dur-secs gain 48000)`.
Ex: `(write-wav-file "sig5.wav" sig5 3.0 0.25 48000)`
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
(define sig5 (mod (stitch (line 0.0 0.25 1.0)
                          0.25
                          (stitch 1.0 2.0 (line 1.0 0.25 0.0)))
                  (oscil (mix 300.0 (mod 15.0 (oscil 5.0))))))

; (interp sig6) will fail because our interpreter does not know about `after` and `cut`.
; However, (interp (desugar sig6)) will succeed (despite the bug in desugar
; mentioned above).
(define sig6 (mod 0.3
                  (mix (oscil 300.0)
                       (mix (after 0.5 (oscil 450.0))
                            (after 1.0 (oscil 600.0))))))


; NOTE: We can't yet create any examples that use functions because
; we haven't yet implemented β-reduction. That is the next step.


