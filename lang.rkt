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
  ; Prefix the exports with a: to avoid name clashes.
  (prefix-in a: "./asynth.rkt")
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

--changes--
In the places where we expect ordinary real numbers as parameters to
define generators, we might want to compute them using arithmetic. So
here is a small sub-language to do that. This RExpr term essentially
can replace all the <real> positions in the above grammars.

RExpr -> <real>
RExpr -> (r+ RExpr RExpr)
RExpr -> (r- RExpr RExpr)
RExpr -> (r* RExpr RExpr)
RExpr -> (r/ RExpr RExpr)
RExpr -> (sign RExpr)
RExpr -> (fn <id> RExpr)
RExpr -> (id <id>)
RExpr -> (app RExpr RExpr)

Notice that this could also use functions and the function evaluation mechanism.
So it can be prudent to merge this sub-language into the core language so that
common mechanisms can apply. However, since our RExpr sub-language has no
sugar terms, it doesn't currently need any desugaring.

--booleans--
We can use our functions to express booleans quite easily without having
to introduce extra primitives or incurring performance loss. But it
will be good to have some syntactic sugar for convenience and also to
illustrate how common constructs reduce to simpler constructs like lambda.

True -> (fn 'a (fn 'b (id 'a)))
False -> (fn 'a (fn 'b (id 'b)))
(if c t e) -> (app (app c t) e)
(and a b) -> (app (app a b) False)
(or a b) -> (app (app a True) b)
(not a) -> ((app a False) True)

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
(struct (e) line ([start : e] [dur : e] [end : e]) #:transparent)
(struct (e) expon ([start : e] [dur : e] [end : e]) #:transparent)
(struct (e) stitch ([a : e] [dur : e] [b : e]) #:transparent)
(struct (e) after ([dur : e] [sig : e]) #:transparent)
(struct (e) cut ([dur : e] [sig : e]) #:transparent)

; --changes--
; New primitives
(struct (e) sign ([sig : e]) #:transparent)
(struct (e) switch ([sign : e] [pos : e] [neg : e]) #:transparent)

#|
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

; --changes--
; arithmetic operators
(struct (e) r+ ([a : e] [b : e]) #:transparent)
(struct (e) r- ([a : e] [b : e]) #:transparent)
(struct (e) r* ([a : e] [b : e]) #:transparent)
(struct (e) r/ ([a : e] [b : e]) #:transparent)

; Booleans
(struct (e) band ([a : e] [b : e]) #:transparent)
(struct (e) bor ([a : e] [b : e]) #:transparent)
(struct (e) bnot ([a : e]) #:transparent)
(struct (c e) bif ([b : c] [then : e] [else : e]) #:transparent)
(struct (e) lt ([a : e] [b : e]) #:transparent) ; Bridges the world of real numbers and booleans.
(define btrue (fn 'a (fn 'b (id 'a))))
(define bfalse (fn 'a (fn 'b (id 'b))))

;--change--
; Real is no longer a part of SigCoreTerm and konst must be used explicitly.
; So it looks like we gave up our convenience, but we can always add it back
; as sugar for konst since our desugar only deals with signal expressions
; and not numeric computations. When we introduce numeric sugar terms as well,
; we will have to refine it.
(define-type (SigCoreTerm e) (U Real
                                (oscil e)
                                (phasor e)
                                ; Note that `mix` here refers to the
                                ; type constructor and not the struct's
                                ; value constructor. So it only takes
                                ; one argument as declared in the (struct ...)
                                (mix e)
                                (mod e)
                                (sign e)
                                (line e)
                                (expon e)
                                (stitch e)
                                (sign e)
                                (switch e)

                                (fn e)
                                id
                                (app e)
                                (r+ e) (r- e) (r* e) (r/ e)
                                (lt e)
                                ))

;--change--
; The pure Sugar terms. Note that Real is now a considered a sugar for konst.
(define-type (SigSugarTerm c e) (U Real
                                   Boolean
                                   (after e)
                                   (cut e)
                                   (band e)
                                   (bor e)
                                   (bnot e)
                                   (bif c e)
                                   ))

; Now we're ready to define the SigExprC and SigExprS grammars.

; Here we're saying SigExprC is all the SigCore terms which can only contain
; other SigExprC terms or expressions which compute real numbers but since
; our sugar terms only compute signals, we cannot have any sugar terms in
; real-number expressions, as there is no mechanism to derive real numbers
; out of signals within our language. When we do add such a feature, this
; will need to be tweaked.
(define-type SigExprC (SigCoreTerm SigExprC))

; Here we're saying SigExprS can be any core term that permits other sugar
; terms within it, or any of the sugar terms that also permit other sugar terms
; within them. Here we are leaving the resolution of whether an expression is
; valid in the "condition" position of bif to the runtime.
(define-type SigExprS (U (SigCoreTerm SigExprS)
                         (SigSugarTerm SigExprS SigExprS)))


; We introduce the idea of "desugaring" the `after` and `cut` terms
; in terms of `stitch`. What we're saying here is that no matter where
; these terms occur, we want to rewrite those terms in terms of `stitch`.
; One option is to leave the interpreter as is, but it hinders evolving
; the language because now when we add a new term we need to consider the
; correctness of our interpreter with two additional terms to reckon with.
; Hence we declare that `after` and `cut` as "syntactic sugar" and rewrite
; expressions into "core terms" before passing them on to the interpreter.

#|
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

(define-type Val (U GenV FnV RealV))

(struct GenV ([gen : a:Gen]) #:transparent)
; Here we've added an additional slot to store an "environment"
; - the **definition environment**. See the notes in the relevant
; part of the interpreter below for more about this.
(struct FnV ([denv : Env]
             [argname : Symbol]
             [expr : SigExprC]) #:transparent)
(struct RealV ([r : Real]) #:transparent)

; Now the type of desugar becomes more tight. It must be (-> SigExprS SigExprC)

(: desugar (-> SigExprS SigExprC))
(define (desugar expr)
  (match expr
    [(? real?) expr]
    [(after dur sig) (stitch 0.0 (desugar dur) (desugar sig))]
    [(cut dur sig) (stitch (desugar sig) (desugar dur) 0.0)]

    [#t btrue]
    [#f bfalse]
    [(band a b) (app (app (desugar a) (desugar b)) bfalse)]
    [(bor a b) (app (app (desugar a) (desugar #t)) (desugar b))]
    [(bnot a) (app (app (desugar a) bfalse) btrue)]
    [(bif c t e) (app (app (desugar c) (desugar t)) (desugar e))]

    [(oscil f) (oscil (desugar f))]
    [(phasor f) (phasor (desugar f))]
    [(mix a b) (mix (desugar a) (desugar b))]
    [(mod a b) (mod (desugar a) (desugar b))]
    [(fn argname expr) (fn argname (desugar expr))]
    [(app fexpr vexpr) (app (desugar fexpr) (desugar vexpr))]
    [(stitch a dur b) (stitch (desugar a) (desugar dur) (desugar b))]

    ; Some new primitives
    [(sign expr) (sign (desugar expr))]
    [(switch c pos neg) (switch (desugar c)
                                (desugar pos)
                                (desugar neg))]

    ; The rest are to be left without recursive desugaring.
    [(line start dur end) (line (desugar start)
                                (desugar dur)
                                (desugar end))]
    [(expon start dur end) (expon (desugar start)
                                  (desugar dur)
                                  (desugar end))]
    [(r+ a b) (r+ (desugar a) (desugar b))]
    [(r- a b) (r- (desugar a) (desugar b))]
    [(r* a b) (r* (desugar a) (desugar b))]
    [(r/ a b) (r/ (desugar a) (desugar b))]
    [(lt a b) (lt (desugar a) (desugar b))]
    [(id sym) (id sym)]
    [_ (error 'desugar "Unknown signal expression to desugar ~a" expr)]))

#|
The interpreter's job here is to take a SigExpr and produce a a:Gen type value.
Notice that the recursive structure of the expression means our interpreter itself
can use structural recursion to compute its result.
|#


#|
The branch for interpreting (id sym) below requires a new concept
within our interpreter - what value should the interpreter produce
when encountering an identifier term?

Pretty much the only thing that can be done with the symbol is
to get a value by looking it up from some table of symbol-value
associations. We'll call such as set of associations an "environment".

We'll use a simple implementation of such symbol-value lookup
- using lambda functions.
|#

(define-type Env (-> Symbol Val))
(define empty-env (λ (sym) (error 'env "Unknown symbol ~a" sym)))

(: extend (-> Env Symbol Val Env))
(define (extend env sym value)
  (λ (k)
    (if (equal? k sym)
        value
        (lookup env k))))

(: lookup (-> Env Symbol Val))
(define (lookup env sym) (env sym))

; Now our interpreter needs to be augmented with a "current environment"
; using which we'll lookup a given identifier's value.
(: interp (-> Env SigExprC Val))
(define (interp env expr)
  (match expr
    ;--change--
    ; Now real values in our language can have two meanings -
    ; 1. As part of the computation of a constant to be used for
    ;    for terms like stitch. In this case, they should be
    ;    RealV values.
    ; 2. As part of specification of signals, in which case they
    ;    need to be treated as `konst` signals.
    ; This meaning is determined at runtime depending on where these
    ; are encountered. The (realv ..) and (genv ..) are the ones that
    ; assert this, leaving us free to use ordinary real numbers
    ; for both numerical calculations as well as for konst signals.
    [(? real?) (RealV expr)]
    
    [(oscil f) (GenV (a:oscil (genv (interp env f))))]
    [(phasor f) (GenV (a:phasor (genv (interp env f))))]
    [(mix a b) (GenV (a:mix (genv (interp env a))
                            (genv (interp env b))))]
    [(mod a b) (GenV (a:mod (genv (interp env a))
                            (genv (interp env b))))]

    [(line start dur end) (GenV (a:line
                                 (realv (interp env start))
                                 (realv (interp env dur))
                                 (realv (interp env end))))]
    [(expon start dur end) (GenV (a:expon
                                  (realv (interp env start))
                                  (realv (interp env dur))
                                  (realv (interp env end))))]
    [(stitch a dur b) (GenV (a:stitch (genv (interp env a))
                                      (realv (interp env dur))
                                      (genv (interp env b))))]

    ; Now interpreting an (id..) term is just a matter of looking up
    ; the value associated with the symbol in the current environment.
    ; If the symbol has no such associated value, the expression is in
    ; error and a runtime error will be raised by `lookup`.
    [(id sym) (lookup env sym)]

    ; With these arithmetic terms, we can now calculate some of the
    ; numeric arguments to our signal operators.
    [(r+ a b) (RealV (+ (realv (interp env a)) (realv (interp env b))))]
    [(r- a b) (RealV (- (realv (interp env a)) (realv (interp env b))))]
    [(r* a b) (RealV (* (realv (interp env a)) (realv (interp env b))))]
    [(r/ a b) (RealV (/ (realv (interp env a)) (realv (interp env b))))]
    [(lt a b) (boolv (< (realv (interp env a))
                        (realv (interp env b))))]
    
    [(fn argname expr)
     ; Here we are examining an (fn..) term and constructing a FnV
     ; value. When the resultant function is applied, what is the
     ; environment that needs to be used to lookup any identifiers
     ; mentioned in the expression of the (fn..)? Other than the `argname`,
     ; any other "free variables" will need to remember any values
     ; they were bound to ... and this is the REALLY IMPORTANT PART ...
     ; ** at the time the FnV is constructed **
     ; or in other words
     ; ** in the definition environment of the (fn..) **.
     ; So we need to store the definition env in the FnV so we
     ; can refer to it later when we need it.
     (FnV env argname expr)]
    [(app fexpr vexpr) (let ([f (fnv (interp env fexpr))]
                             [argval (interp env vexpr)])
                         ; Now we augment the environment with a new binding for
                         ; the argname symbol to the argval and interpret the
                         ; function's body.
                         ;
                         ; Here, we need to extend not the interpretation environment,
                         ; but the **definition environment** of the function so that
                         ; any other identifiers available at the point of definition
                         ; are available when evaluating its body.
                         ;
                         ; The only change here is from `env` to `(FnV-denv f)`. 
                         (interp (extend (FnV-denv f) (FnV-argname f) argval)
                                 (FnV-expr f)))]
    [_ (error 'interp "Unknown expression ~a" expr)]))

; Boolean constants.
(: boolv (-> Boolean Val))
(define (boolv b)
  (if b btruev bfalsev))

(define btruev (interp empty-env btrue))
(define bfalsev (interp empty-env bfalse))

; Useful in circumstances where it is a runtime error for a value
; to be anything other than a GenV.
(: genv (-> (U Real Val) a:Gen))
(define (genv v)
  (cond
    [(GenV? v) (GenV-gen v)]
    [(RealV? v) (a:konst (RealV-r v))]
    [(real? v) (a:konst v)]
    [else (error 'genv "GenV expected. Got ~a" v)]))

; Useful when processing (app..) terms where the first expression is
; expected to evaluate to a FnV.
(: fnv (-> Val FnV))
(define (fnv v)
  (if (FnV? v)
      v
      (error 'fnv "FnV expected. Got ~a" v)))
   
(: realv (-> (U Real Val) Real))
(define (realv v)
  (cond
    [(real? v) v]
    [(RealV? v) (RealV-r v)]
    [else (error 'realv "RealV expected. Got ~a" v)]))


#|
Try some of the following sample expressions. Run each through the
interpreter and supply the resultant gen to a:write-wav-file like
this - `(a:write-wav-file "filename.wav" result-gen dur-secs gain 48000)`.
Ex: `(write-wav-file "sig5.wav" sig5 3.0 0.25 48000)`
|#

;
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


; QUESTION: Examine the definition of sig7 and sig8 below. What do you
; expect to be the result of rendering sig7/sig8? i.e. what "should be"
; the result? What actually happens? To answer this, consider
; expressing the same idea in plain Racket using the asynth module's
; exported procedures and then examine any differences between your
; expectation and the results of sig8. Use the following correspondences
; to help you.
;     (fn sym expr) ==> (λ (sym) expr)
;     (app fexpr vexpr) ==> (fexpr vexpr)
;     (id 'sym) ==> sym

; A simple use of functions that ought to work.
(define fsig1 (fn 'a (fn 'b
                         (stitch (id 'a) 0.5
                                 (stitch (id 'b) 0.5
                                         (stitch (id 'a) 0.5
                                                 (id 'b)))))))
(define sig7 (app (app fsig1 (oscil 300.0)) (oscil 450.0)))


(define fsig2 (fn 'a (stitch (id 'a) 0.5 (id 'b))))
(define sig8 (app (fn 'f
                      (app (fn 'b
                               (app (id 'f) (oscil 300.0)))
                           (oscil 450.0)))
                  fsig2))
                            
; The Y and θ fixed point combinators expressed in our language.
(define Y (fn 'f (app (fn 'g (app (id 'g) (id 'g)))
                      (fn 'w (app (id 'f)
                                  (fn 'x (app (app (id 'w)
                                                   (id 'w))
                                              (id 'x))))))))
(define θ (app (fn 'x (app (id 'x) (id 'x)))
               (fn 'g (fn 'f (app (id 'f)
                                  (fn 'x (app (app (app (id 'g) (id 'g))
                                                   (id 'f))
                                              (id 'x))))))))

(define fsig3 (fn 'a (oscil (bif (lt (id 'a) 1.0)
                                 300.0
                                 450.0))))
(define sig9 (app fsig3 0.5))
(define sig10 (app fsig3 1.5))
