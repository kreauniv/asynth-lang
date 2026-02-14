#lang typed/racket

(provide write-wav-file 
         Gen
         (struct-out step)
         konst clock phasor oscil noise midi2hz mix mod
         line expon decay stitch cut after
         d adsr fadein fadeout crossfade
         lpf bpf bpf0 hpf
         loop seq dynseq)

(require racket/match)

; A struct capturing the result of a sample generation step.
(struct step ([val : Real] [gen : Gen])
  #:transparent)
                           
; An "audio signal" is a sequence of samples. We model the process
; of producing this sequence of samples using a step function which
; when called with the time step, will produce the next sample value
; along with the next step function to compute further samples.
(define-type Gen (-> Real step))

(define *default-sampling-rate* 48000)

(: write-wav-file (-> String Gen Positive-Real Positive-Real Positive-Integer Void))
(define (write-wav-file filename
                        model
                        duration
                        gain
                        [sample-rate *default-sampling-rate*])
  (define dt (/ 1.0 sample-rate))
  (define num-samples (exact-round (* duration sample-rate)))
  (define num-channels 1)
  (define bytes-per-sample 4)
  (define bits-per-sample (* 8 bytes-per-sample))
  (define byte-rate (* sample-rate num-channels bytes-per-sample))
  (define block-align (* num-channels bytes-per-sample))
  (define data-size (* num-samples num-channels bytes-per-sample))
  (define file-size (+ 36 data-size))

  (call-with-output-file filename
    #:exists 'replace
    (lambda ([out : Output-Port])
      ;<write-RIFF-header>
      (write-bytes #"RIFF" out)
      (write-int32le file-size out)
      (write-bytes #"WAVE" out)

      ;<write-fmt-subchunk>
      (write-bytes #"fmt " out)
      (write-int32le 16 out)    ; subchunk size
      (write-int16le 3 out)     ; audio format (3 = IEEE float)
      (write-int16le num-channels out)
      (write-int32le sample-rate out)
      (write-int32le byte-rate out)
      (write-int16le block-align out)
      (write-int16le bits-per-sample out)

      ;<write-data-subchunk>
      (write-bytes #"data" out)
      (write-int32le data-size out)

      (let loop : Void ([i : Integer 0]
                        [bytes : Bytes (make-bytes 4)]
                        [s : Gen model])
        (let ([v (s dt)])
          (when (< i num-samples)
            (real->floating-point-bytes (* gain (step-val v))
                                        4 ; bytes per value
                                        #f ; little-endian
                                        bytes
                                        )
            (write-bytes bytes out)
            (loop (+ i 1) bytes (step-gen v))))))))

(: write-int16le (-> Nonnegative-Integer Output-Port Void))
(define (write-int16le n out)
  (write-byte (bitwise-and n #xFF) out)
  (write-byte (bitwise-and (arithmetic-shift n -8) #xFF) out))

(: write-int32le (-> Nonnegative-Integer Output-Port Void))
(define (write-int32le n out)
  (write-byte (bitwise-and n #xFF) out)
  (write-byte (bitwise-and (arithmetic-shift n -8) #xFF) out)
  (write-byte (bitwise-and (arithmetic-shift n -16) #xFF) out)
  (write-byte (bitwise-and (arithmetic-shift n -24) #xFF) out))



; The "konst" primitive (for "constant") simply always produces the same
; sample value every time the model is asked for one.
(: konst (-> Real Gen))
(define (konst v)
  (lambda (dt)
    (step v (konst v))))

(define-type ?Gen (U Real Gen))
(: ?konst (-> ?Gen Gen))
(define (?konst v)
  (if (real? v)
      (konst v)
      v))

; The "clock" simply accumulates the sample intervals to compute the "time".
; This is not technically an "audio" model as the clock is not intended to be
; heard, but it is nevertheless how time keeping needs to be done. We'll permit
; the clock to change its speed over time, and so make the "speed" of the clock
; also a model.

(: clock (-> Gen Real Gen))
(define (clock speed t)
  (lambda (dt)
    (let ([s (speed dt)])
      ; Step the time to the sig value by getting the current speed
      ; and scaling the given dt by the speed. So if speed produces
      ; 2.0, the clock will advance twice as fast.
      (step t (clock (step-gen s) (+ t (* (step-val s) dt)))))))

; Given a Gen that produces a stream of values and a function that
; maps a value to another, we can define a general operation of 
; mapping the function over the Gen.

(: mapgen (-> (-> Real Real) Gen Gen))
(define (mapgen fn s)
  (lambda (dt)
    (let ([v (s dt)])
      (step (fn (step-val v))
            (mapgen fn (step-gen v))))))

(: mapgen2 (-> (-> Real Real Real) Gen Gen Gen))
(define (mapgen2 fn s1 s2)
  (lambda (dt)
    (let ([v1 (s1 dt)]
          [v2 (s2 dt)])
      (step (fn (step-val v1) (step-val v2))
            (mapgen2 fn (step-gen v1) (step-gen v2))))))

; A "phasor" is a simpler version of the clock which goes periodically from 0
; to 1 over a duration determined by a given "frequency".

(: phasor (-> Gen Gen))
(define (phasor f)
  (mapgen (lambda (x) (- x (floor x)))
          (clock f 0.0)))

(: noise Gen)
(define noise
  (lambda (dt)
    (step (* 2.0 (- (random) 0.5)) noise)))

; An "oscil" is a sinusoidal oscillator. This can be easily derived from a
; phasor, so we make use of the phasor.

(: oscil (-> Gen Gen))
(define (oscil f)
  (mapgen (lambda (x) (sin (* 2 pi x)))
          (phasor f)))

; MIDI note numbers have a logarithmic relationship to frequency in Hz.
; middle octave A is MIDI note number 69 which is set at 440Hz for tuning purposes.
; And a octave is a frequency doubling (or halving) and an octave is 12 MIDI notes
; higher (or lower) from wherever you are.
(: midi2hz (-> Gen Gen))
(define (midi2hz notenum)
  (mapgen (lambda (n) (* 440.0 (exp (* (log 2) (/ (- n 69) 12)))))
          notenum))

; The simplest operation that combines two audio Gens is to "mix" them. This
; is simple addition of the sample values produced by the processes. However,
; you do need to be aware of whether the step can exceed the [-1,1] range.

(: mix (-> Gen Gen Gen))
(define (mix a b)
  (mapgen2 + a b))

; "Modulation" refers to controlling the amplitude of one form with another
; form. This is often just the multiplication of two Gens. So we'll use that
; simple definition.

(: mod (-> Gen Gen Gen))
(define (mod a b)
  (mapgen2 * a b))

; Controlling Gens often needs linear ramps as a primitive. So we'll make
; one. When given two values and a duration, a "line" will start at the
; starting value and change linearly to the ending value.

(: line (-> Real Real Real Gen))
(define (line a dur b)
  (stitch (mapgen (λ (t) (+ a (* t (- b a))))
                  (clock (konst (/ 1.0 dur)) 0.0))
          dur
          (konst b)))

; expon is like line except it make an exponential curve instead of a linear one
; between the two end values a and b.
(: expon (-> Real Real Real Gen))
(define (expon a dur b)
  (let ([la (log a)]
        [lb (log b)])
    (stitch (mapgen (λ (t) (real-part (exp (+ la (* t (- lb la))))))
                    (clock (konst (/ 1.0 dur)) 0.0))
            dur
            (konst b))))

; An exponential "decay" starts at some value and goes to 0 exponentially at some
; rate.
(: decay (-> Real Real Gen))
(define (decay halflife v)
  (if (< (abs v) 1/32768)
      (konst 0.0)
      (lambda (dt)
        (step v (decay halflife (* v (exp (- (* (log 2) (/ dt halflife))))))))))

; It is useful to be able to sequence two models in time. In this case, we want to
; stop processing the preceding Gen once its stipulated duration completes, and then
; switch to processing the second Gen.
(: stitch (-> Gen Real Gen Gen))
(define (stitch a dur b)
  (if (<= dur 0.0)
      ; If no duration left, then it's all b afterwards.
      ; Notice that stitch does not get used recursively
      ; in this branch, which means it's all really b from
      ; this point onwards.
      b
      (lambda (dt)
        ; Keep reducing the duration as we run a.
        (match-let ([(step av ag) (a dt)])
          (step av (stitch ag (- dur dt) b))))))

; Single time step delay.
(: d (-> Gen Gen))
(define (d g)
  (define (d* [g : Gen] [v : Real]) : Gen
    (lambda (dt)
      (match-let ([(step gv gg) (g dt)])
        (step v (d* gg gv)))))
  (d* g 0.0))

; Recursively defined n-step delay.
(: dn (-> Nonnegative-Integer Gen Gen))
(define (dn n g)
  (if (= n 0)
      g
      (d (dn (- n 1) g))))          
        
; We can now use the core primitives we've defined above to express some common
; constructs that are useful.

; A cut can be expressed in terms of stitch.
(: cut (-> Real Gen Gen))
(define (cut dur g)
  (stitch g dur (konst 0.0)))

; Likewise `after` can be expressed in terms of stitch too.
(: after (-> Real Gen Gen))
(define (after dur g)
  (stitch (konst 0.0) dur g))

; The "ADSR" curve refers to a four segment curve with an "attack" period over
; which the value rises from 0.0 to some peak, followed by a short "decay"
; period when the value reduces to a "sustain level", which then lasts for a
; "sustain duration" before getting "released" back to 0.0 over the release
; duration. We can therefore express ADSR as a sequence of line segments.

(: adsr (-> Real Real Real Real Real Real Gen))
(define (adsr alevel adur decay slevel sdur release)
  (stitch (line 0.0 adur alevel)
          adur
          (stitch (line alevel decay slevel)
                  decay
                  (stitch (line slevel sdur slevel)
                          sdur
                          (line slevel release 0.0)))))

; A "fadein" modifies an audio clip by ramping up its volume from 0.0 to 1.0
; over a specified duration. Similarly, a "fadeout" ramps the volume from 1.0
; to 0.0 at the end. This enables smooth entry and exit of an audio clip.

(: fadein (-> Real Gen))
(define (fadein xdur)
  (line 0.0 xdur 1.0))

(: fadeout (-> Real Real Gen))
(define (fadeout xdur totaldur)
  (stitch (konst 1.0)
          (- totaldur xdur)
          (line 1.0 xdur 0.0)))

; A "crossfade" refers to two audio snippets that are partially overlapped to
; "join" them smoothly. Over this overlap period, the preceding audio snippet
; "fades out" while the succeeding audio snippet "fades in". This is a more
; practical form of sequencing audio snippets. We can use line, stitch, mix and
; mod to express this combination approach.

(: crossfade (-> Real Gen Real Gen Gen))
(define (crossfade xdur a adur b)
  (mix (cut adur (mod (fadeout adur xdur) a))
       (after (- adur xdur)
              (mod (fadein xdur) b))))


; So now we have a bunch of audio operators and methods to combine them so we can
; construct Gens and render them to a file for playback.

; Below are some common "biquad filters" that are useful for synthesis.
; I've included them here just to make the point that we can continue
; modelling more operators using the same approach. Understanding the
; math here requires getting into digital signal processing and that's
; not a requirement. Just understand that `lpf` cuts of higher frequencies,
; `bpf` selects frequencies around a given value and `hpf` cuts off lower
; frequencies. `lpf` is useful to "smooth" sounds, "hpf" is useful to get
; rid of offsets and "bpf" is useful as model of resonance. This isn't
; an exhaustive list.

(: biquad (-> Real Real Real Real Real Real Real Real Real Real Real Real))
(define (biquad b0 b1 b2 a0 a1 a2 xn xn1 xn2 yn1 yn2)
  (/ (+ (* b0 xn) (* b1 xn1) (* b2 xn2)
        (* -1 a1 yn1) (* -1 a2 yn2))
     a0))

(: lpf (-> Real Real Real Gen Gen))
(define (lpf freq q sr g)
  (let* ([dt (/ 1.0 sr)]
         [w0 (* 2 pi freq dt)]
         [sw0 (sin w0)]
         [cw0 (cos w0)]
         [alpha (/ sw0 (* 2 q))]
         [b1 (- 1.0 cw0)]
         [b0 (/ b1 2.0)]
         [b2 (/ b1 2.0)]
         [a0 (+ 1.0 alpha)]
         [a1 (* -2.0 cw0)]
         [a2 (- 1.0 alpha)])
    (: lpf* (-> Gen Real Real Real Real Gen))
    (define (lpf* x xn1 xn2 yn1 yn2)
      (lambda (dt)
        (match-let ([(step xn xg) (x dt)])
          (let ([yn (biquad b0 b1 b2 a0 a1 a2 xn xn1 xn2 yn1 yn2)])
            (step yn (lpf* xg xn xn1 yn yn1))))))
    (lpf* g 0.0 0.0 0.0 0.0)))

(: bpf (-> Real Real Real Gen Gen))
(define (bpf freq q sr g)
  (let* ([dt (/ 1.0 sr)]
         [w0 (* 2 pi freq dt)]
         [sw0 (sin w0)]
         [cw0 (cos w0)]
         [alpha (/ sw0 (* 2 q))]
         [b0 sw0]
         [b1 0.0]
         [b2 (- b0)]
         [a0 (+ 1.0 alpha)]
         [a1 (* -2.0 cw0)]
         [a2 (- 1.0 alpha)])
    (: bpf* (-> Gen Real Real Real Real Gen))
    (define (bpf* x xn1 xn2 yn1 yn2)
      (lambda (dt)
        (match-let ([(step xn xg) (x dt)])
          (let ([yn (biquad b0 b1 b2 a0 a1 a2 xn xn1 xn2 yn1 yn2)])
            (step yn (bpf* xg xn xn1 yn yn1))))))
    (bpf* g 0.0 0.0 0.0 0.0)))

(: bpf0 (-> Real Real Real Gen Gen))
(define (bpf0 freq q sr g)
  (let* ([dt (/ 1.0 sr)]
         [w0 (* 2 pi freq dt)]
         [sw0 (sin w0)]
         [cw0 (cos w0)]
         [alpha (/ sw0 (* 2 q))]
         [b0 alpha]
         [b1 0.0]
         [b2 (- b0)]
         [a0 (+ 1.0 alpha)]
         [a1 (* -2.0 cw0)]
         [a2 (- 1.0 alpha)])
    (: bpf0* (-> Gen Real Real Real Real Gen))
    (define (bpf0* x xn1 xn2 yn1 yn2)
      (lambda (dt)
        (match-let ([(step xn xg) (x dt)])
          (let ([yn (biquad b0 b1 b2 a0 a1 a2 xn xn1 xn2 yn1 yn2)])
            (step yn (bpf0* xg xn xn1 yn yn1))))))
    (bpf0* g 0.0 0.0 0.0 0.0)))

(: hpf (-> Real Real Real Gen Gen))
(define (hpf freq q sr g)
  (let* ([dt (/ 1.0 sr)]
         [w0 (* 2 pi freq dt)]
         [sw0 (sin w0)]
         [cw0 (cos w0)]
         [alpha (/ sw0 (* 2 q))]
         [b0 (/ (+ 1.0 cw0) 2.0)]
         [b1 (* -2.0 b0)]
         [b2 b0]
         [a0 (+ 1.0 alpha)]
         [a1 (* -2.0 cw0)]
         [a2 (- 1.0 alpha)])
    (: hpf* (-> Gen Real Real Real Real Gen))
    (define (hpf* x xn1 xn2 yn1 yn2)
      (lambda (dt)
        (match-let ([(step xn xg) (x dt)])
          (let ([yn (biquad b0 b1 b2 a0 a1 a2 xn xn1 xn2 yn1 yn2)])
            (step yn (hpf* xg xn xn1 yn yn1))))))
    (hpf* g 0.0 0.0 0.0 0.0)))

(: dynseq (-> Nonnegative-Integer
              (-> Nonnegative-Integer (U #f (List Gen Real)))
              Gen))
(define (dynseq i fn)
  (let ([g (fn i)])
    (if g
        (stitch (first g) (second g) (dynseq (+ i 1) fn))
        (konst 0.0))))

(: loop (-> Nonnegative-Integer Real Gen Gen))
(define (loop n dur g)
  (dynseq 0 (λ (i) (and (< i n) (list g dur)))))

(: seq (-> Nonnegative-Integer Nonnegative-Integer
           (-> Nonnegative-Integer Nonnegative-Integer Gen)
           Gen))
(define (seq N dur fn)
  (dynseq 0 (λ (i) (and (< i N) (list (fn i N) dur)))))


