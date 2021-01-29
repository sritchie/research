#!r6rs

(import
 (rnrs)
 (rnrs records syntactic))

(define-record-type dual-number (fields epsilon primal tangent))

(define *eta-expansion?* #f)

(define *tag-substitution?* #t)

(define *section9?* #f)

;; I (Sam) added this new conditional to toggle the "third fix" behavior.
(define *fix-three?* #f)

;; This controls whether or not to conservatively do tag replacement, vs
;; everywhere.
(define *save-work?* #f)

;;; One of equation-24d, equation-38, or equation-41
(define *function-substitution* 'equation-24d)

(define *epsilon* 0)

(define (generate-epsilon)
  (set! *epsilon* (+ *epsilon* 1))
  *epsilon*)

(define (create-dual-number epsilon primal tangent)
 ;; This enforces the invariant that no epsilon is nested inside the same
 ;; epsilon. This situation could have arisen with Equation (24b) in subst and
 ;; was the source of the bug that Sam Ritchie uncovered. The invariant is
 ;; enforced by making sure that only smaller epsilons are nested inside larger
 ;; ones.
 (if (and (or (not (dual-number? primal))
	      (> epsilon (dual-number-epsilon primal)))
	  (or (not (dual-number? tangent))
	      (> epsilon (dual-number-epsilon tangent))))
     (make-dual-number epsilon primal tangent)
     (d+ primal (d* tangent (make-dual-number epsilon 0 1)))))

(define (subst epsilon1 epsilon2 x)
  (cond ((real? x) x)			;Equation (24a)
        ((dual-number? x)
	       (if (= (dual-number-epsilon x) epsilon2)
	           ;; Equation (24b)
	           (create-dual-number
	            epsilon1 (dual-number-primal x) (dual-number-tangent x))
	           ;; Equation (24c)
	           (create-dual-number
	            (dual-number-epsilon x)
	            (subst epsilon1 epsilon2 (dual-number-primal x))
	            (subst epsilon1 epsilon2 (dual-number-tangent x)))))
        ((procedure? x)
         (lambda (y)
	         (case *function-substitution*
             ((equation-24d)
	            ;; Equation (24d)
	            (let ((epsilon3 (generate-epsilon)))
	              (subst epsilon2 epsilon3
		                   (subst epsilon1 epsilon2 (x (subst epsilon3 epsilon2 y))))))
	           ((equation-38)
	            ;; Equation (38)
	            (subst epsilon2 epsilon1 (x (subst epsilon1 epsilon2 y))))
	           ;; Equation (41)
	           ((equation-41) (x y))
	           (else (error "A")))))
        (else (error "B"))))

(define *active-epsilons* '())

(define (epsilon-active? epsilon)
  (memq epsilon *active-epsilons*))

(define (with-active-epsilon epsilon f arg)
  (let ((old *active-epsilons*))
    (set! *active-epsilons* (cons epsilon *active-epsilons*))
    (let ((result (f arg)))
      (set! *active-epsilons* old)
      result)))

(define (prim epsilon x)
  (cond ((real? x) x)
        ((dual-number? x)
	       (if (= (dual-number-epsilon x) epsilon)
	           (dual-number-primal x)
	           (create-dual-number (dual-number-epsilon x)
				                         (prim epsilon (dual-number-primal x))
				                         (prim epsilon (dual-number-tangent x)))))
        ((procedure? x)
	       (cond (*tag-substitution?*
	              (lambda (y)
	                (let ((epsilon2 (generate-epsilon)))
	                  (subst epsilon
		                       epsilon2
		                       (prim epsilon (x (subst epsilon2 epsilon y)))))))

               (*save-work?*
                (lambda (y)
	                (if (epsilon-active? epsilon)
                      (let ((epsilon2 (generate-epsilon)))
	                      (subst epsilon
		                           epsilon2
		                           (prim epsilon
                                     (with-active-epsilon
                                      x (subst epsilon2 epsilon y)))))
                      (prim epsilon (with-active-epsilon x y)))))

               (else (lambda (y) (prim epsilon (x y))))))
        (else (error "C"))))

(define (tg epsilon x)
  (cond ((real? x) 0)			;Equation (8a)
        ((dual-number? x)
	       (if (= (dual-number-epsilon x) epsilon)
	           ;; Equation (8b)
	           (dual-number-tangent x)
	           ;; Equation (8c)
	           (create-dual-number (dual-number-epsilon x)
				                         (tg epsilon (dual-number-primal x))
				                         (tg epsilon (dual-number-tangent x)))))
        ((procedure? x)
	       (if *tag-substitution?*
	           ;; Equation (23)
	           (lambda (y)
	             (let ((epsilon2 (generate-epsilon)))
	               (subst epsilon
		                    epsilon2
		                    (tg epsilon (x (subst epsilon2 epsilon y))))))
	           ;; Equation (8e)
	           (lambda (y) (tg epsilon (x y)))))
        (else (error "D"))))

;; This function is ~similar to tg, except that it's meant to be called only at the return of "d",
;; when you're actually attempting to extract the tangent for good and not bundle it up again.
(define (extract-fix-three epsilon x)
  (cond ((dual-number? x)
         ;; If tg is attempting to extract an epsilon that a higher level is
         ;; waiting for, (tg epsilon x) acts as (identity x).
         (if (epsilon-active? epsilon)
             x
             (tg epsilon x)))

        ;; The returned procedure calls (x y) with epsilon marked as active.
        ;; Inside that (x y) call, the (epsilon-active? x) branch in the (dual-number? x)
        ;; case above will return true.
        ((procedure? x)
         (lambda (y)
           (extract-fix-three epsilon (with-active-epsilon epsilon x y))))

        ;; All other cases are identical to a call to tg.
        (else (tg epsilon x))))

(define (bun epsilon x x-prime)
  (cond ((and (or (real? x) (dual-number? x))
	            (or (real? x-prime) (dual-number? x-prime)))
	       ;; Equation (30a)
	       (create-dual-number epsilon x x-prime))
        ((and (procedure? x) (procedure? x-prime))
	       (if *tag-substitution?*
	           ;; Equation (31)
             (lambda (y)
	             (let ((epsilon2 (generate-epsilon)))
	               (subst epsilon epsilon2
		                    (bun epsilon
			                       (x (subst epsilon2 epsilon y))
			                       (x-prime (subst epsilon2 epsilon y))))))
	           ;; Equation (30b)
	           (lambda (y) (bun epsilon (x y) (x-prime y)))))
        (else (error "E"))))

(define (lift-real->real f df/dx)
 (letrec ((self (lambda (x)
		 (if (dual-number? x)
		     (let ((epsilon (dual-number-epsilon x)))
		      (bun epsilon
			   (self (prim epsilon x))
			   (d* (df/dx (prim epsilon x)) (tg epsilon x))))
		     (f x)))))
  self))

(define (lift-real*real->real f df/dx1 df/dx2)
 (letrec ((self (lambda (x1 x2)
		 (if (or (dual-number? x1) (dual-number? x2))
		     (let ((epsilon (if (dual-number? x1)
					(dual-number-epsilon x1)
					(dual-number-epsilon x2))))
		      (bun epsilon
			   (self (prim epsilon x1) (prim epsilon x2))
			   (d+ (d* (df/dx1 (prim epsilon x1) (prim epsilon x2))
				   (tg epsilon x1))
			       (d* (df/dx2 (prim epsilon x1) (prim epsilon x2))
				   (tg epsilon x2)))))
		     (f x1 x2)))))
  self))

;;; Equation (5a)
(define d+ (lift-real*real->real + (lambda (x1 x2) 1) (lambda (x1 x2) 1)))

;;; Equation (5b)
(define d* (lift-real*real->real * (lambda (x1 x2) x2) (lambda (x1 x2) x1)))

(define dexp (lift-real->real exp (lambda (x) (dexp x))))

(define (j* f)
  (lambda (x)
    ;; I am not sure if this is well founded... but I had to make this change to
    ;; get the nested j* examples to work. I also had to remove the x-prime
    ;; argument from the eta-expansion, procedure branch below.
    (let ((x-prime (if (procedure? x) (j* x) 1)))
      (if *eta-expansion?*
          (if (procedure? (f x))
	            ;; Equation (32a)
	            (lambda (y) ((j* (lambda (x) ((f x) y))) x))
	            ;; Equation (32b)
	            (let ((epsilon (generate-epsilon)))
	              (tg epsilon (f (bun epsilon x x-prime)))))
          ;; Equation (33)
          (let ((epsilon (generate-epsilon)))
            (tg epsilon (f (bun epsilon x x-prime))))))))

(define (d f)
  (lambda (x)
    (cond (*section9?* ((j* f) x))	;Equation (34)
	        (*eta-expansion?*
	         (if (procedure? (f x))
	             ;; Equation (18a)
	             (lambda (y) ((d (lambda (x) ((f x) y))) x))
	             ;; Equation (18b)
	             (let ((epsilon (generate-epsilon)))
	               (tg epsilon (f (create-dual-number epsilon x 1))))))

          ;; This branch enables the new "fix" to Alexey's Amazing Bug from Sam, GJS
          (*fix-three?*
           (let ((epsilon (generate-epsilon)))
	           (extract-fix-three epsilon (f (create-dual-number epsilon x 1)))))

          ;; Equation (8d)
	        (else (let ((epsilon (generate-epsilon)))
	                (tg epsilon (f (create-dual-number epsilon x 1))))))))

;; Jeff, I:
;;
;; - turned the comments below into write statements
;;
;; - added a new block of Sam's Second Example with *fix-three?* enabled
;;
;; - added a further block comparing *fix-three?* to *tag-substitution?*, on
;;   Alexey's Amazing Bug - it turns out that behavior we've been studying shows
;;   up there too!

(write "Sam's Second Example")
(newline)

(define (f x)
 (lambda (cont)
  ((cont (lambda (y) (d* x (d* x y))))
   (lambda (g) (g x)))))

(write "case 1, (f2 f1) inside continuation: ")
(write (((d f) 2)
	(lambda (f1)
	 (lambda (f2)
	  (f2 f1)))))
(newline)

(define (kons a) (lambda (d) (lambda (m) ((m a) d))))

(define (kar p) (p (lambda (a) (lambda (d) a))))

(define (kdr p) (p (lambda (a) (lambda (d) d))))

(write "case 2, just function evaluation, no derivative: ")
(write (let ((pair ((f 2)
		    (lambda (f1)
		     (lambda (f2)
		      ((kons f1) f2))))))
	(let ((f1 (kar pair))
	      (f2 (kdr pair)))
	 (f2 f1))))
(newline)

(write "case 2, use kons to split the original tangent space into two tangent spaces: ")
(write (let ((pair (((d f) 2)
		    (lambda (f1)
		     (lambda (f2)
		      ((kons f1) f2))))))
	(let ((f1 (kar pair))
	      (f2 (kdr pair)))
	 (f2 f1))))
(newline)

(set! *tag-substitution?* #f)
(set! *fix-three?* #t)

(write "case 2 using the NEW fix - tangent spaces persist through a functional return value: ")
(write (let ((pair (((d f) 2)
		    (lambda (f1)
		     (lambda (f2)
		      ((kons f1) f2))))))
	(let ((f1 (kar pair))
	      (f2 (kdr pair)))
	 (f2 f1))))
(newline)

(write "Go back to tag substitution.")
(set! *tag-substitution?* #t)
(set! *fix-three?* #f)
(newline)

(write "Alexey's Amazing Bug shows the same split in behavior. First, use the familiar form of the example.")
(newline)

(define (arg-shift offset)
  (lambda (g)
    (lambda (a) (g (d+ a offset)))))


(let ((f-hat ((d arg-shift) 3)))

  (write "((f-hat dexp) 5)) returns (exp 8): ")
  (write ((f-hat dexp) 5))
  (newline)

  (write "((f-hat (f-hat dexp)) 5)) returns (exp 11): ")
  (write ((f-hat (f-hat dexp)) 5))
  (newline))

(write "Define a version arg-shift-cont that takes a continuation:")
(newline)

(define (arg-shift-cont offset)
  (lambda (cont)
    (cont (lambda (g)
            (lambda (a) (g (d+ a offset)))))))


(write "If you use cont==identity, ((f-hat (f-hat dexp)) 5)) returns (exp 11), because each f-hat has its own tangent space:")
(let ((f-hat (((d arg-shift-cont) 3) (lambda (x) x))))
  (write ((f-hat (f-hat dexp)) 5))
  (newline))

(write "If you evaluate  ((f-hat (f-hat dexp)) 5)) inside a continuation you get (* 2 (exp 11)), since the f-hat passed to the continuation space has a SINGLE tangent space:")
(let ((result (((d arg-shift-cont) 3)
               (lambda (f-hat)
                 ((f-hat (f-hat dexp)) 5)))))
  (write result)
  (newline))

(write "Now go back to *fix-three?*. Both cases return (* 2 (exp 11)), because fix three doesn't split tangent spaces.")
(newline)
(set! *tag-substitution?* #f)
(set! *fix-three?* #t)

(write "fix three, cont==identity: ")
(let ((f-hat (((d arg-shift-cont) 3) (lambda (x) x))))
  (write ((f-hat (f-hat dexp)) 5))
  (newline))

(write "fix three, evaluate inside cont: ")
(let ((result (((d arg-shift-cont) 3)
               (lambda (f-hat)
                 ((f-hat (f-hat dexp)) 5)))))
  (write result)
  (newline))

(write "The mental model offered by 'fix three' is that the act of passing an argument to (D f) creates a tangent space.")
(newline)
(write "To get the 'old' behavior back, pass input 3 to the (d arg-shift) twice:")
(let* ((df (d arg-shift))
       (f-hat1 (df 3))
       (f-hat2 (df 3)))
  (write ((f-hat1 (f-hat2 dexp)) 5)))
(newline)

(write "This is basically equation 15 in Manzyuk.")
(newline)
(newline)

;; reset to tag substitution.
(set! *tag-substitution?* #t)
(set! *fix-three?* #f)

(write "j* Investigation")
(newline)

;; This is just like arg-shift-cont, but it takes the continuation argument
;; FIRST, and returns a function that expects the offset. This is the format we
;; need to test j*.
(define (arg-shift-cont-flipped cont)
  (lambda (offset)
    (cont
     (lambda (g)
       (lambda (a) (g (d+ a offset)))))))

;; This is the continuation we've been using in the examples above.
(define (cont f-hat)
  ((f-hat (f-hat dexp)) 5))

;; My understanding of the semantics of passing a function g to (j* f) [ie, ((j*
;; f) g)] is: if g takes some number x, the function will internally produce its
;; result (g x) in the form of a dual of [(g x), ((d g) x)].
;;
;; ie whenever g is called it tags its input, which then bubbles up through the
;; whole function call.
;;
;; The following example is interesting; the answers are the same, but
;; superficially. In the first, offset == 3 is augmented:
(write "j* arg-shift with function and int args, tag sub:")
(newline)
(write (((j* arg-shift-cont) 3) cont))
(newline)

;; In the second, the interior =a= argument is augmented, which is actually =5=.
(write (((j* arg-shift-cont-flipped) cont) 3))
(newline)

;; Same answer with eta expansion.
(write "with eta expansion:")
(set! *tag-substitution?* #f)
(set! *eta-expansion?* #t)
(newline)
(write (((j* arg-shift-cont) 3) cont))
(newline)
(write (((j* arg-shift-cont-flipped) cont) 3))
(newline)

;; I don't have a good mental model for the next example. Here, cont2 takes a
;; function like arg-shift and makes two separate calls with inputs 1 and 2.
;;
;; Then it does what the other continuation does.
(define (cont2 d-shift)
  (let ((f-hat1 (d-shift 1))
        (f-hat2 (d-shift 2)))
    ((f-hat1 (f-hat2 dexp)) 2)))

;; With both eta expansion and tag substitution, ((j* cont2) arg-shift) results
;; in BOTH `f-hat' instances getting tagged with the same tag... so the final
;; result is (* 2 (exp 5)).
;;
;; BUT if I call (cont2 (j* arg-shift)) == (cont2 (d arg-shift)), then the
;; careful tag replacement machinery gives SEPARATE tags to each call and
;; returns (exp 5).
;;
;; Which is right? Should separate calls inside cont2 get tagged with the SAME
;; tag, and confuse? Weird that you could have two separate inputs to d-shift
;; get lifted into the same tangent space.

(write "j* example with tag sub:")
(set! *tag-substitution?* #t)
(set! *eta-expansion?* #f)
(newline)
(write (cont2 (j* arg-shift)))
(newline)
(write ((j* cont2) arg-shift))
(newline)

;; Here are the same examples, showing that the output matches with eta
;; expansion.
(write "j* arg-shift with function and int args, eta expansion:")
(set! *tag-substitution?* #t)
(set! *eta-expansion?* #f)
(newline)
(write (cont2 (j* arg-shift)))
(newline)
(write ((j* cont2) arg-shift))
(newline)
