
(encapsulate
 ()
 (local
  (include-book "arithmetic-5/top" :dir :system))
 (local
  (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
			HIST PSPV))))

 (local
  (defthm app-nil-preserves-bv
      (implies (is-bv x)
               (is-bv (app x (list nil))))))
 (local
  (defthm app-t-preserves-bv
      (implies (is-bv x)
               (is-bv (app x (list t))))))
 (local
  (defthm len-app-nil
      (implies  (is-bv x)
		(equal (len (app x (list nil)))
                       (+ (len x) 1) ))))
 (local
  (defthm len-app-t
      (implies  (is-bv x)
		(equal (len (app x (list t)))
                       (+ (len x) 1) ))))
 (local
  (defthm bv-dec-app-nil
      (implies (is-bv x)
               (equal (unsigned-bv-dec (app x (list nil)))
                      (* 2 (unsigned-bv-dec x))))))
 (local
  (defthm bv-dec-app-t
      (implies (is-bv x)
               (equal (unsigned-bv-dec (app x (list t)))
                      (+ 1 (* 2 (unsigned-bv-dec x)))))))
 (local
  (defthm to-bv-is-bv
      (implies (natp n)
	       (is-bv (to-bv n)))))

 (local
  (defthm zero-vector-len-lemma
      (implies (natp n)
               (equal (len (zero-vector n)) n))))
 (local
  (defthm zero-vector-is-bv
      ( implies (and (natp n)(not (zp n)))
	(is-bv (zero-vector n)))))
 (local
  (defthm zero-vector-non-zero-len-if-n-nonzero
      (implies (and (natp n)(not (zp n)))
               (not (zp (len (zero-vector n)))))))
 (local
  (defthm is-zero-vector-implies-decimal-0
      (implies (is-zero-vector x)
               (equal (unsigned-bv-dec x) 0))))
 (local
  (defthm is-zero-vector-not-implies-decimal>0
      (implies (and (is-bv x)(not (is-zero-vector x)))
               (> (unsigned-bv-dec x) 0))))
 (local
  (defthm is-zero-vector-not-implies-not-decimal-zero
      (implies (and (not (is-zero-vector x)) (is-bv x) )
               (not (equal (unsigned-bv-dec x) 0)))))
 (local
  (defthm zero-vector-is-zero-vector
      (implies (and (natp n)(not(zp n)))
	       (is-zero-vector (zero-vector n)))))
 (local
  (defthm app-nil-preserves-is-zero-vector
      (implies (and (is-bv x)(is-zero-vector x))
	       (is-zero-vector (app x (list nil))))))
 (local
  (defthm app-nil-preserves-not-is-zero-vector
      (implies (and (is-bv x)(not (is-zero-vector x)))
	       (not (is-zero-vector (app x (list nil)))))))
 (local
  (defthm app-t-preserves-not-is-zero-vector
      (implies (and (is-bv x)(not (is-zero-vector x)))
	       (not (is-zero-vector (app x (list t)))))))
 (local
  (defthm dec-to-bv-equal-bv-to-dec
      (implies (and (natp n))
               (equal (unsigned-bv-dec (to-bv n)) n))))
 (local
  (defthm to-bv-non-zero-is-not-zero-vector
      (implies (and (natp n)(not (zp n)))
	       (not (is-zero-vector (to-bv n))))))
 (local
  (defthm is-bv-no-zero-len
      (implies (is-bv x)
               (> (len x) 0))))
 (local
  (defthm is-bv-no-zero-lens
      (implies (is-bv x)
               (not (equal (len x) 0)))))
  (local
  (defthm leading-1-lemma
      (equal (leading-1 x (+ p 1)) 
	     (+ (leading-1 x p) 1))))
 (local
  (defthm leading-1-lemma2
      (equal (leading-1 x 2) 
	     (+ (leading-1 x 1) 1))))
 (local
  (in-theory (disable leading-1-lemma)))

 (local
  (defthm leading-1-returns-integerp
      (implies (and (is-bv x)(integerp j))
               (integerp (leading-1 x j)))
    :rule-classes :type-prescription))
 (local
  (defthm leading-1-nth-lemma
      (implies (and (is-bv x)(<= (leading-1 x 1) (len x) ))
               (equal (nth (+ (leading-1 x 1) -1 ) x) t))))

 (local
  (defthm leading-1-returns-greater-than-argument
      (implies (and (is-bv x)(integerp j))
               (>= (leading-1 x j) j))
    :rule-classes :linear))

 (local
  (defthm leading-1-1-for-non-zero-vector-returns-less-than-len
      (implies (and (is-bv x)(not (is-zero-vector x)))
               (<= (leading-1 x 1) (len x) ))))

 (local
  (defthm is-bv-implies-consp
      (implies (is-bv x)
	       (consp x))))

 (local
  (defthm leading-1-all-takess-before-is-zero-vector
      (implies (and (is-bv x)(not (zp j))(< j (leading-1 x 1) ) )
               (is-zero-vector  (takes j x )))))

 (local
  (defthm leading-1-all-takess-before-is-zero-in-decimal
      (implies (and (is-bv x)(< n (leading-1 x 1)))
               (equal (unsigned-bv-dec (takes n x)) 0))))

 (local
  (defthm leadin-1-greater-than-len-implies-zero-vector
      (implies (and (is-bv x)(> (leading-1 x 1) (len x)))
	       (is-zero-vector x))))

 (local
  (defthm is-zero-vector-implies-leading-greater-than-len
      (implies (and (is-bv x) (is-zero-vector x))
	       (> (leading-1 x 1) (len x)))))

 (local
  (defthm leading-1-another-lemma
      (implies (and (is-bv x)(not (is-zero-vector x))(not (equal (leading-1 x 1) (len x))))
	       (< (leading-1 x 1) (len x)))))
;;;

 (local
  (defthm unsinged-bv-dec-retuns-intp
      (implies (is-bv x)
               (and (>= (unsigned-bv-dec x) 0)(integerp (unsigned-bv-dec x))))
    :rule-classes :type-prescription))

 (local
  (defthm unsinged-bv-dec-retuns-intpx
      (implies (is-bv x)
               (and (>= (unsigned-bv-dec x) 0)(integerp (unsigned-bv-dec x))))))

 ;;

 (local
  (defthm take-bv
      (implies (and (is-bv x)(natp j)(not (zp j))(<= j (len x)))
	       (is-bv (takes j x)))))

 (local
  (defthm take-consp
      (implies (and (is-bv x)(natp j)(not (zp j))(<= j (len x)))
	       (consp (takes j x)))))

 (local
  (defthm takes-len-equal
      (implies (and (is-bv x)(natp n)(< n (+ 1 (len x))))
               (equal (len (takes  n x)) n))))

 (local
  (defthm discards-len-equal
      (implies (and (is-bv x)(natp n)(< n (+ 1 (len x))))
               (equal (len (discard  n x)) (- (len x) n)))))

 (local
  (defthm discard-returns-bv
      (implies (and (is-bv x)(< n (len x))(natp n))
               (is-bv (discard n x )))))

 (local
  (defthm discard-returns-consp
      (implies (and (is-bv x)(natp n)(< n (len x)))
               (consp (discard n x )))))

 (local
  (defthm bv-frac-discard-lemma
      (implies (and (is-bv x))
	       (equal (bv-frac (discard (len x) x) 1)
		      0))))
 ;;

 (local
  (defthm takes-is-zero-vector
      (implies (and (is-bv x)(natp j)(not (zp j))(is-zero-vector x)(<= j (len x)))
	       (is-zero-vector (takes j x)))))

 (local
  (defthm  takes-is-zero-vector2
      (implies (and (is-bv x)(natp i)(not (zp i))(natp j)
		    (< i j)(is-zero-vector (takes j x))(<= j (len x)))
               (is-zero-vector (takes i x)))))

 (local
  (defthm is-zero-bv-dec-takes
      (implies (and (is-bv x)(is-zero-vector x)(natp j)(<= j (len x)))
	       (equal (unsigned-bv-dec (takes j x)) 0))))

 (local
  (defthm is-zero-bv-dec-discard
      (implies (and (is-bv x)(is-zero-vector x)(natp j)(<= j (len x)))
	       (equal (unsigned-bv-dec (discard j x)) 0))))

 (local
  (defthm is-zero-bv-frac-equal-0
      (implies (and (is-bv x)(is-zero-vector x)(integerp j))
	       (equal (bv-frac x j) 0))))

 (local
  (defthm is-zero-bv-frac-discard
      (implies (and (is-bv x)(is-zero-vector x)(integerp i)(not (zp j))(natp j)(<= j (len x)))
	       (equal (bv-frac (discard j x) i) 0))))

 (local
  (defthm is-zero-bv-frac-takes
      (implies (and (is-bv x)(is-zero-vector x)(natp j)(integerp i)(<= j (len x)))
	       (equal (bv-frac (takes j x) i) 0))))

 (local
  (defthm bv-frac-lemma-eqv
      (implies (and (is-bv x)(integerp j))
               (equal (bv-frac x (+ j 1))
                      (* 1/2 (bv-frac x j))))))
 (local
  (IN-THEORY (DISABLE BV-FRAC-LEMMA-EQV)))
 ;;
 ;;

 (local
  (defthm zero-vector-is-zero-vector
      (implies (and (natp n)(not(zp n)))
	       (is-zero-vector (zero-vector n)))))

 (local
  (defthm zero-vector-len-lemma
      (implies (natp n)
               (equal (len (zero-vector n)) n))))

 (local
  (defthm zero-vector-is-bv
      ( implies (and (natp n)(not (zp n)))
	(is-bv (zero-vector n)))))

 (local
  (defthm zero-vector-non-zero-len-if-n-nonzero
      (implies (and (natp n)(not (zp n)))
               (not (zp (len (zero-vector n)))))))

 (local
  (defthm bv-dec-of-zero-vector-0
      (equal (unsigned-bv-dec (zero-vector n)) 0)))
 ;;

 (local
  (defthm leading-1-returns-greater-than-1
      (implies (and (is-bv x))
               (>= (leading-1 x 1) 1))))

 (local
  (defthm useful-bvfrac-1
      (implies (and (is-bv x)(<= (leading-1 x 1) (len x) ))
	       (equal (bv-frac x 1)
		      (* (expt 2 (- (leading-1 x 1)))
			 (+ 1 (bv-frac (discard (leading-1 x 1) x) 1)))))
    :hints  (("Goal"
	      :in-theory (enable bv-frac-lemma-eqv)))))

 (local
  (defthm useful-bvfrac-lemma2
      (implies (and (is-bv x)(natp k)(not (zp k))(< k (len x))(integerp j))
	       (equal (bv-frac x j)
		      (+ (/  (bv-frac (discard k x) j)
		             (expt 2 k))
			 (bv-frac (takes k x) j))))
    :hints (("Goal"
	     :in-theory (enable bv-frac-lemma-eqv)))))

 (local
  (defthm useful-bvfrac-lemma4
      (implies (and (is-bv x)(natp k)(not (zp k))(< k (len x)))
	       (equal (* (bv-frac x 1)
			 (expt 2 k))
		      (+ (*  (bv-frac (takes k x) 1)
		             (expt 2 k))
			 (bv-frac (discard k x) 1))))))

 (local
  (defthm bv-dec-bv-frac-eqv
      (implies (and (is-bv x))
	       (equal (unsigned-bv-dec x)
		      (* (bv-frac x 1) (expt 2 (len x)))))
    :hints (("Goal"
	     :in-theory (enable bv-frac-lemma-eqv)))))

 (local
  (defthm try-2
      (implies (and (is-bv x)(natp k)(not (zp k))(< k (len x))(<= (leading-1 x 1) (len x)))
	       (equal (+ (unsigned-bv-dec (takes k x))
			 (bv-frac (discard k x) 1))
		      (* (+ 1 (bv-frac (discard (leading-1 x 1) x) 1))
			 (expt 2 (- k (leading-1 x 1)) ))))
    :hints (("Goal'''"
	     :use ((:instance useful-bvfrac-lemma4 )
		   (:instance  useful-bvfrac-1))))))

 (local
  (defthm try-3
      (implies (and (is-bv x)(natp k)(not (zp k))(< k (len x))
		    (equal (leading-1 x 1) (len x)))
	       (equal  (bv-frac (discard k x) 1)
		       (expt 2 (- k (len x)) )))))

 (defthm unnormalize-makes-mantissa-len-atleast-3
      (implies (is-fp x)
               (> (len (nth 2 (un-normalize-fp x)))  2)))

 
 (defthm normalize-eqv
     (implies (and (is-fp x)(> (len (nth 2 x)) 2))
              (equal (fp-rat-normal (normalize-fp x))
                     (fp-rat-unnormal x)))
   :hints  (("Goal"
	     :in-theory (disable  bv-dec-bv-frac-eqv
				  leading-1-all-takess-before-is-zero-vector
				  leading-1-all-takess-before-is-zero-in-decimal))))

 (defthm un-normalize-eqv
     (implies (and (is-fp x))
              (equal (fp-rat-unnormal (un-normalize-fp x))
                     (fp-rat-normal x))))

 )
