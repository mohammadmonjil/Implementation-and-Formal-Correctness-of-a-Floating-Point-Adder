;$ACL2s-SMode$;ACL2s
(encapsulate
  ()
  (local
   (include-book "arithmetic-5/top" :dir :system))
  (local
   (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                 HIST PSPV))))
  (local 
   (defthm takes-len-equal
     (implies (and (is-bv x)(natp n)(< n (len x)))
              (equal (len (takes  n x)) n))))
  (local
   (defthm takes-returns-bv
     (implies (and (is-bv x)(natp n)(< n (len x))(not (zp n)))
              (is-bv (takes n x )))))
  (local   
   (defthm discard-len-equal
     (implies (and (is-bv x)(natp n)(< n (len x)))
              (equal (len (discard  n x)) (- (len x) n)))))
  (local
   (defthm discard-returns-bv
     (implies (and (is-bv x)(natp n)(< n (len x)))
              (is-bv (discard n x )))))
  (local
   (defthm unsinged-bv-dec-retuns-intergerp
     (implies (and (is-bv x))
              (integerp (unsigned-bv-dec x)))))
  (local
   (defthm bv-frac-lemma1
     (implies (and (is-bv x)(integerp j))
              (equal (bv-frac x (+ j 1))
                     (* 1/2 (bv-frac x j))))))
  (local
   (defthm right-shift-returns-bv
     (implies (and (is-bv x)(natp n))
              (is-bv (right-shift x n)))))
  (local
   (defthm right-shift-len-lemma
     (implies (and (is-bv x)(natp n))
              (equal (len (right-shift x n)) (+ (len x) n)))))
  (local
   (defthm right-shift-divides-bv-frac-power2n
     (implies (and (is-bv x)(natp n))
              (equal (bv-frac (right-shift x n) 1) 
                     (/ (bv-frac x 1) (expt 2 n))))))
  (local
   (defthm add-trailing-zero-returns-bv
     (implies (and (is-bv x)(natp n))
              (is-bv (add-trailing-zeros x n)))))
  (local
   (defthm add-trailing-zeros-len-lemma
     (implies (and (is-bv x)(natp n))
              (equal (len (add-trailing-zeros x n)) (+ (len x) n)))))
  (local
   (defthm len-app-nil
     (implies  (is-bv x)
               (equal (len (app x (list nil)))
                      (+ (len x) 1) ))))
  (local
   (defthm dec-to-bv-app-nil
     (implies (is-bv x)
              (equal (unsigned-bv-dec (app x (list nil)))
                     (* 2 (unsigned-bv-dec x))))))
  (local
   (defthm add-trailing-zeros-multiplies-bv-dec-power2n
     (implies (and (is-bv x)(natp n))
              (equal (unsigned-bv-dec (add-trailing-zeros x n)) 
                     (* (unsigned-bv-dec x) (expt 2 n))))))
  (local   
   (defthm app-nil-preserves-bv
     (implies (is-bv x)
              (is-bv (app x (list nil))))))
  (local   
   (defthm app-t-preserves-bv
     (implies (is-bv x)
              (is-bv (app x (list t))))))
  (local   
   (defthm app-nil-before-preserves-bv
     (implies (is-bv x)
              (is-bv (app (list nil) x )))))
  (local
   (defthm bv-frac-bv-dec-lemma1
     (implies (is-bv x)
              (equal (unsigned-bv-dec x)
                     (* (expt 2 (len x)) (bv-frac x 1))))))
  (local   
   (defthm bv-frac-take-0-is-0
     (implies (and (is-bv x))
              (equal (bv-frac (take 0 x) 1)
                     0))))
  (local   
   (defthm bv-frac-lemma3
     (implies (and (is-bv x)(natp j)(< j (len x))(not (zp j))(integerp k))
              (equal (bv-frac x k)
                     (+ (bv-frac (takes j x) k)
                        (* (expt 2 (- j))
                           (bv-frac (discard j x) k)))))
     :hints (("Subgoal *1/5"
              :cases ((> j 1)) ))))
  (local   
   (defthm bv-frac-bv-dec-lemma
     (IMPLIES (AND (IS-BV X) (< k (LEN X))(natp j)(natp k)(> k j))
              (EQUAL (+ (* (expt 2 (- k j)) (UNSIGNED-BV-DEC (TAKES j X)))
                        (* (expt 2 (- k j)) (BV-FRAC (DISCARD j X) 1)))
                     (+ (UNSIGNED-BV-DEC (TAKES k X))
                        (BV-FRAC (DISCARD k X) 1))))))
  (local   
   (defthm bv-frac-bv-frac-lemma
     (IMPLIES (AND (IS-BV X) (< k (LEN X))(natp j)(natp k)(> k j)(not (zp j)))
              (EQUAL (+ (* (expt 2 k) (bv-frac (TAKES j X) 1))
                        (* (expt 2 (- k j)) (BV-FRAC (DISCARD j X) 1)))
                     (+ (* (expt 2 k) (bv-frac (TAKES k X) 1))
                        (BV-FRAC (DISCARD k X) 1))))
     :hints (("Goal"
              :in-theory (disable bv-frac-bv-dec-lemma bv-frac-bv-dec-lemma1 bv-frac-lemma1  bv-frac-lemma3)
              :use ((:instance bv-frac-bv-dec-lemma)
                    (:instance bv-frac-bv-dec-lemma1 (x (TAKES k X) ))
                    (:instance bv-frac-bv-dec-lemma1 (x (TAKES j X) )))))))
  (local   
   (defthm try-new
     (implies (and (is-bv x)(> (len x) 2))
              (EQUAL (+ (BV-FRAC (DISCARD 1 X) 0)
                        (* 2 (BV-FRAC (TAKES 1 X) 0)))
                     (+ (* 2 (BV-FRAC (TAKES 2 X) 0))
                        (* 1/2 (BV-FRAC (DISCARD 2 X) 0)))))
     :hints (("Goal"
              :in-theory (disable bv-frac-bv-frac-lemma  bv-frac-lemma1)
              :use ((:instance bv-frac-lemma1 (x (takes 1 x)) (j 0) )
                    (:instance bv-frac-lemma1 (x (takes 2 x)) (j 0) )
                    (:instance bv-frac-lemma1 (x (discard 1 x)) (j 0) )
                    (:instance bv-frac-lemma1 (x (discard 2 x)) (j 0) )
                    (:instance bv-frac-bv-frac-lemma (j 1)(k 2)))))))
  
  (defthm fp-rat-help-right-shift
    (implies (and (is-bv x)(bitsp s)(natp n)(> (len x) 2))
             (equal (fp-rat-unnorm-help s (right-shift x n))
                    (/ (fp-rat-unnorm-help s x) (expt 2 n)))))
  (local   
   (defthm takes-app-lemma
     (implies (and (is-bv x)(natp j)(< j (len x)))
              (equal (takes j (app x (list nil)))
                     (takes j x)))))
  (local
   (defthm adding-zero-takes-equality
     (implies (and (is-bv x)(> (len x) j)(natp n)(natp j))
              (equal (takes j (add-trailing-zeros x n))
                     (takes j x)))))
  
  (local
   (defthm adding-zero-discard-bv-frac-equality
       (implies (and (is-bv x)(> (len x) j)(natp n)(natp j)(integerp k))
		(equal (bv-frac (discard j (add-trailing-zeros x n)) k)
                       (bv-frac (discard j x) k )))
     :hints (("Goal"
              :in-theory (disable bv-frac-lemma3)))))
  
  (defthm fp-rat-help-add-trailing-zeros
      (implies (and (is-bv x)(bitsp s)(natp n)(> (len x) 2))
               (equal (fp-rat-unnorm-help s (add-trailing-zeros x n))
                      (fp-rat-unnorm-help s x))))


  (defthm bv-frac-zero-vector
      (implies (and (is-bv x)(integerp j)(is-zero-vector x))
	       (equal (bv-frac x j) 0)))
  
  (defthm unsigned-bv-dec-zero-vector
      (implies (and (is-bv x)(is-zero-vector x))
	       (equal (unsigned-bv-dec x) 0)))

  (defthm is-zero-takes
      (implies (and (is-bv x)(is-zero-vector x)(natp n)(< n (len x))(not (zp n)))
	       (is-zero-vector (takes n x))))


  (defthm is-zero-discards
      (implies (and (is-bv x)(is-zero-vector x)(natp n)(< n (len x)))
	       (is-zero-vector (discard n x))))

  (defthm fp-rat-help-zero-vectors
      (implies (and (is-bv x)(bitsp s)(is-zero-vector x)(> (len x) 2))
               (equal (fp-rat-unnorm-help s x )
                      0 )))
  )
