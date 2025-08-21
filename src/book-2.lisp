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
  (defthm 1bit-t-equal-1
      (implies (and (equal (car x) t) (is-bv x) (equal (len x) 1)) 
               (equal (unsigned-bv-dec x) 1 ))))
 (local
  (defthm 1bit-nil-equal-0
      (implies (and (not (equal (car x) t)) (is-bv x) (equal (len x) 1))
               (equal (unsigned-bv-dec x) 0 ))))
 (local
  (defthm bv-add-len-lemma
      (implies (and (is-bv x) (is-bv y)(equal (len x) (len y)))
               (equal (len (cdr (bv-add x y )))
                      (len x)))))        
 (local
  (defthm bv-add-is-consp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (consp (bv-add x y)))))
 (local          
  (defthm bv-add-returns-bv
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (is-bv (bv-add x y)))))
 (local
  (defthm bv-add-cdr-returns-bv
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (is-bv (cdr (bv-add x y))))))
 (local
  (defthm bv-sub-len-lemma
      (implies (and (is-bv x) (is-bv y)(equal (len x) (len y)))
               (equal (len (cdr (bv-sub x y )))
                      (len x)))))        
 (local
  (defthm bv-sub-len-lemma2
      (implies (and (is-bv x) (is-bv y)(equal (len x) (len y)))
               (equal (len (bv-sub x y ))
                      (+ 1 (len x))))))
 (local
  (defthm bv-sub-is-consp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (consp (bv-sub x y)))))
 (local          
  (defthm bv-sub-returns-bv
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (is-bv (bv-sub x y)))))
 (local
  (defthm bv-sub-cdr-returns-bv
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (is-bv (cdr (bv-sub x y))))))
 (local
  (defthm is-bv-no-zero-len
      (implies (is-bv x)
               (> (len x) 0))))
 (local                        
  (defthm bv-adder-thm
      (implies
       (and (is-bv x ) (is-bv y )(equal (len x) (len y)))
       (equal (unsigned-bv-dec (bv-add x y ))
              (+ (unsigned-bv-dec x) (unsigned-bv-dec y))))
    :hints (("Goal"
             :induct (bv-add x y)))))
 (local
  (defthm bv-sub-thm
      (implies
       (and (is-bv x ) (is-bv y )(equal (len x) (len y)))
       (equal (unsigned-bv-dec (bv-sub x y ))
              (+ (* (bit-to-val (car (bv-sub x y))) (expt 2 (+ 1 (len x))))
                 (unsigned-bv-dec x)
                 (- (unsigned-bv-dec y)))))))
 
 
 (local
  (defthm bv-comp-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))(not (bv-comp x y)))
               (bv-comp y x))))
 (local
  (defthm unsigned-bv-dec-less-than-next-exp-of-len
      (implies (and (is-bv x))
               (> (expt 2 (len x)) (unsigned-bv-dec x)))))
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
  (defthm bv-add-bv-frac-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (equal (+ (bv-frac (cdr (bv-add x y)) 1)
                         (bit-to-val (car (bv-add x y))))
                      (+ (bv-frac x 1)
                         (bv-frac y 1))))))
 
 (local
  (defthm bv-add-discard-j-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))
                    (> (len x) j) (natp j))
               (equal (cdr (bv-add (discard j x) (discard j y)))
                      (discard j (cdr (bv-add x y)))))))
 (local
  (defthm bv-add-leave-takes-j-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(natp j)(< j (len x)))
               (equal (unsigned-bv-dec (takes (+ j 1) (bv-add x y)))
                      (+ (unsigned-bv-dec (takes j x ))
                         (unsigned-bv-dec (takes j y ))
                         (bit-to-val (car (bv-add (discard j x)(discard j y)))))))))
 (local
  (defthm bv-add-equality-for-unnormalized-x-y
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(natp j)(< j (len x))
                    (equal (car x) nil)(equal (car y) nil))
               (equal (unsigned-bv-dec (takes (+ j 1) (bv-add x y)))
                      (unsigned-bv-dec (takes j (cdr (bv-add x y))))))))
 
 (local
  (defthm try-bv-add
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(> (len x) 2)(equal (car x) nil)(equal (car y) nil) )
               (EQUAL (+ (UNSIGNED-BV-DEC (TAKES 2 (CDR (BV-ADD x y))))
                         (BV-FRAC (DISCARD 2 (CDR (BV-ADD x y)))
                                  1))
                      (+ (UNSIGNED-BV-DEC (TAKES 2 x))
                         (UNSIGNED-BV-DEC (TAKES 2 y))
                         (BV-FRAC (DISCARD 2 x) 1)
                         (BV-FRAC (DISCARD 2 y) 1))))
    :hints (("Goal"
             :use ((:instance bv-add-bv-frac-lemma (x (discard 2 x)) (y (discard 2 y)) )
                   (:instance bv-add-discard-j-lemma (j 2))
                   (:instance bv-add-leave-takes-j-lemma (j 2) )
                   (:instance bv-add-equality-for-unnormalized-x-y  (j 2) ))))))
 (local
  (defthm bv-sub-borrow-out-zero-for-bv-comp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(bv-comp x y ))
               (equal (car (bv-sub x y)) nil))
    :hints (("Goal"
             :induct (bv-sub x y)))))
 (local
  (defthm bv-sub-borrow-out-one-for-not-bv-comp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(not (bv-comp x y )))
               (equal (car (bv-sub x y)) t))
    :hints (("Goal"
             :induct (bv-sub x y)))))
 (local
  (defthm bv-sub-bv-frac-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (equal (- (bv-frac (cdr (bv-sub x y)) 1)
                         (bit-to-val (car (bv-sub x y))))
                      (- (bv-frac x 1)
                         (bv-frac y 1))))))
 
 (local
  (defthm bv-sub-discard-j-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))
                    (> (len x) j) (natp j))
               (equal (cdr (bv-sub (discard j x) (discard j y)))
                      (discard j (cdr (bv-sub x y)))))))
 (local
  (defthm bv-sub-equality-for-unnormalized-x-y
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(natp j)(< j (len x))
                    (equal (car x) nil)(equal (car y) nil)(bv-comp x y ))
               (equal (unsigned-bv-dec (takes (+ j 1) (bv-sub x y)))
                      (unsigned-bv-dec (takes j (cdr (bv-sub x y))))))))
 (local           
  (defthm bv-sub-leave-takes-j-lemma
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(natp j)(< j (len x)))
               (equal (unsigned-bv-dec (takes (+ j 1) (bv-sub x y)))
                      (- (+ (unsigned-bv-dec (takes j x ))
                            (* (bit-to-val (car (bv-sub x y)))
                               (expt 2 (+ j 1))))
                         (+ (unsigned-bv-dec (takes j y ))
                            (bit-to-val (car (bv-sub (discard j x)(discard j y))))))))))
 (local
  (defthm bv-sub-leave-takes-j-lemma-sp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(natp j)(< j (len x))(bv-comp x y))
               (equal (unsigned-bv-dec (takes (+ j 1) (bv-sub x y)))
                      (- (unsigned-bv-dec (takes j x ))
                         (+ (unsigned-bv-dec (takes j y ))
                            (bit-to-val (car (bv-sub (discard j x)(discard j y))))))))
    :hints (("Goal"
             :use ((:instance bv-sub-leave-takes-j-lemma)
                   (:instance bv-sub-borrow-out-zero-for-bv-comp))
             :in-theory (disable bv-sub-leave-takes-j-lemma bv-sub-borrow-out-zero-for-bv-comp)))))
 
 (local
  (defthm try-bv-sub
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y))(> (len x) 2)(equal (car x) nil)(equal (car y) nil) 
                    (bv-comp x y))
               (EQUAL (+ (UNSIGNED-BV-DEC (TAKES 2 y))
                         (BV-FRAC (DISCARD 2 y) 1)
                         (UNSIGNED-BV-DEC (TAKES 2 (CDR (BV-SUB x y))))
                         (BV-FRAC (DISCARD 2 (CDR (BV-SUB x y))) 1))
                      (+ (UNSIGNED-BV-DEC (TAKES 2 x))
                         (BV-FRAC (DISCARD 2 x) 1))))
    
    :hints (("Goal"
             :use ((:instance bv-sub-bv-frac-lemma (x (discard 2 x)) (y (discard 2 y)) )
                   (:instance bv-sub-discard-j-lemma (j 2))
                   (:instance bv-sub-leave-takes-j-lemma-sp (j 2) )
                   (:instance bv-sub-equality-for-unnormalized-x-y  (j 2) ))
             :in-theory (disable bv-sub-equality-for-unnormalized-x-y bv-sub-leave-takes-j-lemma-sp bv-sub-discard-j-lemma bv-sub-bv-frac-lemma)))))
 


 (defthm signed-bv-add-preserves-fp-rat-unnorm-help
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))(> (len x) 2)
		   (bitsp sx)(bitsp sy)(0-bitp (car x))(0-bitp (car y)))
              (equal (fp-rat-unnorm-help (car (signed-bv-add sx x sy y)) 
                                         (nth 1 (signed-bv-add sx x sy y)))
                     (+ (fp-rat-unnorm-help sx x)
			(fp-rat-unnorm-help sy y))))
   :hints (("Goal"
            :in-theory (disable takes discard bv-add bv-sub bv-frac-lemma1))))
 (local
  (defthm bv-add-cdr-lemma-non-zero
      (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))(> (len x) 1)
                    (0-bitp (car x))(0-bitp (car y))
                    (not (is-zero-vector (cdr x)))(not (is-zero-vector (cdr y))))
               (not (is-zero-vector   (cdr (bv-add x y)))))))


 (defthm signed-bv-add-for-same-sign-is-not-zero-vector
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))(> (len x) 1)
                   (0-bitp (car x))(0-bitp (car y))
                   (not (is-zero-vector (cdr x)))(not (is-zero-vector (cdr y)))
                   (or (and (0-bitp sx)(0-bitp sy))
                       (and (1-bitp sx)(1-bitp sy))))
              (not (is-zero-vector (nth 1 (signed-bv-add sx x sy y))) ))
   :hints (("Goal"
            :in-theory ( disable bv-add bv-sub))))
 )
