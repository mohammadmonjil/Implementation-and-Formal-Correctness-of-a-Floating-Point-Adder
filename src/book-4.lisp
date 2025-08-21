(encapsulate
 ()
 (local
  (include-book "arithmetic-5/top" :dir :system))

 (local
  (defthm bv-add-len-lemma
      (implies (and (is-bv x) (is-bv y)(equal (len x) (len y)))
               (equal (len (cdr (bv-add x y )))
                      (len x))))       )

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
  (defthm bv-add-cdr-returns-consp
      (implies (and (is-bv x)(is-bv y)(equal (len x) (len y)))
               (consp (cdr (bv-add x y))))))

 (local
  (defthm bv-sub-len-lemma
      (implies (and (is-bv x) (is-bv y)(equal (len x) (len y)))
               (equal (len (cdr (bv-sub x y )))
                      (len x))))     )
 
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
  (defthm unsinged-bv-dec-retuns-intp
      (implies (is-bv x)
               (and (>= (unsigned-bv-dec x) 0)(integerp (unsigned-bv-dec x))))
    :rule-classes :type-prescription))

 (local
  (defthm singed-bv-dec-retuns-intp
      (implies (is-bv x)
               (integerp (signed-bv-dec x)))
    :rule-classes :type-prescription))

 (local
  (defthm singed-bv-dec-retuns-intpx
      (implies (is-bv x)
               (integerp (signed-bv-dec x)))))

 (local
  (defthm zero-vector-is-bv
      (implies (and (natp n)(not (zp n)))
	       (is-bv (zero-vector n)))))

 (local
  (defthm create-zero-exp-returns-bv
      (implies (is-bv x )
	       (is-bv (create-zero-exp x)))))

 (local
  (defthm is-zero-vector-implies-bv
      (implies (is-zero-vector x)
               (is-bv x))))

 (local
  (defthm zero-vector-is-is-zero-vector
      (implies (and (natp n)(not (zp n)))
               (is-zero-vector (zero-vector n)))))

 (defthm signed-bv-add-properties-bitsp
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))
		   (bitsp sx)(bitsp sy))	      
	      (bitsp (car (signed-bv-add sx x sy y)))))

 (defthm signed-bv-add-properties-bv
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))
		   (bitsp sx)(bitsp sy))	      
	      (is-bv (nth 1 (signed-bv-add sx x sy y)))))

 (defthm signed-bv-add-properties-len-inequality
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))
		   (bitsp sx)(bitsp sy) (> (len x) j))	      
	      (> (len (nth 1 (signed-bv-add sx x sy y))) j)))

 (defthm signed-bv-add-properties-len-equality
     (implies (and (is-bv x)(is-bv y)(equal (len x)(len y))
		   (bitsp sx)(bitsp sy))	      
	      (equal (len (nth 1 (signed-bv-add sx x sy y)))
		     (len x))))

 (defthm signed-bv-add-is-consp
     (implies (and (is-bv x)(is-bv y) (bitsp sx)(bitsp sy))
	      (consp (signed-bv-add  sx x sy y))))

 (local
  (defthm right-shift-returns-bv
      (implies (and (is-bv x)(natp n))
	       (is-bv (right-shift x n)))))

 (local
  (defthm add-trailing-zero-returns-bv
      (implies (and (is-bv x)(natp n))
	       (is-bv (add-trailing-zeros x n)))))

 (local
  (defthm right-shift-len
      (implies (and (is-bv x)(natp n))
	       (equal (len (right-shift x n))
		      (+ (len x) n)))))

 (local
  (defthm add-trailing-zero-len
      (implies (and (is-bv x)(natp n))
	       (equal (len (add-trailing-zeros x n))
		      (+ (len x) n)))))


 (defthm fp-add-un-norm-len
     (implies (are-unnorm-fps x y)
	      (> (len (nth 2 (fp-add-un-norm x y))) 2))
   :hints (("Goal"
	    :in-theory (disable signed-bv-add))))

 (defthm fp-add-un-norm-is-fp
     (implies (are-unnorm-fps x y)
	      (is-fp (fp-add-un-norm x y)))
   :hints (("Goal"
	    :in-theory (disable signed-bv-add))))

 (defthm norm-unnorm-predicate
     (implies (and (are-norm-fps x y))
	      (are-unnorm-fps (un-normalize-fp x) (un-normalize-fp y))))

 (defthm norm-implies-fp
     (implies (are-norm-fps x y)
	      (and (is-fp x)(is-fp y))))

 (defthm unnorm-implies-fp
     (implies (are-unnorm-fps x y)
	      (and (is-fp x)(is-fp y)
		   (> (len (nth 2 x)) 2)
		   (> (len (nth 2 y)) 2))))

 (defthm is-fp-is-consp
     (implies (is-fp x)
	      (consp x)))

 )
