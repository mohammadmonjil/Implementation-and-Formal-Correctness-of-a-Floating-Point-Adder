(encapsulate
 ()
 (local
  (include-book "arithmetic-5/top" :dir :system))

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

 (local
  (defthm is-zero-vector-implies-bv
      (implies (is-zero-vector x)
               (is-bv x))))

 (local
  (defthm right-shift-returns-bv
      (implies (and (is-bv x)(natp n))
               (is-bv (right-shift x n)))))

 (local
  (defthm add-trailing-zero-returns-bv
      (implies (and (is-bv x)(natp n))
               (is-bv (add-trailing-zeros x n)))))

 (local
  (defthm right-shift-add-trailing-equality
      (implies (and (is-bv x)(natp n)(is-bv y)(equal (len x) (len y)))
	       (equal (len (right-shift x n))
		      (len (add-trailing-zeros y n))))))


 (local
  (defthm right-shift-len-equality
      (implies (and (is-bv x)(natp n)(> (len x) j))
	       (> (len (right-shift x n)) j))))


 (local
  (defthm add-trailing-zeros-len-equality
      (implies (and (is-bv x)(natp n)(> (len x) j))
	       (> (len (add-trailing-zeros x n)) j))))

 (local
  (defthm right-shift-car-nil
      (implies (and (is-bv x)(natp n)(0-bitp (car x)))
               (0-bitp (car (right-shift x n))))))

 (local
  (defthm add-trailing-zero-car-nil
      (implies (and (is-bv x)(natp n)(0-bitp (car x)))
               (0-bitp (car (add-trailing-zeros x n))))))

 (local
  (defthm stupid-hack-1
      (implies (and (0-bitp (car x))
                    (not (is-zero-vector x)))
               (not (is-zero-vector (cdr x))))))

 (local
  (prefer-positive-exponents))
 
 (local
  (defthm n1
      (implies(and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n2 n1)(or (and (1-bitp sx) (0-bitp sy))
									     (and (0-bitp sx) (1-bitp sy)))
		   (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		   (is-zero-vector (nth 1 (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))))
	      (equal (fp-rat-unnorm-help (car (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))
					 (nth 1 (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))) 
		     0))
    :hints (("Goal"
	     :in-theory (disable 1-bitp 0-bitp bitsp fp-rat-unnorm-help  signed-bv-add  )))))

 (local
  (defthm n2
      (implies (and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n2 n1)(or (and (1-bitp sx) (0-bitp sy))
									      (and (0-bitp sx) (1-bitp sy)))
		    (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		    (equal (fp-rat-unnorm-help (car (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))
					       (nth 1 (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))) 
			   0))
	       (equal (+ (*
			  (expt 2 n2)
			  (fp-rat-unnorm-help sy y))
			 (*
			  (expt 2 n1)
			  (fp-rat-unnorm-help sx x))) 
		      0))
    :hints (("Goal"
	     :in-theory (disable  1-bitp 0-bitp bitsp fp-rat-unnorm-help signed-bv-add)))))

 (defthm n34
     (implies (and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n2 n1)(or (and (1-bitp sx) (0-bitp sy))
									     (and (0-bitp sx) (1-bitp sy)))
		   (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		   (is-zero-vector (nth 1 (signed-bv-add sx (right-shift x (- n2 n1)) sy (add-trailing-zeros y (- n2 n1))))))
	      (equal (+ (* (expt 2 n2)
			   (fp-rat-unnorm-help sy y))
			(* (expt 2 n1)
			   (fp-rat-unnorm-help sx x)))
		     0))
   
   :hints (("Goal"
	    :in-theory (disable  n1 n2 fp-rat-unnorm-help signed-bv-add right-shift add-trailing-zeros)
	    :use ((:instance n1 )
		  (:instance n2 )))))


 
 (local
  (defthm n11
      (implies (and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n1 n2)(or (and (1-bitp sx) (0-bitp sy))
									      (and (0-bitp sx) (1-bitp sy)))
		    (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		    (is-zero-vector (nth 1 (signed-bv-add sx (add-trailing-zeros x (- n1 n2)) sy (right-shift y (- n1 n2))))))
	       (equal (fp-rat-unnorm-help (car (signed-bv-add sx (add-trailing-zeros x (- n1 n2)) sy (right-shift y (- n1 n2))))
					  (nth 1 (signed-bv-add sx (add-trailing-zeros x (- n1 n2)) sy (right-shift y (- n1 n2))))) 
		      0))
    :hints (("Goal"
	     :in-theory (disable 1-bitp 0-bitp bitsp fp-rat-unnorm-help  signed-bv-add )))))



 (local
  (defthm n22
      (implies (and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n1 n2)(or (and (1-bitp sx) (0-bitp sy))
									      (and (0-bitp sx) (1-bitp sy)))
		    (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		    (equal (fp-rat-unnorm-help (car (signed-bv-add sx (add-trailing-zeros x (- n1 n2)) sy (right-shift y (- n1 n2))))
					       (nth 1 (signed-bv-add sx (add-trailing-zeros x (- n1 n2)) sy (right-shift y (- n1 n2))))) 
			   0))
	       (equal (+ (* 
			  (expt 2 n2)
			  (fp-rat-unnorm-help sy y))
			 (* 
			  (expt 2 n1)
			  (fp-rat-unnorm-help sx x))) 
		      0))
    :hints (("Goal"
	     :in-theory (disable fp-rat-unnorm-help signed-bv-add)))))


 (defthm n3344
     (implies (and (is-bv x)(is-bv y)(integerp n1)(integerp n2)(>= n1 n2)(or (and (1-bitp sx) (0-bitp sy))
									     (and (0-bitp sx) (1-bitp sy)))
		   (equal (len x) (len y))(> (len x) 2)  (0-bitp (car x))(0-bitp (car y))
		   (is-zero-vector (nth 1 (signed-bv-add sx (add-trailing-zeros x (- n1 n2))
							 sy (right-shift y (- n1 n2))))))
	      (equal (+
		      (* (expt 2 n1)
			 (fp-rat-unnorm-help sx x)
			 )
		      (* (expt 2 n2)
		         (fp-rat-unnorm-help sy y)
			 ))
		     0))
   
   :hints (("Goal"
	    :in-theory (disable n11 n22 fp-rat-unnorm-help signed-bv-add right-shift add-trailing-zeros)
	    :use ((:instance n11 )
		  (:instance n22 )))))
 
 )

