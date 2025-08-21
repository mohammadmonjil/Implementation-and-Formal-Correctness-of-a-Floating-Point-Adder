(include-book "arithmetic-5/top" :dir :system)

(defthm singed-bv-dec-returns-intp
    (implies (force(is-bv x))
             (integerp (signed-bv-dec x)))
  :rule-classes (:rewrite :type-prescription ))

(defthm is-bv-implies-consp
    (implies (is-bv x)
	     (consp x)))

(defthm right-shift-returns-bv
    (implies (and (is-bv x)(natp n))
             (is-bv (right-shift x n)))
:rule-classes ( :rewrite ))

(defthm add-trailing-zero-returns-bv
    (implies (and (is-bv x)(natp n))
             (is-bv (add-trailing-zeros x n)))
    :rule-classes ( :rewrite))


(defthm right-shift-len
    (implies (and (is-bv x)(natp n))
             (equal (len (right-shift x n))
                    (+ (len x) n))))


(defthm add-trailing-zero-len
    (implies (and (is-bv x)(natp n))
             (equal (len (add-trailing-zeros x n))
                    (+ (len x) n))))

(defthm right-shift-car-nil
    (implies (and (is-bv x)(natp n)(0-bitp (car x)))
             (0-bitp (car (right-shift x n)))))

(defthm app-nil-is-zero
    (implies (and (is-bv x)(not (is-zero-vector x)))
             (not (is-zero-vector (app x (list nil))))))

(defthm right-shift-cdr-t
    (implies (and (is-bv x)(natp n)(0-bitp (car x))(not (is-zero-vector (cdr x)))(> (len x) 1))
             (not (is-zero-vector (cdr (right-shift x n))))))

(defthm add-trailing-zero-car-nil
    (implies (and (is-bv x)(natp n)(0-bitp (car x)))
             (0-bitp (car (add-trailing-zeros x n)))))


(defthm stupid-3
    (implies (and (is-bv (cdr x))(natp n)(0-bitp (car x)))
	     (is-bv (cdr (add-trailing-zeros x n)))))

(defthm add-trailing-zero-cdr-t
    (implies (and (is-bv x)(natp n)(0-bitp (car x))(not (is-zero-vector (cdr x)))(> (len x) 1))
             (not (is-zero-vector (cdr (add-trailing-zeros x n))))))

(defthm stupid-hack-1
    (implies (and (0-bitp (car x) )
                  (not (is-zero-vector x)))
             (not (is-zero-vector (cdr x)))))

(defthm stupid-hack-2
    (implies (and (is-bv x)(1-bitp (cadr x)))
             (not (is-zero-vector (cdr x)))))

                 
(defthm zero-vector-is-is-zero
    (implies (and (natp n)(not (zp n)))
	     (is-zero-vector (zero-vector n))))

                 
(defthm zero-vector-is-bv
    (implies (and (natp n)(not (zp n)))
	     (is-bv (zero-vector n))))

(defthm right-shift-len-inequality
    (implies (and (is-bv x)(natp n)(> (len x) j) (integerp j) )
             (> (len (right-shift x n)) j)))

(defthm add-trailing-zeros-len-inequality
    (implies (and (is-bv x)(natp n)(> (len x) j) (integerp j) )
             (> (len (add-trailing-zeros x n)) j)))

















(defthm fp-add-un-norm-lemma
    (implies (and (are-unnorm-fps x y))
             (equal (fp-rat-unnormal (fp-add-un-norm x y))
                    (+ (fp-rat-unnormal y)
                       (fp-rat-unnormal x))))


  :hints (("Goal"
	   :in-theory (disable is-bv  1-bitp 0-bitp len fp-rat-unnorm-help signed-bv-dec signed-bv-add))))


(defthm fp_add_final_thm
    (implies (and (are-norm-fps x y))
	     (equal (fp-rat-normal (fp-add-norm x y))
		    (+ (fp-rat-normal x)
		       (fp-rat-normal y))))
  :hints (("Goal"
	   :in-theory (disable  normalize-fp  un-normalize-fp are-unnorm-fps  are-norm-fps fp-add-un-norm fp-rat-normal fp-rat-unnormal))))


