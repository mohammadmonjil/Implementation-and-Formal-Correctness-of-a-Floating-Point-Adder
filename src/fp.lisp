

(defun 1-bitp (x)
  (equal x t))


(defun 0-bitp (x)
  (equal x nil))


(defun bitsp (x)
  (mbe :logic (or (1-bitp x) (0-bitp x))
       :exec (or (1-bitp x) (0-bitp x))))


(defthm bitp-not-0-implies-1
  (implies (and (bitsp x)
                (not (0-bitp x)))
           (1-bitp x))
  :rule-classes (:forward-chaining))

(defthm bitp-not-1-implies-0
  (implies (and (bitsp x)
                (not (1-bitp x)))
           (0-bitp x))
  :rule-classes (:forward-chaining))

(defthm 1-bitp-implies-bitsp
  (implies (1-bitp x)
           (bitsp x))
  :rule-classes (:forward-chaining))

(defthm 0-bitp-implies-bitsp
  (implies (0-bitp x)
           (bitsp x))
  :rule-classes (:forward-chaining))

(defthm not-0-bitp-but-is-bv
    (implies (and (is-bv x)(not (0-bitp (car x))))
	     (1-bitp (car x)))
  :rule-classes :forward-chaining)

(defthm not-1-bitp-but-is-bv
    (implies (and (is-bv x)(not (1-bitp (car x))))
	     (0-bitp (car x)))
  :rule-classes :forward-chaining)

;; (defthm bitp-not-1-implies-0-1
;;   (implies
;;                 (not (1-bitp x))
;;            (0-bitp x))
;;   :rule-classes (:forward-chaining))


(defun is-bv (x)
  (if (not (consp (cdr x)))
    (and (bitsp (car x)) (not (zp (len x)) ))
    (and (bitsp (car x))(is-bv (cdr x)) )))


(defun is-fp (x)
  (and (bitsp (nth 0 x) )
       (and (is-bv (nth 1 x)) (> (len (nth 1 x)) 1) )
       (is-bv (nth 2 x) )
       (equal (len x) 3) ))

(defun are-norm-fps (x y)
  (and (is-fp x)(is-fp y)
       (equal (len (nth 1 x)) (len (nth 1 y)))
       (equal (len (nth 2 x)) (len (nth 2 y)))))

(defun is-unnorm-fp (x)
  (and (is-fp x)
       (0-bitp (car (nth 2 x))) (1-bitp (cadr (nth 2 x)))
       (> (len (nth 2 x)) 2)))

(defun are-unnorm-fps (x y)
  (and (is-unnorm-fp x)(is-unnorm-fp y)
       (equal (len (nth 1 x)) (len (nth 1 y)))
       (equal (len (nth 2 x)) (len (nth 2 y)))))


(defun app (x y)
  (if (not (consp x))
    y
    (cons (car x) (app (cdr x) y))))

(defun discard (n x)
  (if (zp n)
    x
    (discard (- n 1) (cdr x) )))

(defun takes (n x)
  (if (zp n)
    nil
    (cons (car x) (takes (- n 1) (cdr x)) )))

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  
;(include-book "arithmetic-5/top" :dir :system)
  
  (defun to-bv (x)
    (if (zp x)
      (list nil)
      (if (equal (mod x 2) 1)
        (app (to-bv (floor (- x 1) 2)) (list t) )
        (app (to-bv (floor x 2)) (list nil) ))))  
  )

(defun unsigned-bv-dec (x)
  (if (not (consp x))
    0
    (if (1-bitp (car x))
      (+ (expt 2 (- (len x) 1)) (unsigned-bv-dec (cdr x)) )
      (unsigned-bv-dec (cdr x))))) 

(defun get-sign (x)
  (if (0-bitp x)
    1
    -1))

(defun signed-bv-dec (x)
  (* (get-sign (car x)) (unsigned-bv-dec (cdr x))))

(defun bv-frac (x i)
  (if (not (consp x))
    0
    (if (1-bitp (car x))
      (+ (expt 2 (* -1 i)) (bv-frac (cdr x) (+ i 1) ) )
      (bv-frac (cdr x) (+ i 1) ))))                

(defun one-vector (n)
  (if (zp n)
    (list t)
    (app (list t) (one-vector (- n 1)))))

(defun zero-vector (n)
  (if (zp n)
    nil
    (app (list nil) (zero-vector (+ n -1)) )))

(defun is-zero-vector (x)
  (if (not (consp (cdr x)))
    (and (0-bitp  (car x)) (not (zp (len x)) ))
    (and (0-bitp  (car x))(is-zero-vector (cdr x)) )))


(defun is-one-vector (x)
  (if (not (consp x))
    t
    (if (0-bitp (car x))
      nil
      (is-one-vector (cdr x))))) 

(defun full-adder (x y cin)
  (let* ((sum-bit (if (xor (1-bitp x) (1-bitp y))   
                    (if (1-bitp cin) nil t)       
                    (if (1-bitp cin) t nil)))    
         (carry-out (or (and (1-bitp x) (1-bitp y))  
                        (and (1-bitp x) (1-bitp cin)) 
                        (and (1-bitp y) (1-bitp cin))))) ; 
    (list carry-out sum-bit )))                     


(defun bv-add (x y)
  (if  (and (is-bv x) (is-bv y) (equal (len x) (len y)) )                
    (if (not (consp (cdr x)))
      ( full-adder (car x) (car y) nil)
      ( app  ( full-adder (car x) (car y) (car (bv-add (cdr x) (cdr y) )) ) (cdr (bv-add (cdr x) (cdr y) )) ))
    nil))

(defun full-subtractor (a b bin)
  (let* ((diff-bit (if (xor (1-bitp a) (1-bitp b))   
                     (if (1-bitp bin) nil t)        
                     (if (1-bitp bin) t nil)))    
         (borrow-out (or (and (not (1-bitp a)) (1-bitp b))  
                         (and (not (1-bitp a)) (1-bitp bin)) 
                         (and (1-bitp b) (1-bitp bin))))) 
    (list borrow-out diff-bit)))

(defun bv-sub (x y)
  (if  (and (is-bv x) (is-bv y) (equal (len x) (len y)) )                
    (if (not (consp (cdr x)))
      ( full-subtractor (car x) (car y) nil)
      ( app  ( full-subtractor (car x) (car y) (car (bv-sub (cdr x) (cdr y) )) ) (cdr (bv-sub (cdr x) (cdr y) )) ))
    nil))

;; (defun ones-complement (x)
;;   (if (not (consp x))
;;     x
;;     (if (equal (car x) )
;;       (app (list nil) (ones-complement (cdr x)) )
;;       (app (list t) (ones-complement (cdr x)) ))))


;; (defun twos-complement (x)
;;   (bv-add (ones-complement x) ( app ( zero-vector (- (len x) 1 )) (list t) )))
 

(defun right-shift (x n)
  (if (zp n)
    x
    (right-shift (app (list nil) x) (+ n -1))))       


(defun add-leading-zeros (x n)
  (if (zp n)
    x
    ( add-leading-zeros (app (list nil) x ) (+ n -1) )))

(defun add-trailing-zeros (x n)
  ( if (zp n)
    x 
    (app (add-trailing-zeros x (- n 1) ) (list nil) )))

(defun leading-1 (x p)
  (if (not (consp x))
    p
    (if (1-bitp (car x))
      p
      (leading-1 (cdr x) (+ p 1)))))

(defun get-mantissa (x)
  (let ((index (leading-1 x 1) )) 
    (if (equal index (len x))
      (list nil)    
      (discard index x ))))

(defun get-exponent (m e)
  (let ((e_new (- (signed-bv-dec e) (- (leading-1 m 1) 2 )))) 
    (if (>= e_new 0)
        ( app (list nil) (to-bv e_new) )
        ( app (list t)   (to-bv (- e_new))))))

(defun normalize-fp (x)
  (let ((s (nth 0 x))(e (nth 1 x))(m (nth 2 x)))
    (if (or (and (1-bitp (car e))(is-zero-vector (cdr e))) (is-zero-vector m) )
      (list s (app (list t) (zero-vector (- (len e) 1))) m)
      (list s (get-exponent m e) (get-mantissa m)))))

(defun un-normalize-fp (x)
  (let ((s (nth 0 x))(e (nth 1 x))(m (nth 2 x)))
    (list s e (app (list nil t) m))))

(defun zero-exp (x)
  (and (1-bitp (car x))(is-zero-vector (cdr x))))

(defun fp-rat-normal (x)
  (let ((s (nth 0 x)) (e (nth 1 x)) (m (nth 2 x) ))
    (if (zero-exp e)
      0
      (* (get-sign s)
         (expt 2 (signed-bv-dec e))
         (+ 1 (bv-frac m 1))))))

(defun fp-rat-unnorm-help (s m)
  (* (get-sign s)
     (+ (unsigned-bv-dec (takes 2 m)) (bv-frac (discard 2 m ) 1 ) )))

(defun fp-rat-unnormal (x)                                  ;mantissa with decimal point after first two bits
  (let ((s (nth 0 x)) (e (nth 1 x)) (m (nth 2 x) ))
    (if (zero-exp e)
      0
      (* (fp-rat-unnorm-help s m)
         (expt 2 (signed-bv-dec e))))))

(defun bit-to-val (x)
  (if (1-bitp x)
    1
    0))


(defun bv-comp (x y)
  (if (not (consp x))
    t
    (if (equal (car x)(car y))
      (bv-comp (cdr x)(cdr y))
      (if (and (1-bitp (car x))(0-bitp (car y)))
        t
        nil))))

(defun signed-bv-add (sx mx sy my)
  (cond ((and (0-bitp sx) (0-bitp sy)) 
         (list nil (cdr (bv-add mx my))))
        
        ((and (1-bitp sx) (0-bitp sy))   
         (if (bv-comp mx my)
           (list t (cdr (bv-sub mx my)))
           (list nil (cdr (bv-sub my mx)))))                     
        
        ((and (0-bitp sx) (1-bitp sy))
         (if (bv-comp mx my)
           (list nil (cdr (bv-sub mx my)))
           (list t (cdr (bv-sub my mx)))))                               
        
        ((and (1-bitp sx) (1-bitp sy))     
         (list t (cdr (bv-add mx my))))))

(defun create-zero-exp (x)
  (app (list t) (zero-vector (len x))))

(defun fp-add-un-norm (x y)
  (let* ((sx (nth 0 x))(ex (nth 1 x))(mx (nth 2 x))
         (sy (nth 0 y))(ey (nth 1 y))(my (nth 2 y)) 
         (decx (signed-bv-dec ex))(decy (signed-bv-dec ey)))
    
    (cond ((and (zero-exp ex)(zero-exp ey))
           (list sx ex mx))
          
          ((and (zero-exp ex) (not (zero-exp ey)))
           (list sy ey my))
          
	  ((and (not(zero-exp ex)) (zero-exp ey))
           (list sx ex mx))
          (t
           (if (>= decx decy)
             (let* ((mx  (add-trailing-zeros mx (- decx decy)))
                    (my  (right-shift my (- decx decy)))
                    (add  (signed-bv-add sx mx sy my))
                    (s  (nth 0 add))
                    (m  (nth 1 add)))
               (if (is-zero-vector m)
                 (list s (create-zero-exp ex) m)
                 (list s ex m)))
             (let* ((mx  (right-shift mx (- decy decx)))
                    (my  (add-trailing-zeros my (- decy decx)))
                    (add  (signed-bv-add sx mx sy my))
                    (s  (nth 0 add))
                    (m  (nth 1 add)))
               (if (is-zero-vector m)
                 (list s (create-zero-exp ey) m)
                 (list s ey m))))))))

(defun fp-add-norm (x y)
  (normalize-fp (fp-add-un-norm (un-normalize-fp x) (un-normalize-fp y))))
