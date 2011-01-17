;(set-option print-success false)

(declare-fun _base () Int)
(assert (= _base 0))
(declare-fun n () Int)
(assert (>= n 0))

; maxdepth = 1
(declare-fun ___z3z___ (Int) Bool)
			; OK ;  OUTPUT/103
(declare-fun ___z4z___ (Int) Bool)
			; V13_b ;  LOCAL/104
(declare-fun ___z5z___ (Int) Bool)
			; V14_d ;  LOCAL/105
(declare-fun ___z6z___ (Int) Bool)
			; V40_a ;  LOCAL,STATE(1,)/106
(declare-fun ___z7z___ (Int) Bool)
			; V41_b ;  LOCAL,STATE(1,)/107
(declare-fun ___z8z___ (Int) Int)
			; V51_time ;  LOCAL,STATE(1,)/108


; ; Generic definitions:
(define-fun DEF__103 ((_M Int)) Bool (= (___z3z___ _M) (= (___z4z___ _M) (___z5z___ _M))))
 (define-fun DEF__104 ((_M Int)) Bool (= (___z4z___ _M) (and (___z6z___ _M) (___z7z___ _M))))
 (define-fun DEF__105 ((_M Int)) Bool (= (___z5z___ _M) (= (___z8z___ _M) 2)))
 (define-fun DEF__106 ((_M Int)) Bool (= (___z6z___ _M) (ite (= _M _base) false (not (___z7z___ (- _M 1))))))
 (define-fun DEF__107 ((_M Int)) Bool (= (___z7z___ _M) (ite (= _M _base) false (___z6z___ (- _M 1)))))
 (define-fun DEF__108 ((_M Int)) Bool (= (___z8z___ _M) (ite (= _M _base) 0 (ite (= (___z8z___ (- _M 1)) 3) 0 (+ (___z8z___ (- _M 1)) 1)))))

 (define-fun P ((_M Int)) Bool (___z3z___ _M))
 (define-fun trans ((_M Int)) Bool
 	    (and (DEF__103 _M)
 	    	 (DEF__104 _M)
 	    	 (DEF__105 _M)
 	    	 (DEF__106 _M)
 	    	 (DEF__107 _M)
 	    	 (DEF__108 _M)))

