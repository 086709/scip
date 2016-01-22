(use srfi-1)

(define (quotify tr sy)
  (? tr sy `',sy sy))


(define (deriv exp var)
  (cond ((number? exp) 0)

	((variable? exp)
	 (if (same-variable? exp var) 1 0))

	((sum? exp)
	 (eval `(make-sum ,@(map (lambda (t)
				   (let ((dv (deriv t var)))
				     (if (number? dv)
					 dv
					 `',dv)))
				 exp))))
	((product? exp)
	 (make-sum
	  (make-product (multiplier exp)
			(deriv (multiplicand exp) var))
	  (make-product (deriv (multiplier exp) var)
			(multiplicand exp))))

	((exponentiation? exp)
	 (make-product (exponent exp)
		       (make-product
			(make-exponentiation
			 (base exp)
			 (- (exponent exp) 1))
			(deriv (base exp) var))))

	((trig? exp)
	 (cond ((sin? exp)
		(make-product (make-trig 'cos
					 (trig-subexp exp))
			      (deriv (trig-subexp exp) var)))
	       ((cos? exp)
		(make-product -1
			      (make-product (make-trig 'sin
						       (trig-subexp exp))
					    (deriv (trig-subexp exp) var))))))

	(else
	 (error "unknown expression type -- DERIV" exp))))



(define (variable? x) (symbol? x))
(define (same-variable? v1 v2)
  (and (variable? v1) (variable? v2) (eq? v1 v2)))

(define (make-sum . ad)
  #|makes addition lists of a variable
  number of arguments, does some simplification
  as possible|#
  (define (accumulate-terms lst)
    #|takes the list of terms ad
    and sums up the numeric terms
    while filtering out the non-numeric terms
    into another list, returning a new list with 
    the non-numeric terms tailed with the number 
    sum|#
    (define (accumulate-terms-help lst num-sum other-terms)
      (cond ((null? lst) `(,@other-terms ,num-sum))
	    ((number? (car lst)) (accumulate-terms-help
				  (cdr lst)
				  (+ num-sum (car lst))
				  other-terms))
	    (else (accumulate-terms-help (cdr lst)
					 num-sum
					 (cons (car lst) other-terms)))))
    (accumulate-terms-help lst 0 '()))
  (define (flatten lst sym)
    #|flattens all terms matching the symbol
    i.e: '(+ 1 3 4 (+ 5 x)) -> '(+ 1 3 4 5 x)
    i.e: '(+ (+ 2 x) (* x 4)) -> '(+ 2 x (* x 4))|#
    (cond ((eq? lst '()) '())
	  ((list? (car lst))
	   (cond ((eq? (caar lst) sym)
		  (append (flatten (car lst) sym) (flatten (cdr lst) sym)))
		 (else (cons (car lst) (flatten (cdr lst) sym)))))
	  (else
	   (cons (car lst) (flatten (cdr lst) sym)))))
  #|flattens the list for addition sub-terms
  , and then filteres out andy stray plusses and zero
  terms|#
  (let* ()
    (define ret
      (filter (lambda (p)
		(not (eq? p 0)))
	      (cond ((> (length ad) 1)
		     `(+ ,@(accumulate-terms
			    (filter (lambda (q)
				      (not (eq? q '+)))
				    (flatten ad '+)))))
		    (else ad))))
    #|if the resulting list from above
    contains only the symbol + and one 
    term, then return the term, 
    else returns the list|#
    (cond ((> (length ret) 2)
	   ret)
	  (else (cadr ret)))))

(define (addend s) (cadr s))

(define (augend s) (cddr s))

(define (sum? x)
  (and (pair? x) (eq? (car x) '+)))

(define (product? x)
  (and (pair? x) (eq? (car x) '*)))

(define (make-product . ms)
  (define (accumulate-product-terms tr)
    (define (accumulate-terms-help lst num-prod other-terms)
      (cond ((null? lst) `(,num-prod ,@other-terms))
	    ((number? (car lst)) (accumulate-terms-help
				  (cdr lst)
				  (* num-prod (car lst))
				  other-terms))
	    (else (accumulate-terms-help (cdr lst)
					 num-prod
					 (cons (car lst) other-terms)))))
    (accumulate-terms-help tr 1 '()))
  
  (define (flatten-p lst sym)
    (cond ((eq? lst '()) '())
	  ((and (list? (car lst))
		(eq? (caar lst) sym)
		(eq? '() (filter symbol? (car lst))))
	   (append (flatten-p (car lst) sym) (flatten-p (cdr lst) sym)))
	  (else (cons (car lst) (flatten-p (cdr lst) sym)))))

  (let ((ln (length ms)))
    (define re
      (cond ((eq? '() (filter (lambda (t)
				(cond ((symbol? t) #f)
				      ((pair? t) #f)
				      ((zero? t) #t)
				      (else #f)))
			      ms))
	     `(* ,@(accumulate-product-terms
		    (filter (lambda (r)
			      (not (equal? r 1)))
			    (filter (lambda (q)
				      (not (eq? q '*)))
				    (flatten-p ms '*))))))
	    (else 0)))
    (cond ((list? re)
	   (cond ((> (length re) 2)
		  re)
		 ((eq? (length re) 2) (cadr re))
		 (else re)))
	  (else re))))
	  
(define (multiplier p)
  (cadr p))
(define (multiplicand p)
  (cond ((> (length p) 3)
	 `(* ,@(cddr p)))
	(else (caddr p))))
	 
(define (exponentiation? x)
  (and (pair? x) (eq? (car x) '**)))

(define (base exp)
  (cadr exp))

(define (exponent exp)
  (caddr exp))

(define (make-exponentiation
	 base expo)
  (cond ((equal? expo 0) 1)
	((equal? expo 1) base)
	(else (list '** base expo))))

(define (trig? exp)
  (cond ((or (eq? 'sin (car exp))
	     (eq? 'cos (car exp))
	     (eq? 'tan (car exp)))
	 #t)
	(else #f)))

(define (make-trig fun subexp)
  (list fun subexp))

(define (sin? exp)
  (eq? (car exp) 'sin))

(define (cos? exp)
  (eq? (car exp) 'cos))

(define (trig-subexp exp)
  (cadr exp))

(define (symbol-replace exp sym rep)
  (map (lambda (s)		
	 (cond ((eq? s sym) rep)
	       ((pair? s) (symbol-replace s sym rep))
	       (else s)))
       exp))

(define (** base exp)
  (cond ((eq? exp 0) 1)
		((eq? exp 1) base)
	(else (* base (** base (- exp 1))))))

(define (disp-derv exp var)
  (printf "Expression: ~A~N" exp)
  (printf "Derivative: ~A~N" (deriv exp var)))

(disp-derv '(* (** x 3) (** x 2)) 'x)
(disp-derv '(** x 3) 'x)
(disp-derv '(sin (** x 4)) 'x)
