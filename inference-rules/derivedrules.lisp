(in-package #:shadowprover)


(defun handle-DR1 (Premises Formula sortal-fn proof-stack)
  (let ((fresh
         (filter (lambda (CommonK-Agent)
                   (let ((C (first CommonK-Agent))
                         (a1 (first (second CommonK-Agent)))
                         (a2 (second (second CommonK-Agent))))
                       (and (common-knowledge? C) 
                            (not (elem `(knows ,a1 ,(modal-time (first CommonK-Agent))
                                               (knows ,a2 ,(modal-time (first CommonK-Agent))
                                                      ,(modal-F (first CommonK-Agent))))
                                       Premises)))))
                 (cartesian-product (list premises  
                                          (cartesian-power (agents* (cons Formula Premises)) 2))))))
    (if fresh 
        (let ((derived (optima:match (first fresh)
                         ((list (list 'common time F) agent) 
                          `(knows ,(first  agent) ,time
                                  (knows ,(second  agent) ,time ,F))))))
          (prove! (cons derived premises)
                 formula
                 :sortal-fn sortal-fn
                 :proof-stack 
                 (add-to-proof-stack proof-stack 
                                     :DR2 
                                     derived 
                                     (list
                                      (princ-to-string (first fresh))))
                 :caller 'handle-DR1)))))
(defun handle-DR2 (Premises Formula sortal-fn proof-stack)
  (let ((fresh
         (filter (lambda (CommonK-Agent)
                   (and (common-knowledge? (first CommonK-Agent)) 
                        (not (elem `(knows ,(second CommonK-Agent)
                                           ,(modal-time (first CommonK-Agent))
                                           ,(modal-F (first CommonK-Agent)))
                                   Premises))))
                 (cartesian-product (list premises (agents* (cons Formula Premises)))))))
    (if fresh 
        (let ((derived (optima:match (first fresh)
                         ((list (list 'common time F) agent) `(knows ,agent
                                                                     ,time ,F)))))
          (prove! (cons derived premises)
                 formula
                 :sortal-fn sortal-fn
                 :proof-stack 
                 (add-to-proof-stack proof-stack 
                                     :DR2 
                                     derived 
                                     (list
                                      (princ-to-string (first fresh))))
                 :caller 'handle-DR2)))))

(defun matches? (x y) (equalp x y))
(defun unused-DR9-terms (Premises Formula)
(filter (lambda (Knows-Term)
                   (let ((K (first Knows-Term))
                         (term (second Knows-Term)))
                     ;(print Knows-Term)
                       (and (knowledge? K) 
                            (universal? (modal-F K))
                            (matches? (first (var-sorts (vars (modal-F K))))
                                      (sorts:get-sort term *signature*))
                            (not (elem `(knows 
                                         ,(modal-agent K)
                                         ,(modal-time K)
                                         ,(specialize (modal-F K) term))
                                       Premises)))))
                 (cartesian-product (list premises 
                                          (terms* (cons Formula Premises))))))

(defun handle-DR9 (Premises Formula sortal-fn proof-stack)
  (let ((fresh
         (unused-DR9-terms Premises Formula)))
     (if fresh 
        (let ((derived (optima:match (first fresh)
                         ((list (list 'knows agent time F) term) 
                          `(knows ,agent
                                  ,time ,(specialize F term))))))
          (prove! (cons derived premises)
                 formula
                 :sortal-fn sortal-fn
                 :proof-stack 
                 (add-to-proof-stack proof-stack 
                                     :D9 
                                     derived 
                                     (list
                                      (princ-to-string (first fresh))))
                 :caller 'handle-DR9)))))


(defun unused-univ-elim-terms (Premises Formula)
(filter (lambda (Univ-Term)
                   (let ((U (first Univ-Term))
                         (term (second Univ-Term)))
                       (and (universal? U)
                            (matches? (first (var-sorts (vars U)))
                                      (sorts:get-sort term *signature*))
                            (not (elem (specialize U term)
                                       Premises)))))
                 (cartesian-product (list premises 
                                          (terms* (cons Formula Premises))))))

(defun handle-univ-elim (Premises Formula sortal-fn proof-stack)
  (let ((fresh
         (unused-univ-elim-terms Premises Formula)))
     (if fresh 
        (let ((derived (optima:match (first fresh)
                         ((list F term) 
                          (specialize F term)))))
          (prove! (cons derived premises)
                 formula
                 :sortal-fn sortal-fn
                 :proof-stack 
                 (add-to-proof-stack proof-stack 
                                     :D9 
                                     derived 
                                     (list
                                      (princ-to-string (first fresh))))
                 :caller 'handle-DR9)))))



(define-type-1-expander handle-DR3 nil
  P (list 'common _ P))

(define-type-1-expander handle-DR4 nil 
  (list 'knows a time P) 
  (list 'sees a time P))

(define-type-1-expander handle-DR5 nil 
  (list 'believes a time P) 
  (list 'knows a time P))

(define-type-1-expander handle-DR6 
    (lambda (pair)
      (let ((K1 (first pair))
            (K2 (second pair)))
        (and (knowledge? K1)
             (knowledge? K2)
             (implies? (modal-F K1))
             (equalp (antecedent  (modal-F K1))
                     (modal-F K2))))) 
  (list 'knows a time P2) 
  (list 'knows a time (list 'implies _ P2))
  (list 'knows _ _ _)) 
 
(define-type-1-expander handle-DR12 nil 
  (list 'believes a1 time  (list 'believes a2 time P)) 
  (list 'believes a1 time (list 'knows a2 _ P)))
