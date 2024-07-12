(set-logic ALL)
(define-ctype int (_ BitVec 32))
(declare-cb abs (int) int)
(declare-const colossus_fresh_var_arr1 (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const x (Array (_ BitVec 32) (_ BitVec 8)))
(assert (=
    (concat 
        (select colossus_fresh_var_arr1 #x00000003)
        (concat 
            (select colossus_fresh_var_arr1 #x00000002)
            (concat 
                (select colossus_fresh_var_arr1 #x00000001) 
                (select colossus_fresh_var_arr1 #x00000000)
            ) 
        )        
    )
    (abs 
        (concat 
            (select x #x00000003)
            (concat 
                (select x #x00000002)
                (concat 
                    (select x #x00000001) 
                    (select x #x00000000)
                ) 
            )        
        )
    )
))
(assert (not
    (= 
        #x00000001 
        (concat 
            (select colossus_fresh_var_arr1 #x00000003)
            (concat 
                (select colossus_fresh_var_arr1 #x00000002)
                (concat 
                    (select colossus_fresh_var_arr1 #x00000001) 
                    (select colossus_fresh_var_arr1 #x00000000)
                ) 
            )        
        )
    )
))