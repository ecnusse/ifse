(set-logic ALL)
(set-arch X86)
(define-ctype int (_ BitVec 32))
(define-ctype |const char*| (_ BitVec 64))
(declare-cb atoi (|const char*|) int)
(declare-const colossus_fresh_var_arr1 (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const symvar (Array (_ BitVec 32) (_ BitVec 8)))
(alloc #x0000000001290044 1
    (select symvar #x00000000)
)
(alloc #x0000000001290045 1
    #x00
)
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
    (atoi 
        #x0000000001290044
    )
))
(assert (=
    #x00000007
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
))