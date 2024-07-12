(set-logic ALL)
(set-arch X86)
(declare-const arg (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not
    (= 
        #x25
        (select arg #x00000000)
    )
))
(assert false)