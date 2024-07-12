(set-logic ALL)

(declare-const x (_ BitVec 8))

(assert (= 
    x
    (select ((as (_ god_save_me_const |030102|) (Array (_ BitVec 32) (_ BitVec 8))) #x04) #x00000001)
))
