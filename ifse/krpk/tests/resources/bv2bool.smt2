(set-logic ALL)
(declare-const a Bool)
(assert (bv2bool
    ((_ extract 0 0)
        ((_ sign_extend 7)
            (bool2bv a)
        )
    )
))