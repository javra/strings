{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities

/n+ : ∀{m n} → /n {m + n} ~* ∣ ^⊗ m ⊗ /n {n} · /n {m} ⊗ ∣ ^⊗ n
/n+ {m} {zero} = - (~·* (- ∣^⊗suc) ■ ι ∣n· ■ ι ⊗ε)
/n+ {m} {suc n} = ·~* (~⊗* (/n+ {m} {n}) ■ - ⊗∣·⊗∣ ■ ·~* (-⊗⊗ ■ ⊗~* (- ∣^⊗suc))) ■ ι ··
                  ■ ~·* (~·* (~⊗* ∣^⊗+ ■ -⊗⊗) ■ ·~* -⊗⊗ ■ ∣n⊗·∣n⊗)

/n·∣⊗ : ∀{m n}{d : D m n} → /n · ∣ ⊗ d ~* d ⊗ ∣ · /n
/n·∣⊗ {d = ε}     = ·~* (ι ⊗ε) ■ - (~·* (ι ε⊗))
/n·∣⊗ {d = ∣}     = ·∣∣ ■ - ∣∣·
/n·∣⊗ {d = d · e} = ·~* (- ∣⊗·∣⊗) ■ ι ·· ■ ~·* /n·∣⊗ ■ -·· ■ ·~* /n·∣⊗
                    ■ ι ·· ■ ~·* ⊗∣·⊗∣
/n·∣⊗ {d = _⊗_ {m} {n} {k} {l} d e}
                  = ~·* (/n+ {m}{k})
                    ■ -·· ■ ·~* (·~* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ~⊗* /n·∣⊗ ■ ι ·⊗·)
                    ■ ι ·· ■ ~·* (·~* -⊗⊗ ■ ∣n⊗·⊗∣m) ■ ·~* (- ∣n⊗·⊗∣m) ■ ι ··
                    ■ ~·* (·~* (~⊗* ∣^⊗suc ■ -⊗⊗)
                           ■ - (ι ·⊗·) ■ ⊗~* /n·∣⊗ ■ ι ·⊗· ■ ~·* (ι ⊗⊗))
                    ■ -·· ■ ·~* (- (/n+ {n} {l}))
/n·∣⊗ {d = ∩}     = ∣· ■ - (ι ∩∣∣//∣) ■ -··
                    ■ ·~* (~·* (~⊗* (- (ι ⊗ε))) ■ ·~* (~⊗* (- (·∣∣ ■ ι ε⊗))))
/n·∣⊗ {d = ∪}     = ~·* (~·* (~⊗* (ι ⊗ε)) ■ ·~* (~⊗* (·∣∣ ■ ι ε⊗)))
                    ■ ι ∣//∣∣∪ ■ - ·∣
/n·∣⊗ {d = /}     = ~·* (~·* (~⊗* (ι ⊗ε)) ■ ·~* (~⊗* (·∣∣ ■ ι ε⊗))) ■ - (ι ///)
                    ■ -·· ■ ·~* (~·* (~⊗* (- (ι ⊗ε))) ■ ·~* (- (~⊗* (·∣∣ ■ ι ε⊗))))
/n·∣⊗ {d = R}     = ι /nR
/n·∣⊗ {d = M}     = ι /nM

∩n : ∀{n} → D n (n + 2)
∩n {n} = ∣ ^⊗ n ⊗ ∩ · /n ⊗ ∣

∩n·∣⊗∣ : ∀{m n}{d : D m n} → ∩n · ∣ ⊗ d ⊗ ∣ ~* d · ∩n
∩n·∣⊗∣ = -·· ■ ·~* (- (ι ·⊗·) ■ ~⊗* /n·∣⊗ ■ ι ·⊗·)
         ■ ι ·· ■ ~·* (·~* -⊗⊗ ■ - (ι ·⊗·) ■ ~⊗* (ι ∣n·) ■ ⊗~* ·∣∣)
         ■ ~·* (~⊗* (- (ι ·∣n)) ■ - ·⊗∩) ■ -··

∪n : ∀{n} → D (n + 2) n
∪n {n} = ∣ ⊗ /n · ∪ ⊗ ∣ ^⊗ n

∣⊗∣·∪n : ∀{m n}{d : D m n} → ∣ ⊗ d ⊗ ∣ · ∪n ~* ∪n · d
∣⊗∣·∪n = ι ·· ■ ~·* (~·* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* (- /n·∣⊗) ■ ι ·⊗·) ■ -··
         ■ ·~* (~·* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ⊗~* (ι ·∣n) ■ ~⊗* ∣∣· ■ ⊗~* (- (ι ∣n·)) ■ - ∪⊗·) ■ ι ··

