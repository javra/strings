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
∩n {zero}  = ∩
∩n {suc n} = ∣ ⊗ ∩n · / ⊗ ∣ ^⊗ _

∩n⊗ : ∀{m n k l}{d : D m n}{e : D k l} → ∩n · ∣ ⊗ d ⊗ e ⊗ ∣ ~* ∩n {m} ⊗ ∩n {k} · ∣ ⊗ d ⊗ ∪ ⊗ e ⊗ ∣
∩n⊗ {zero}{d = d}{e} = ·~* -⊗⊗ ■ ~·* (- (ι ε⊗))
                       ■ - (⊗∩⊗·⊗∪⊗ {d = ε} {e = ∣ ⊗ d} {d' = ∩n} {e' = e ⊗ ∣})
                       ■ ~·* (~⊗* (ι ε⊗)) ■ ·~* (ι ⊗⊗)
∩n⊗ {suc m}{n}{k}{l} =
              ~·* (·~* (- ∣n⊗·⊗∣m ■ ~·* (~⊗* (⊗~* (ι ⊗ε)) ■ -⊗⊗ ■ ⊗~* (⊗~* ∣^⊗suc ■ ι ⊗⊗ ■ ~⊗* (⊗~* (∣^⊗+ {m}{k}))))) ■ ι ··)
              ■ ~·* (~·* (- (ι ·⊗·) ■ ⊗~* (·~* (~⊗* (ι ⊗⊗)) ■ ∩n⊗) ■ ι ·⊗· ■ ~·* (ι ⊗⊗))) ■ -·· ■ -··
              ■ ·~* (~·* (ι ⊗⊗ ■ ~⊗* (ι ⊗⊗) ■ ~⊗* (~⊗* (ι ⊗⊗)) ■ -⊗⊗) ■ ι ··
                     ■ ~·* (·~* (⊗~* (⊗~* (∣^⊗+ {m} {k})) ■ ⊗⊗⊗)) ■ ·~* -⊗⊗
                     ■ ~·* ({!!} ■ {!!})
                     ■ {!!})
              ■ ι ··
              ■ ~·* (- (ι ·⊗·) ■ ⊗~* (ι ·∣n))

∩n∣·∣ : ∀{m n}{d : D m n} → ∩n · ∣ ⊗ d ⊗ ∣ ~* d · ∩n
∩n∣·∣ = {!!}
