{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Identities

∩n : ∀{n} → D n (n + 2)
∩n {zero}  = ∩
∩n {suc n} = ∣ ⊗ ∩n · / ⊗ ∣ ^⊗ _

∩∩n∣∪ : ∀{m} → ∩ ⊗ ∩n · ∣ ⊗ ∪ ⊗ ∣ ^⊗ (suc m) ~* ∩n
∩∩n∣∪ {zero} = ~·* (- ·⊗∣∣) ■ -·· ■
               ·~* (- (ι ·⊗·) ■ ~⊗* (ι ∩∪) ■ - ∣⊗·∣⊗ ■ ∣∣· ■ ι ⊗⊗ ■ ι ⊗ε)
               ■ ·∣∣
∩∩n∣∪ {suc m} = {!!}

∩∩n : ∀{m n}{d : D m n} → ∩ ⊗ ∩n · ∣ ⊗ ∪ ⊗ d ⊗ ∣ ~* ∩n · ∣ ⊗ d ⊗ ∣
∩∩n {zero} = ~·* (- ·⊗∣∣) ■ -··
             ■ ·~* (·~* -⊗⊗ ■ - (ι ·⊗·) ■ ~⊗* (ι ∩∪))
             ■ ·~* (- ∣⊗·∣⊗ ■ ∣∣· ■ ι ⊗⊗)
∩∩n {suc m} = {!!}

∩n∣m⊗ : ∀{m n k}{d : D m n} → ∩n · ∣ ⊗ ∣ ^⊗ k ⊗ d ⊗ ∣
                              ~* ∩n {k} ⊗ ∩n {m} · ∣ ⊗ ∣ ^⊗ k ⊗ ∪ ⊗ d ⊗ ∣
∩n∣m⊗ {k = zero} = {!!}
∩n∣m⊗ {k = suc k} = {!!}

∩n∣·∣ : ∀{m n}{d : D m n} → ∩n · ∣ ⊗ d ⊗ ∣ ~* d · ∩n
∩n∣·∣ {d = ε}     = ·~* (~⊗* (ι ⊗ε)) ■ ·∣∣ ■ - (ι ε·)
∩n∣·∣ {d = ∣}     = ·∣∣∣ ■ - ∣·
∩n∣·∣ {d = d · e} = ·~* (~⊗* (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣) ■ ι ··
                    ■ ~·* ∩n∣·∣ ■ -·· ■ ·~* ∩n∣·∣ ■ ι ··
∩n∣·∣ {d = d ⊗ e} = ·~* (~⊗* (⊗~* (- ⊗∣n·∣m⊗)) ■ {!!})
                    ■ {!!}
∩n∣·∣ {d = ∩}     = {!!}
∩n∣·∣ {d = ∪}     = {!!}
∩n∣·∣ {d = /}     = {!!}
∩n∣·∣ {d = R}     = {!!}
∩n∣·∣ {d = M}     = {!!}
