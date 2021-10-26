{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities
open import BraidingNaturality

∩n : ∀ n → D 0 (n + n)
∩n zero    = ε
∩n (suc n) = ∩ · ∣ ⊗ ∩n n ⊗ ∣

∪n : ∀ n → D (n + n) 0
∪n zero    = ε
∪n (suc n) = ∣ ⊗ ∪n n ⊗ ∣ · ∪

∩suc : ∀{n} → ∩n (suc n) ~ ∩n n · ∣ ^⊗ n ⊗ ∩ ⊗ ∣ ^⊗ n
∩suc {zero}  = ·~ (~⊗ ⊗ε) ■ ·∣∣ ■ - ε⊗ ■ - ⊗ε ■ - ε·
∩suc {suc n} = ·~ (~⊗ (⊗~ (∩suc ■ ·~ -⊗⊗) ■ - ∣⊗·∣⊗ ■ ·~ ⊗⊗⊗)
               ■ - ⊗∣·⊗∣ ■ ·~ (-⊗⊗ ■ ⊗~ (- ∣^⊗suc))) ■ ··

∪suc : ∀{n} → ∪n (suc n) ~ ∣ ^⊗ n ⊗ ∪ ⊗ ∣ ^⊗ n · ∪n n
∪suc {zero} = ~· (~⊗ ⊗ε) ■ ∣∣· ■ - (·ε ■ ⊗ε ■ ε⊗)
∪suc {suc n} = - (~·· (~· (⊗~ ∣^⊗suc ■ ⊗⊗) ■ ⊗∣·⊗∣ ■ ~⊗
                (~· (- ⊗⊗⊗) ■ ∣⊗·∣⊗ ■ ⊗~ (~· ⊗⊗ ■ - ∪suc))))

∩n∣n∣n∪n : ∀{n} → ∩n n ⊗ ∣ ^⊗ n · ∣ ^⊗ n ⊗ ∪n n ~ ∣ ^⊗ n
∩n∣n∣n∪n {zero}  = ~· ε⊗ ■ ε· ■ ⊗ε
∩n∣n∣n∪n {suc n} = ~· (~⊗ ∩suc ■ - ⊗∣n·⊗∣n) ■ ·~ (- ∣n⊗·∣n⊗)
                   ■ ··~ (~·· (~· (-⊗⊗ ■ ⊗~ (- ∣^⊗+)) ■ ·~ (⊗~ -⊗⊗ ■ ⊗⊗ ■ ~⊗ (- ∣^⊗suc)) ■ ⊗∣n·∣m⊗ ■ - ∣n⊗·⊗∣m))
                   ■ ·~ (··~ (·~ (~⊗ ∣^⊗suc ■ -⊗⊗) ■ ~· -⊗⊗ ■ ∣n⊗·∣n⊗ ■ ⊗~ (~· (⊗~ ⊗ε) ■ ∩∪) ■ - ∣^⊗suc))
                   ■ ·~ (·∣n ■ ⊗⊗) ■ ~· (⊗~ ∣^⊗suc ■ ⊗⊗) ■ ⊗∣·⊗∣ ■ ~⊗ ∩n∣n∣n∪n ■ - ∣^⊗suc

∣n∩n∪n∣n : ∀{n} → ∣ ^⊗ n ⊗ ∩n n · ∪n n ⊗ ∣ ^⊗ n ~ ∣ ^⊗ n
∣n∩n∪n∣n {zero}  = ~· ⊗ε ■ ε· ■ ⊗ε
∣n∩n∪n∣n {suc n} = ~· (⊗~ ∩suc ■ - ∣n⊗·∣n⊗) ■ ·~ (- ⊗∣n·⊗∣n)
                   ■ ~·· (··~ (~· (⊗~ -⊗⊗ ■ ⊗⊗ ■ ~⊗ (- ∣^⊗+)) ■ ·~ -⊗⊗ ■ ∣n⊗·⊗∣m ■ - ⊗∣n·∣m⊗))
                   ■ ··~ (-·· ■ ·~ (·~ ⊗⊗ ■ ~· (~⊗ ⊗ε ■ ⊗⊗) ■ ⊗∣n·⊗∣n ■ ~⊗ ∪∩) ■ ·∣n)
                   ■ ~· -⊗⊗ ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~ ∣n∩n∪n∣n
