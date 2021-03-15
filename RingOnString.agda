{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Identities
open import Bracket
open import Arity
open import Sliding
open import InverseBraiding

puzzle : D 2 0
puzzle =         ∩n
         ·   /   ⊗   /⁻¹
         · ∣ ⊗   R   ⊗ ∣
         ·   ∪   ⊗   ∪

∩-2 : ∩-n {2} ~* ∣ ⊗ ∩ ⊗ ∣ · /⁻¹ ⊗ /
∩-2 = {!!}

R0⊗∣ : R {0} ⊗ ∣ ~* ∣ ⊗ R
R0⊗∣ = {!!}

solution : puzzle ~* ∪ ⊗ R
solution = - ··· ■ ∩n~∩-n' ■ ~·* ∩-2 ■ ι ··
           ■ ~·* (-·· ■ ·~* (- (ι ·⊗·) ■ ~⊗* /⁻¹/ ■ ⊗~* //⁻¹ ■ ι ⊗⊗) ■ ·∣∣∣∣)
           ■ ι ·· ■ ~·* (⊗∣·⊗∣ ■ ~⊗* (∣⊗·∣⊗ ■ ⊗~* (~·* (- (ι ⊗ε ■ ι ε⊗)) ■ ι (∩·R {0} {0}))))
           ■ ~·* (~⊗* (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣ ■ ~·* (-⊗⊗ ■ ⊗~* R0⊗∣ ■ ι ⊗⊗))
           ■ -·· ■ ·~* (~·* (~⊗* (⊗~* (ι ⊗ε ■ ι ε⊗))) ■ ·~* (- (ι ⊗ε)) ■ ⊗∩⊗·⊗∪⊗ {d = ∣}{∪}{∣}{ε} ■ ∣∣·)
           ■ - (ι ·⊗·) ■ ~⊗* ∣∣· ■ ⊗~* (ι ·ε)
