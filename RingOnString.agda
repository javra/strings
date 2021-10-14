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

∩-2 : ∩-n {2} ~ ∣ ⊗ ∩ ⊗ ∣ · /⁻¹ ⊗ /
∩-2 = ·~ (- ∣⊗·∣⊗) ■ ·· ■ ~· (~· ⊗⊗ ■ ·~ ⊗⊗ ■ - ·⊗· ■ ~⊗ (- ∣∩/⁻¹∣)
                                  ■ ⊗~ (·~ ⊗ε ■ ~· ⊗ε ■ ∣·) ■ - ⊗∣·⊗∣)
      ■ -·· ■ ·~ (·~ ⊗⊗ ■ ⊗∣∣·∣∣⊗ ■ ⊗~ (·∣∣ ■ ⊗ε))

R0⊗∣ : R {0} ⊗ ∣ ~ ∣ ⊗ R
R0⊗∣ = - ·∣ ■ - (/nR {0}) ■ ∣·

solution : puzzle ~ ∪ ⊗ R
solution = - ··· ■ ∩n~∩-n' ■ ~· ∩-2 ■ ··
           ■ ~· (-·· ■ ·~ (- ·⊗· ■ ~⊗ /⁻¹/ ■ ⊗~ //⁻¹ ■ ⊗⊗) ■ ·∣∣∣∣)
           ■ ·· ■ ~· (⊗∣·⊗∣ ■ ~⊗ (∣⊗·∣⊗ ■ ⊗~ (~· (- (⊗ε ■ ε⊗)) ■ (∩·R {0} {0}))))
           ■ ~· (~⊗ (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣ ■ ~· (-⊗⊗ ■ ⊗~ R0⊗∣ ■ ⊗⊗))
           ■ -·· ■ ·~ (~· (~⊗ (⊗~ (⊗ε ■ ε⊗))) ■ ·~ (- ⊗ε) ■ ⊗∩⊗·⊗∪⊗ {d = ∣}{∪}{∣} ■ ∣∣·)
           ■ - ·⊗· ■ ~⊗ ∣∣· ■ ⊗~ ·ε
