{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities

∩/⁻¹ : ∩ · /⁻¹ ~* ∩
∩/⁻¹ = ι ·· ■ ~·* (ι ·· ■ ~·* (·⊗∩ ■ ~⊗* ·∣∣ ■ - ·⊗∣∣))
       ■ -·· ■ -·· ■ ·~* (·~* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* (ι ·· ■ ∩∣∣/∪∣)) ■ ·∣∣

/⁻¹∪ : /⁻¹ · ∪ ~* ∪
/⁻¹∪ = -·· ■ ·~* (⊗∣∣· ■ - ∣∣⊗·) ■ ι ·· ■ ~·* (~·* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗) ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗)
       ■ ~·* (⊗~* ∣∩/∣∣∪) ■ ∣∣·


∣∩∣/⁻¹/∣∪∣ :   ∣ ⊗   ∩   ⊗ ∣
             ·  /⁻¹  ⊗   /
             · ∣ ⊗   ∪   ⊗ ∣ ~* ∪ ⊗ ∩
∣∩∣/⁻¹/∣∪∣ = ~·* (·~* (⊗~* (- ·∣∣ ■ - ·∣∣) ■ (ι ·⊗· ■ ~·* (ι ·⊗·)))) ■ -··
             ■ ·~* (-·· ■ ·~* (~·* (- ⊗⊗⊗) ■ ∪⊗· ■ ⊗~* (~·* ⊗⊗⊗ ■ ∣∣∣∣·)))
             ■ ·~* (-·· ■ ·~* (~·* (-⊗⊗ ■ ⊗~* (ι ⊗⊗)) ■ ·~* (ι ⊗⊗ ■ ~⊗* (ι ⊗⊗) ■  -⊗⊗)
                                   ■ - (ι ·⊗·) ■ ⊗~* (∣∣∣· ■ - ·∣) ■ ι ·⊗·))
             ■ ·~* (ι ·· ■ ~·* (~·* (- ∣∣⊗·⊗∣∣) ■ -·· ■ ·~* (·~* (ι ⊗⊗) ■ ⊗∩∣⊗·⊗∪⊗)))
             ■ ·~* (~·* (·~* ∣∣∣∣·)) ■ ι ··
             ■ ~·* (ι ·· ■ ~·* (·~* -⊗⊗ ■ ~·* -⊗⊗ ■ ∣⊗·∣⊗) ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~* (ι ∩∣∣//∣))
             ■ ~·* (ι ⊗⊗) ■ ∣∣⊗·⊗∣∣

∣∩/⁻¹∣ : ∣ ⊗ ∩ · /⁻¹ ⊗ ∣ ~* ∩ ⊗ ∣ · ∣ ⊗ /
∣∩/⁻¹∣ = - ·∣∣∣
         ■ ·~* (~⊗* (⊗~* (- (ι ∪∩))) ■ ~⊗* (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣ ■ ~·* (-⊗⊗ ■ ⊗~* (-⊗⊗ ■ ⊗~* (- (ι ∣∩/∣∣/)))))
         ■ ·~* (~·* (⊗~* (- ∣⊗·∣⊗ ■ ~·* (- ∣⊗·∣⊗)) ■ - ∣⊗·∣⊗ ■ ~·* (- ∣⊗·∣⊗)))
         ■ ·~* (-·· ■ ·~* (~·* (ι ⊗⊗ ■ ι ⊗⊗) ■ ·~* (~⊗* (ι ⊗⊗)) ■ ∣∣∣⊗·⊗∣∣) ■ ·~* (- ⊗∣∣·∣⊗)) ■ ι ·· ■ ι ··
         ■ ~·* (~·* (ι ·· ■ ~·* (-·· ■ ·~* (·~* ⊗⊗⊗ ■ ·⊗∩ ■ ~⊗* ·∣∣∣)))
                ■ ~·* (~·* (·⊗∩ ■ - ∣⊗·⊗∣∣ ■ ·~* (- ⊗∣∣·⊗∣∣)) ■ -·· ■ ·~* (-·· ■ ·~* (·~* ⊗⊗⊗ ■ ·~* -⊗⊗ ■ ⊗∣∣∣·∣∣⊗)))
                ■ -·· ■ ·~* (~·* (·~* (ι ⊗⊗)) ■ ~·* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* ∣∩∣/⁻¹/∣∪∣ ■ -⊗⊗ ■ - ⊗∣·⊗)
                ■ ι ·· ■ ~·* (ι ∪∩) ■ ∣·)

//⁻¹ : / · /⁻¹ ~* ∣ ⊗ ∣
//⁻¹ = ι ··
       ■ ~·* (ι ·· ■ ~·* (·⊗∩ ■ ~⊗* ·∣∣ ■ - ∣∣⊗·⊗∣∣)) ■ -·· ■ -··
       ■ ·~* (·~* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* (ι ·· ■ ι /∣∣/∪∣) ■ -⊗⊗)
       ■ ~·* -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~* (ι ∪∩)

∩∣∣/⁻¹ : ∩ ⊗ ∣ · ∣ ⊗ /⁻¹ ~* ∣ ⊗ ∩ · / ⊗ ∣
∩∣∣/⁻¹ = ~·* (- (ι ∣∩/∣∣/)) ■ - ··· ■ ·~* (·~* (∣⊗·∣⊗ ■ ⊗~* //⁻¹ ■ ι ⊗⊗) ■ ·∣∣∣)

/⁻¹/ : /⁻¹ · / ~* ∣ ⊗ ∣
/⁻¹/ = -·· ■ ·~* (⊗∣∣· ■ - ∣∣⊗·⊗∣∣) ■ ι ··
       ■ ~·* (~·* (~·* -⊗⊗ ■ ·~* -⊗⊗) ■ ·~* -⊗⊗ ■ - ··⊗·· ■ ⊗~* (ι ∣∩/∣∣/) ■ ~⊗* (·∣ ■ ·∣) ■ ι ⊗⊗)
       ■ ⊗∣·⊗∣ ■ ~⊗* (ι ∪∩)

∣∩∣//⁻¹∣∪∣ : ∣ ⊗ ∩ ⊗ ∣ · / ⊗ /⁻¹ · ∣ ⊗ ∪ ⊗ ∣ ~* ∪ ⊗ ∩
∣∩∣//⁻¹∣∪∣ = ~·* (·~* (- ∣∣⊗·⊗∣∣) ■ ι ·· ■ ~·* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* ∩∣∣/⁻¹ ■ ι ·⊗· ■ ·~* (ι ⊗⊗) ■ ~·* (ι ⊗⊗)))
             ■ - ··· ■ ·~* (ι ·· ■ ~·* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* (ι ∣//∣∣∪)) ■ ∣∣⊗·⊗∣∣
             
