{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities

∩/⁻¹ : ∩ · /⁻¹ ~ ∩
∩/⁻¹ = ~·· (~·· (·⊗∩ ■ ~⊗ ·∣∣ ■ - ·⊗∣∣))
       ■ -·· ■ ··~ (·~ ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗ (·· ■ ∩∣∣/∪∣)) ■ ·∣∣

/⁻¹∪ : /⁻¹ · ∪ ~ ∪
/⁻¹∪ = -·· ■ ·~ (⊗∣∣· ■ - ∣∣⊗·) ■ ~·· (~· (~· -⊗⊗ ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗) ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗)
       ■ ~· (⊗~ ∣∩/∣∣∪) ■ ∣∣·


∣∩∣/⁻¹/∣∪∣ :   ∣ ⊗   ∩   ⊗ ∣
             ·  /⁻¹  ⊗   /
             · ∣ ⊗   ∪   ⊗ ∣ ~ ∪ ⊗ ∩
∣∩∣/⁻¹/∣∪∣ = ~· (·~ (⊗~ (- ·∣∣ ■ - ·∣∣) ■ (·⊗· ■ ~· ·⊗·))) ■ -··
             ■ ·~ (··~ (~· (- ⊗⊗⊗) ■ ∪⊗· ■ ⊗~ (~· ⊗⊗⊗ ■ ∣∣∣∣·)))
             ■ ·~ (··~ (~· (-⊗⊗ ■ ⊗~ ⊗⊗) ■ ·~ (⊗⊗ ■ ~⊗ ⊗⊗ ■  -⊗⊗)
                                   ■ - ·⊗· ■ ⊗~ (∣∣∣· ■ - ·∣) ■ ·⊗·))
             ■ ·~ (~·· (~· (- ∣∣⊗·⊗∣∣) ■ ··~ (·~ ⊗⊗ ■ ⊗∩∣⊗·⊗∪⊗)))
             ■ ·~ (~· (·~ ∣∣∣∣·)) ■ ··
             ■ ~· (~·· (·~ -⊗⊗ ■ ~· -⊗⊗ ■ ∣⊗·∣⊗) ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~ ∩∣∣//∣)
             ■ ~· ⊗⊗ ■ ∣∣⊗·⊗∣∣

∣∩/⁻¹∣ : ∣ ⊗ ∩ · /⁻¹ ⊗ ∣ ~ ∩ ⊗ ∣ · ∣ ⊗ /
∣∩/⁻¹∣ = - ·∣∣∣
         ■ ·~ (~⊗ (⊗~ (- ∪∩)) ■ ~⊗ (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣ ■ ~· (-⊗⊗ ■ ⊗~ (-⊗⊗ ■ ⊗~ (- ∣∩/∣∣/))))
         ■ ·~ (~· (⊗~ (- ∣⊗·∣⊗ ■ ~· (- ∣⊗·∣⊗)) ■ - ∣⊗·∣⊗ ■ ~· (- ∣⊗·∣⊗)))
         ■ ·~ (··~ (~· (⊗⊗ ■ ⊗⊗) ■ ·~ (~⊗ ⊗⊗) ■ ∣∣∣⊗·⊗∣∣) ■ ·~ (- ⊗∣∣·∣⊗)) ■ ··
         ■ ~·· (~· (~·· (··~ (·~ ⊗⊗⊗ ■ ·⊗∩ ■ ~⊗ ·∣∣∣)))
                ■ ~· (~· (·⊗∩ ■ - ∣⊗·⊗∣∣ ■ ·~ (- ⊗∣∣·⊗∣∣)) ■ ··~ (··~ (·~ ⊗⊗⊗ ■ ·~ -⊗⊗ ■ ⊗∣∣∣·∣∣⊗)))
                ■ ··~ (~· (·~ ⊗⊗) ■ ~· ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗ ∣∩∣/⁻¹/∣∪∣ ■ -⊗⊗ ■ - ⊗∣·⊗)
                ■ ~·· ∪∩ ■ ∣·)

//⁻¹ : / · /⁻¹ ~ ∣ ⊗ ∣
//⁻¹ = ··
       ■ ~· (~·· (·⊗∩ ■ ~⊗ ·∣∣ ■ - ∣∣⊗·⊗∣∣)) ■ -··
       ■ ··~ (·~ ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗ (·· ■ /∣∣/∪∣) ■ -⊗⊗)
       ■ ~· -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~ ∪∩

∩∣∣/⁻¹ : ∩ ⊗ ∣ · ∣ ⊗ /⁻¹ ~ ∣ ⊗ ∩ · / ⊗ ∣
∩∣∣/⁻¹ = ~· (- ∣∩/∣∣/) ■ - ··· ■ ·~ (·~ (∣⊗·∣⊗ ■ ⊗~ //⁻¹ ■ ⊗⊗) ■ ·∣∣∣)

/⁻¹/ : /⁻¹ · / ~ ∣ ⊗ ∣
/⁻¹/ = -·· ■ ·~ (⊗∣∣· ■ - ∣∣⊗·⊗∣∣) ■ ··
       ■ ~· (~· (~· -⊗⊗ ■ ·~ -⊗⊗) ■ ·~ -⊗⊗ ■ - ··⊗·· ■ ⊗~ ∣∩/∣∣/ ■ ~⊗ (·∣ ■ ·∣) ■ ⊗⊗)
       ■ ⊗∣·⊗∣ ■ ~⊗ ∪∩

/⁻¹∣∣∪ : /⁻¹ ⊗ ∣ · ∣ ⊗ ∪ ~ ∣ ⊗ / · ∪ ⊗ ∣
/⁻¹∣∣∪ = ·~ (- /∣∣/∪∣) ■ ~·· (~·· (⊗∣·⊗∣ ■ ~⊗ /⁻¹/) ■ ∣∣∣·)

∣∩∣//⁻¹∣∪∣ : ∣ ⊗ ∩ ⊗ ∣ · / ⊗ /⁻¹ · ∣ ⊗ ∪ ⊗ ∣ ~ ∪ ⊗ ∩
∣∩∣//⁻¹∣∪∣ = ~· (·~ (- ∣∣⊗·⊗∣∣) ■ ~·· (~· -⊗⊗ ■ ·~ -⊗⊗ ■ - ·⊗· ■ ⊗~ ∩∣∣/⁻¹ ■ ·⊗· ■ ·~ ⊗⊗ ■ ~· ⊗⊗))
             ■ - ··· ■ ·~ (~·· ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗ ∣//∣∣∪) ■ ∣∣⊗·⊗∣∣

-- another Reidemeister Type II relation
∣∩/⁻¹∣∣/⁻¹ : ∣ ⊗ ∩ · /⁻¹ ⊗ ∣ · ∣ ⊗ /⁻¹ ~ ∩ ⊗ ∣
∣∩/⁻¹∣∣/⁻¹ = ~· (~· (- ∩∣∣//∣) ■ ··~ (⊗∣·⊗∣ ■ ~⊗ //⁻¹) ■ ·∣∣∣)
             ■ ··~ (∣⊗·∣⊗ ■ ⊗~ //⁻¹ ■ ⊗⊗) ■ ·∣∣∣

/n·/n⁻¹ : ∀{n} → /n · /n⁻¹ ~ ∣ ^⊗ (suc n)
/n·/n⁻¹ {zero}  = ·∣ ■ - ⊗ε
/n·/n⁻¹ {suc n} = ~·· (··~ (⊗∣·⊗∣ ■ ~⊗ /n·/n⁻¹ ■ - ∣^⊗suc) ■ ·∣n) ■ ∣n⊗·∣n⊗
                  ■ ⊗~ //⁻¹ ■ ⊗⊗ ■ ~⊗ (- ∣^⊗suc) ■ - ∣^⊗suc

/n⁻¹·/n : ∀{n} → /n⁻¹ · /n ~ ∣ ^⊗ (suc n)
/n⁻¹·/n {zero}  = ·∣ ■ - ⊗ε
/n⁻¹·/n {suc n} = ~·· (··~ (∣n⊗·∣n⊗ ■ ⊗~ /⁻¹/ ■ ⊗⊗ ■ ~⊗ (- ∣^⊗suc) ■ - ∣^⊗suc) ■ ·∣n)
                  ■ ⊗∣·⊗∣ ■ ~⊗ /n⁻¹·/n ■ - ∣^⊗suc

X·X⁻¹ : ∀{n} → X {n} · X⁻¹ ~ ∣ ^⊗ n
X·X⁻¹ {zero}  = ·ε
X·X⁻¹ {suc n} = ~·· (··~ (∣⊗·∣⊗ ■ ⊗~ X·X⁻¹) ■ ·∣n) ■ /n·/n⁻¹

X⁻¹·X : ∀{n} → X⁻¹ {n} · X ~ ∣ ^⊗ n
X⁻¹·X {zero}  = ·ε
X⁻¹·X {suc n} = ~·· (··~ /n⁻¹·/n ■ ·∣n) ■ ∣⊗·∣⊗ ■ ⊗~ X⁻¹·X


