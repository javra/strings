{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Identities
open import Bracket
open import Arity
open import Sliding
open import InverseBraiding
open import BraidingNaturality

2x2B : D 4 4
2x2B = B (replicate 4 1)

2x2B' : D 6 6
2x2B' = B (1 ∷ 1 ∷ 1 ∷ 3 ∷ [])

2x2B∪ : ∀{m}{d : D m 4} → d ⊗ ∪ · 2x2B ~ d ⊗ ∣ ⊗ ∣ · 2x2B' · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∪
2x2B∪ = ~· (- ⊗∣∣·∣n⊗)
        ■ ··~ (- (·~ (~⊗ ⊗ε ■ ⊗⊗ ■ ~⊗ ⊗⊗) ■ ·∣∣∣∣ ■ ~· (⊗⊗ ■ ~⊗ (-⊗⊗ ■ ⊗~ (ε⊗ ■ - ⊗ε ■ - ⊗⊗⊗))))
        ■ (∷B (~· (~· (- ⊗⊗⊗ ■ ~⊗ (- ⊗ε) ■ ⊗~ ⊗⊗)) ■ ·~ (~⊗ (~⊗ (- ⊗ε)) ■ -⊗⊗)
           ■ ∷B (~· (~· (-⊗⊗ ■ ~⊗ (- ⊗ε))) ■ ·~ (~⊗ (- ⊗ε))
             ■ ∷B ((·∣ ■ ~· (~⊗ (- ⊗ε) ■ - ⊗ε))
               ■ ∪[B] ■ ·~ (⊗ε ■ ~⊗ ⊗ε) ■ ~· (- ∣∣∣·))
             ■ ·~ (~⊗ ⊗ε ■ ⊗⊗) ■ ~· (~· (~⊗ ⊗ε ■ ⊗⊗ ■ ~⊗ ⊗⊗)))
           ■ ·~ (~⊗ ⊗ε ■ ⊗⊗ ■ ~⊗ ⊗⊗) ■ ~· (~· (~⊗ ⊗ε ■ ⊗~ (- ⊗⊗⊗) ■ ⊗⊗⊗⊗))))) ■ ··
        ■ ·~ (~⊗ ⊗ε ■ ⊗~ (- ⊗⊗⊗) ■ ⊗⊗⊗⊗)
        ■ ~· (·~ (~· (~⊗ ⊗ε ■ ⊗~ (- ⊗⊗⊗⊗) ■ ⊗⊗⊗⊗⊗) ■ ∣∣∣∣∣∣·))

2x2B'/⁻¹ :  2x2B' · ∣ ⊗ ∣ ⊗ ∣ ⊗ (/⁻¹ ⊗ ∣) ~ ∣ ⊗ ∣ ⊗ ∣ ⊗ (/⁻¹ ⊗ ∣) · 2x2B'
2x2B'/⁻¹ = - (~· (~· (~⊗ ⊗ε) ■ ∣n·) ■ ·~ (~⊗ ⊗ε ■ ⊗⊗ ■ ~⊗ ⊗⊗))
           ■ ∷B (- (·~ (~⊗ ⊗ε ■ ⊗⊗) ■ ~· (~· (~⊗ ⊗ε)))
                ■ ∷B ((- (·~ (~⊗ ⊗ε) ■ ~· (~· (~⊗ ⊗ε))))
                     ■ ∷B (~· ∣n· ■ ·~ (- (⊗~ ⊗ε ■ ~⊗ ε⊗)) ■ - /⁻¹[B]
                       ■ ~· (⊗~ ⊗ε ■ ~⊗ ε⊗) ■ - ·∣n)
                     ■ ·~ (~⊗ ⊗ε) ■ ~· (~· (~⊗ ⊗ε)))
                ■ ·~ (~⊗ ⊗ε) ■ ~· (~· (~⊗ ⊗ε ■ ⊗⊗)))
           ■ ·~ (~⊗ ⊗ε) ■ ·∣n ■ ~· (~⊗ ⊗ε ■ ⊗⊗ ■ ~⊗ ⊗⊗)

M⁻¹∪ : M⁻¹ ⊗ ∪ ~ /⁻¹ ⊗ ∣ · /⁻¹ ⊗ ∣ · M⁻¹ ⊗ ∪
M⁻¹∪ = - (·~ (- ⊗∣∣·) ■ ~·· (··~ (⊗∣·⊗∣ ■ ~⊗ (~· (- (∣∣· ■ ε⊗)) ■ /n⁻¹·⊗∣ ■ ·∣)))
         ■ ~· (⊗∣·⊗∣ ■ ~⊗ (~· (- (∣∣· ■ ⊗ε)) ■ /-n⁻¹·⊗∣ ■ ·∣)) ■ ⊗∣∣·)

puzzle : D 0 0
puzzle =     ∩   ⊗   ∩
         · ∣ ⊗   /   ⊗ ∣
         · ∣ ⊗ ∣ ⊗  /⁻¹
         · ∣ ⊗   R   ⊗ ∣
         ·   /   ⊗ ∣ ⊗ ∣
         · 2x2B
         · M⁻¹ ⊗ ∪ ⊗ M⁻¹

remainder : D _ _
remainder = (∩ ⊗ ε · (∣ ⊗ (∣n⊗∣m 0 ∩ 0 ⊗ ∣) ·
            (/ ⊗ ∣ ⊗ ∣ · (2x2B · (∣ ⊗ ∣ ⊗ ∣ ⊗ M⁻¹ · (∣ ⊗ ∣ ⊗ ∣ · M⁻¹ ⊗ ∪))))))

solution : puzzle ~ remainder ⊗ R{0}
solution = - ···· ■ ~· (~· (·~ (⊗~ (- ∩∪) ■ ~⊗ (- ·∣∣∣) ■ ·⊗·)))
           ■ ~· (~· ·· ■ ··~ (~· ⊗⊗ ■ ⊗∪·))
           ■ ·· ■ ~· (··~ ⊗∪·) ■ ~·· (··~ ⊗∪·) ■ ~·· (··~ 2x2B∪) ■ - ···
           ■ ·~ (·~ (··~ (~· -⊗⊗ ■ - ·⊗· ■ ⊗~ (⊗∪· ■ ~⊗ ∣· ■ M⁻¹∪) ■ - ∣∣∣⊗· ■ ~· (- ∣∣∣⊗·∣∣∣⊗ ■ ~· (- ∣∣∣⊗·∣∣∣⊗)))))
           ■ ···· ■ ~· (~·· (~·· (-·· ■ ·~ (··~ 2x2B'/⁻¹))))
           ■ ~· (~· (··~ (··~ (··~ 2x2B'/⁻¹))))
           ■ ~· (··~ (··~ (··~ (··~ (·~ (⊗⊗ ■ - ∣∣∣∣⊗·) ■ ~·· (~· (- ∣∣∣∣∣∣·) ■ - 2x2B∪))))))
           ■ ~· (···· ■ ~· (~· (~· (·~ (~⊗ (- ⊗∣·⊗∣ ■ ~· (- ⊗∣·⊗∣ ■ ~· (~⊗ ∣∣∣∣·))))) ■ ·~ ⊗⊗ ■ ··~ ⊗∣·⊗∣)))
           ■ ~· (~· (~· (··~ (~· ⊗⊗ ■ ⊗∣·⊗∣ ■ ~⊗ (·~ (··~ (⊗∣∣·∣∣∣⊗ ■ - ∣∣∣⊗·⊗∣∣) ■ ~··
             (··~ (⊗∣∣·∣∣∣⊗ ■ - ∣∣∣⊗·⊗∣∣))) ■ ~·· (~·· (~· (- ·∣∣∣⊗))))))))
           ■ ~· (~· (~· (·~ (~⊗ (~· ·· ■ ~· (~· (- ··· ■ ·~ (·~ (~· -⊗⊗ ■ ·~ -⊗⊗ ■ ∣∣⊗·∣∣⊗) ■ ~· -⊗⊗ ■ ∣∣⊗·∣∣⊗
             ■ ⊗~ (·· ■ ∣∩/⁻¹∣∣/⁻¹)))))))))
           ■ ~· (~·· (~·· (··~ (·~ -⊗⊗ ■ - ·⊗· ■ ⊗~ /⁻¹∣∣∪ ■ ·⊗·))))
           ■ ~· (~· (~· (·~ ∣∣∣⊗·∣∣∣⊗ ■ ~· (·~ (- ⊗∣·⊗∣ ■ ~· (- ⊗∣·⊗∣)) ■ ··) ■ -··)))
           ■ ~· (~· (~· (·~ (⊗∣∣∣·∣∣∣⊗ ■ - ∣∣∣⊗·⊗∣) ■ ~·· (··~ (··~ (⊗∣∣∣·∣∣∣⊗ ■ - ∣∣∣⊗·⊗∣))))))
           ■ ~· (~· (~· (~· (·~ (~· (- ⊗∣·⊗∣) ■ ~·· (·~ (- ∣∣∣⊗·∣∣∣⊗) ■ ~·· (··~ (~· (~⊗ ⊗⊗) ■ ·~ ⊗⊗ ■ ⊗∣∣·∣∣∣∣⊗ ■ - ∣∣⊗·⊗∣∣))))))))
           ■ ~· (~· (~· (~· (·~ (~· (··~ (··~ (·~ (-⊗⊗) ■ ~· (-⊗⊗ ■ -⊗⊗) ■ ∣∣⊗·∣∣⊗ ■ ⊗~ (~· ⊗⊗ ■ ·~ ⊗⊗ ■ ⊗∣·⊗∣ ■ ~⊗ ∩∪) ■ ⊗⊗))))))))
           ■ ~· (~· (~· (~· (~·· (~· (- ·∣∣⊗) ■ ··~ (·~ ·· ■ ~·· (·· ■ ·~ -⊗⊗ ■ ~· (~· -⊗⊗ ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗) ■ ∣⊗·∣⊗ ■ ⊗~ ∣∩/∣∣/)))))))
           ■ ~· (~· (~· (~· (··~ (~· ·∣∣∣∣ ■ ·~ -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~ (⊗∣·⊗∣ ■ ~⊗ (~· (- ε⊗ ■ - ⊗ε) ■ ∩·R{0}{0})))))))
           ■ ~· (~· (~· (~· (·~ (⊗~ (- ⊗∣·⊗∣) ■ - ∣⊗·∣⊗ ■ ~· (⊗~ (- ·∣ ■ - (/nR {0}) ■ ∣·) ■ ⊗⊗))))))
           ■ ~· (~· (~· (~· (~·· (·∣∣⊗ ■ ⊗~ (- ·ε) ■ - ·∩⊗)))))
           ■ -·· ■ -·· ■ -·· ■ -·· ■ -·· ■ - D0n⊗Dm0
