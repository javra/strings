{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding

~·· : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l}{d' : D m k} → d · e ~ d'
      → d · (e · f) ~ d' · f
~·· p = ·· ■ ~· p

-~·· : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l}{d' : D m k} → d · e ~ d'
      → d' · f ~ d · (e · f)
-~·· p = - (~·· p)

··~ : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l}{e' : D n l} → e · f ~ e'
      → (d · e) · f ~ d · e'
··~ p = -·· ■ ·~ p

··⊗·· : ∀{m n k l m' n' k' l'}{d : D m n}{e : D n k}{f : D k l}{d' : D m' n'}{e' : D n' k'}{f' : D k' l'}
        → (d · e · f) ⊗ (d' · e' · f') ~ d ⊗ d' · e ⊗ e' · f ⊗ f'
··⊗·· = ·⊗· ■ ~· ·⊗·

·⊗∣ : ∀{m n k}{d : D m n}{e : D n k} → (d · e) ⊗ ∣ ~ d ⊗ ∣ · e ⊗ ∣
·⊗∣ = ⊗~ (- ∣·) ■ ·⊗·

⊗∣·⊗∣ : ∀{m n k}{d : D m n}{e : D n k} → d ⊗ ∣ · e ⊗ ∣ ~ (d · e) ⊗ ∣
⊗∣·⊗∣ = - ·⊗· ■ ⊗~ ∣·

∣⊗·∣⊗ : ∀{m n k}{d : D m n}{e : D n k} → ∣ ⊗ d · ∣ ⊗ e ~ ∣ ⊗ (d · e)
∣⊗·∣⊗ = - ·⊗· ■ ~⊗ ∣·

⊗∣∣·⊗∣∣ : ∀{m n k}{d : D m n}{e : D n k} → d ⊗ ∣ ⊗ ∣ · e ⊗ ∣ ⊗ ∣ ~ (d · e) ⊗ ∣ ⊗ ∣
⊗∣∣·⊗∣∣ = ~· -⊗⊗ ■ ·~ -⊗⊗ ■ - ·⊗· ■ ⊗~ ∣∣· ■ ⊗⊗

∣∣⊗·∣∣⊗ : ∀{m n k}{d : D m n}{e : D n k} → ∣ ⊗ ∣ ⊗ d · ∣ ⊗ ∣ ⊗ e ~ ∣ ⊗ ∣ ⊗ (d · e)
∣∣⊗·∣∣⊗ = - ·⊗· ■ ~⊗ ∣∣·

∣∣∣⊗·∣∣∣⊗ : ∀{m n k}{d : D m n}{e : D n k} → ∣ ⊗ ∣ ⊗ ∣ ⊗ d · ∣ ⊗ ∣ ⊗ ∣ ⊗ e ~ ∣ ⊗ ∣ ⊗ ∣ ⊗ (d · e)
∣∣∣⊗·∣∣∣⊗ = - ·⊗· ■ ~⊗ ∣∣∣·

∣n⊗·∣n⊗ : ∀{m n k l}{d : D m n}{e : D n k} → ∣ ^⊗ l ⊗ d · ∣ ^⊗ l ⊗ e ~ ∣ ^⊗ l ⊗ (d · e)
∣n⊗·∣n⊗ = - ·⊗· ■ ~⊗ ∣n·

⊗∣n·⊗∣n : ∀{m n k l}{d : D m n}{e : D n k} → d ⊗ ∣ ^⊗ l · e ⊗ ∣ ^⊗ l ~ (d · e) ⊗ ∣ ^⊗ l
⊗∣n·⊗∣n = - ·⊗· ■ ⊗~ ∣n·

∣^⊗suc : ∀{n} → ∣ ^⊗ (suc n) ~ ∣ ^⊗ n ⊗ ∣
∣^⊗suc {zero}  = ⊗ε ■ - ε⊗
∣^⊗suc {suc n} = ⊗~ ∣^⊗suc ■ ⊗⊗

∣^⊗+ : ∀{m n} → ∣ ^⊗ (m + n) ~ ∣ ^⊗ m ⊗ ∣ ^⊗ n
∣^⊗+ {zero}  = - ε⊗
∣^⊗+ {suc m} = ⊗~ ∣^⊗+ ■ ⊗⊗

⊗∩∣⊗·⊗∪⊗ : ∀{m n k m' n' k'}{d : D m n}{e : D (suc n) k}{d' : D m' n'}{e' : D n' k'}
           → d ⊗ ∩ ⊗ ∣ ⊗ d' · e ⊗ ∪ ⊗ e' ~ d ⊗ ∣ ⊗ d' · e ⊗ e'
⊗∩∣⊗·⊗∪⊗ = - ·⊗· ■ ~⊗ (·~ (~⊗ (- ∣n·) ■ - ⊗∪·))
           ■ ~⊗ (~·· (~· -⊗⊗ ■ (·~ (~⊗ ∣^⊗suc ■ -⊗⊗) ■ - ·⊗· ■ ~⊗ ·∣n ■ ⊗~ ∩∪)))
           ■ ·⊗·

⊗∩⊗·⊗∪⊗ : ∀{m n k m' n' k'}{d : D m n}{e : D (suc n) k}{d' : D m' (suc n')}{e' : D n' k'}
           → d ⊗ ∩ ⊗ d' · e ⊗ ∪ ⊗ e' ~ d ⊗ d' · e ⊗ e'
⊗∩⊗·⊗∪⊗ = ~· (- ∣n⊗·⊗∣m) ■ -·· ■ ·~ (~· ⊗⊗ ■ ⊗∩∣⊗·⊗∪⊗) ■ ~·· (·~ -⊗⊗ ■ ∣n⊗·⊗∣m)

/∪ : / · ∪ ~ ∪
/∪ = - ∣∣· ■ ~· (⊗~ (- ∩∪) ■ - ∣⊗·∣⊗) ■ ··~ (~·· (~· ⊗⊗ ■ ⊗∪· ■ ~⊗ ∣∣·))
     ■ ·~ (⊗∪· ■ ⊗~ (- ∣∣·) ■ ·⊗· ■ ·~ (⊗~ (- ∣∣·) ■ - ∪⊗·))
     ■ ·~ (·~ (~· (⊗⊗ ■ ~⊗ (- ∣//∣∣∪) ■ ·⊗∣ ■ ~· ·⊗∣)))
     ■ ·· ■ ·~ (- ···) ■ ~·· (~· (~· ⊗⊗ ■ ·~ ⊗⊗ ■ - ·⊗∣) ■ - ·⊗∣ ■ ~⊗ ∣∩/∣∣/)
     ■ ~·· (~· -⊗⊗ ■ ·~ -⊗⊗ ■ - ·⊗· ■ ~⊗ ∩/ ■ ⊗~ ∣∣·)
     ■ ~·· (~· ⊗⊗ ■ - ·⊗∣ ■ ~⊗ ∩∪) ■ ∣∣·

∪∩ : ∣ ⊗ ∩ · ∪ ⊗ ∣ ~ ∣
∪∩ = ~· (- ∩∣∣//∣) ■ -·· ■ ·~ (- ·⊗· ■ ~⊗ /∪ ■ ⊗~ ∣·) ■ - ·· ■ ~· (~⊗ (- ∩/) ■ ·⊗∣)
     ■ -·· ■ ·~ (·· ■ /∣∣/∪∣) ■ ∩∪

/⁻¹∣∣/⁻¹ :    /⁻¹ ⊗ ∣
           · ∣ ⊗ /⁻¹  ~ ∣ ⊗ ∣ ⊗ ∣ ⊗   ∩
                      · ∣ ⊗ ∣ ⊗   /   ⊗ ∣
                      · ∣ ⊗   /   ⊗ ∣ ⊗ ∣
                      ·   ∪   ⊗ ∣ ⊗ ∣ ⊗ ∣
/⁻¹∣∣/⁻¹ = ~· (⊗~ (- (·∣ ■ ·∣)) ■ ··⊗··)
           ■ ·~ (~⊗ (- (·∣ ■ ·∣)) ■ ··⊗·· ■ - ·· ■ ~· (⊗⊗ ■ ~⊗ ⊗⊗))
           ■ ·· ■ ·∪∣∣∣·∣∣∣∩·  ■ ·~ (- ∪⊗·) ■ ~· (⊗~ (- ·∣∣) ■ ·⊗·) ■ -··
           ■ ·~ (~·· (·~ ⊗⊗ ■ ~· (-⊗⊗ ■ -⊗⊗) ■ - ·⊗· ■ ⊗~ (~· ⊗⊗⊗ ■ ∣∣∣∣·)))
           ■ ~· (-⊗⊗ ■ ~⊗ (- ∣∣·) ■ ⊗~ (- ·∣∣∣) ■ ·⊗· ■ ~· ⊗⊗)
           ■ ··~ (·~ (~· (⊗⊗ ■ ~⊗ (⊗⊗ ■ ~⊗ ·⊗∣) ■ -⊗⊗))
             ■ ~· (⊗⊗ ■ -⊗⊗) ■ ~·· (- ·⊗· ■ ⊗~ ∣∣∣· ■ - ∣∣⊗·⊗∣∣∣ ■ ~· ⊗⊗)
             ■ ··~ (·~ (⊗⊗ ■ ~⊗ ⊗⊗) ■ ⊗∣∣·⊗∣∣
               ■ ~⊗ (~⊗ (~· (- ⊗∣·⊗∣ ■ ·~ (- ⊗∣·⊗∣))
                 ■ ··~ (~· (~· -⊗⊗ ■ ·~ -⊗⊗) ■ - ··⊗·· ■ ⊗~ (-·· ■ ∣∣· ■ ∣∣·))
                 ■ ·~ (- ∣∣∣⊗·) ■ ~·· (~· -⊗⊗ ■ ·~ -⊗⊗ ■ ∣∣⊗·∣∣⊗ ■ ⊗~ ∩∪) ■ ∣∣∣· ■ ·∣))
                         ■ - ⊗∣∣·⊗∣∣))
           ■ ·· ■ ··

∩∣∣/∪∣ : ∩ ⊗ ∣ · ∣ ⊗ / · ∪ ⊗ ∣ ~ ∣
∩∣∣/∪∣ = ·~ (~⊗ (- /∪) ■ - ⊗∣·⊗∣) ■ ~·· (∩∣∣//∣) ■ ∪∩

∣∩/∣∣∪ : ∣ ⊗ ∩ · / ⊗ ∣ · ∣ ⊗ ∪ ~ ∣
∣∩/∣∣∪ = ~· (~· (⊗~ (- (∩/)) ■ - ∣⊗·∣⊗)) ■ -·· ■ ··~ (·· ■ ∣//∣∣∪) ■ ∪∩

∩⊗·∣/⊗·∪⊗ : ∀{m n k l}{d : D m (suc n)}{e : D n k}{f : D (suc k) l}
            → ∩ ⊗ d · ∣ ⊗ / ⊗ e · ∪ ⊗ f ~ d · ∣ ⊗ e · f
∩⊗·∣/⊗·∪⊗ = ~· (~· (- ·∣n ■ ·~ ⊗⊗ ■ - ·⊗· ■ ~⊗ ·∣∣ ■ - ·∩⊗ ■ ·~ ⊗⊗))
            ■ ·~ (- ∣n· ■ ~· ⊗⊗ ■ - ·⊗· ■ ~⊗ ∣∣· ■ - ∪⊗· ■ ~· ⊗⊗)
            ■ ~·· (-·· ■ ··~ (·· ■ - ··⊗·· ■ ~⊗ ∩∣∣/∪∣ ■ ⊗~ (·∣n ■ ∣n·)))

⊗∩·⊗/∣·⊗∪ : ∀{m n k l}{d : D m (suc n)}{e : D n k}{f : D (suc k) l}
            → d ⊗ ∩ · e ⊗ / ⊗ ∣ · f ⊗ ∪ ~ d · e ⊗ ∣ · f
⊗∩·⊗/∣·⊗∪ = ~· (~· (- ·∣n ■ ·~ (∣^⊗suc ■ ~⊗ ∣^⊗suc ■ -⊗⊗) ■ - ·⊗· ■ ⊗~ ·∣∣ ■ - ·⊗∩ ■ ·~ -⊗⊗))
            ■ ·~ (- ∣n· ■ ~· (∣^⊗suc ■ ~⊗ ∣^⊗suc ■ -⊗⊗) ■ - ·⊗· ■ ⊗~ ∣∣· ■ - ⊗∪· ■ ~· -⊗⊗)
            ■ ~·· (-·· ■ -·· ■ ·~ (~·· (~· (⊗⊗ ■ ~⊗ ∣^⊗suc ■ -⊗⊗) ■ ·~ -⊗⊗)
               ■ ·~ (⊗⊗ ■ ~⊗ ∣^⊗suc ■ -⊗⊗) ■ - ··⊗·· ■ ~⊗ (·∣n ■ ∣n·) ■ ⊗~ ∣∩/∣∣∪))

M⁻¹ : D 1 0
M⁻¹ = ∣ ⊗ M · ∪
