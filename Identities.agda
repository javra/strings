{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity

-·· : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l} → d · e · f ~* d · (e · f)
-·· = - (ι ··)

-⊗⊗ : ∀{m m' n n' k k'}{d : D m m'}{e : D n n'}{f : D k k'} → d ⊗ e ⊗ f ~* d ⊗ (e ⊗ f)
-⊗⊗ = - (ι ⊗⊗)

··⊗·· : ∀{m n k l m' n' k' l'}{d : D m n}{e : D n k}{f : D k l}{d' : D m' n'}{e' : D n' k'}{f' : D k' l'}
        → (d · e · f) ⊗ (d' · e' · f') ~* d ⊗ d' · e ⊗ e' · f ⊗ f'
··⊗·· = ι ·⊗· ■ ~·* (ι ·⊗·)

·⊗∣ : ∀{m n k}{d : D m n}{e : D n k} → (d · e) ⊗ ∣ ~* d ⊗ ∣ · e ⊗ ∣
·⊗∣ = ⊗~* (- ∣·) ■ ι ·⊗·

∪⊗· : ∀{m n k}{d : D m n}{e : D n k} → ∪ ⊗ d · e ~* ∪ ⊗ (d · e)
∪⊗· = - (ι (·~ ε⊗)) ■ - (ι ·⊗·) ■ ι (~⊗ ·ε)

⊗∪· : ∀{m n k}{d : D m n}{e : D n k} → d ⊗ ∪ · e ~* (d · e) ⊗ ∪
⊗∪· = - (ι (·~ ⊗ε)) ■ - (ι ·⊗·) ■ ι (⊗~ ·ε)

·∩⊗ : ∀{m n k}{d : D m n}{e : D n k} → d · ∩ ⊗ e ~* ∩ ⊗ (d · e)
·∩⊗ = - (ι (~· ε⊗)) ■ - (ι ·⊗·) ■ ι (~⊗ ε·)

·⊗∩ : ∀{m n k}{d : D m n}{e : D n k} → d · e ⊗ ∩ ~* (d · e) ⊗ ∩
·⊗∩ = - (ι (~· ⊗ε)) ■ - (ι ·⊗·) ■ ι (⊗~ ε·)

·∪∣·∣∩· : ∀{m n}{d : D m 3}{d' : D 3 n} → d · ∪ ⊗ ∣ · ∣ ⊗ ∩ · d' ~* d ⊗ ∩ · ∪ ⊗ d'
·∪∣·∣∩· = ~·* (·⊗∩ ■ ~⊗* ·∣ ■ ⊗~* (-  ·∣∣) ■ ι ·⊗·)
          ■ -·· ■ ·~* (- (ι (~· ⊗⊗)) ■ ∪⊗· ■ ⊗~* (ι (~· ⊗⊗) ■ ∣∣∣·))

·∪∣∣·∣∣∩· : ∀{m n}{d : D m 4}{d' : D 4 n} → d · ∪ ⊗ ∣ ⊗ ∣ · ∣ ⊗ ∣ ⊗ ∩ · d' ~* d ⊗ ∩ · ∪ ⊗ d'
·∪∣∣·∣∣∩· = ~·* (·⊗∩ ■ ~⊗* ·∣∣ ■ ⊗~* (- ·∣∣) ■ ι ·⊗·) ■ -··
            ■ ·~* (~·* (- ⊗⊗⊗) ■ ∪⊗· ■ ⊗~* (~·* (ι ⊗⊗ ■ ι ⊗⊗) ■ ∣∣∣∣·))

·∪∣∣∣·∣∣∣∩· : ∀{m n}{d : D m 5}{d' : D 5 n} → d · ∪ ⊗ ∣ ⊗ ∣ ⊗ ∣ · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∩ · d' ~* d ⊗ ∩ · ∪ ⊗ d'
·∪∣∣∣·∣∣∣∩· = ~·* (·⊗∩ ■ ~⊗* ·∣∣∣ ■ ⊗~* (- ·∣∣) ■ ι ·⊗·) ■ -··
              ■ ·~* (~·* (- ⊗⊗⊗⊗) ■ ∪⊗·
                     ■ ⊗~* (~·* ⊗⊗⊗⊗ ■ ∣∣∣∣∣·))

∣∣⊗· : ∀{m n}{d : D m 0}{e : D 2 n} → ∣ ⊗ ∣ ⊗ d · e ~* e ⊗ d
∣∣⊗· = ·~* (- (ι ⊗ε)) ■ - (ι ·⊗·) ■ ~⊗* ∣∣· ■ ⊗~* (ι ·ε)

⊗∣∣· : ∀{m n}{d : D m 0}{e : D 2 n} → d ⊗ ∣ ⊗ ∣ · e ~* d ⊗ e
⊗∣∣· = ~·* -⊗⊗ ■ ·~* (- (ι ε⊗)) ■ - (ι ·⊗·) ■ ~⊗* (ι ·ε) ■ ⊗~* ∣∣·

·⊗∣∣ : ∀{m n}{d : D m 2}{e : D 0 n} → d · e ⊗ ∣ ⊗ ∣ ~* e ⊗ d
·⊗∣∣ = ~·* (- (ι ε⊗)) ■ ·~* (- (ι ⊗⊗)) ■ - (ι ·⊗·) ■ ~⊗* (ι ε·) ■ ⊗~* ·∣∣

∣∣∣⊗· : ∀{m n}{d : D m 0}{e : D 3 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ d · e ~* e ⊗ d
∣∣∣⊗· = ·~* (- (ι ⊗ε)) ■ - (ι ·⊗·) ■ ~⊗* ∣∣∣· ■ ⊗~* (ι ·ε)

∣∣⊗·⊗∣∣ : ∀{m n}{d : D m 2}{e : D 2 n} → ∣ ⊗ ∣ ⊗ d · e ⊗ ∣ ⊗ ∣ ~* e ⊗ d
∣∣⊗·⊗∣∣ = ·~* (- (ι ⊗⊗)) ■ - (ι ·⊗·) ■ ~⊗* ∣∣· ■ ⊗~* ·∣∣

∣∣⊗·⊗∣∣∣ : ∀{m n}{d : D m 3}{e : D 2 n} → ∣ ⊗ ∣ ⊗ d · e ⊗ ∣ ⊗ ∣ ⊗ ∣ ~* e ⊗ d
∣∣⊗·⊗∣∣∣ = (·~* (- ⊗⊗⊗)) ■ - (ι ·⊗·) ■ ~⊗* ∣∣· ■ ⊗~* (·~* (ι ⊗⊗) ■ ·∣∣∣)

∣∣∣⊗·⊗∣∣ : ∀{m n}{d : D m 2}{e : D 3 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ d · e ⊗ ∣ ⊗ ∣ ~* e ⊗ d
∣∣∣⊗·⊗∣∣ = ·~* (- (ι ⊗⊗)) ■ - (ι ·⊗·) ■ ~⊗* ∣∣∣· ■ ⊗~* ·∣∣

⊗∣·⊗∣ : ∀{m n k}{d : D m n}{e : D n k} → d ⊗ ∣ · e ⊗ ∣ ~* (d · e) ⊗ ∣
⊗∣·⊗∣ = - (ι ·⊗·) ■ ⊗~* ∣·

∣⊗·∣⊗ : ∀{m n k}{d : D m n}{e : D n k} → ∣ ⊗ d · ∣ ⊗ e ~* ∣ ⊗ (d · e)
∣⊗·∣⊗ = - (ι ·⊗·) ■ ~⊗* ∣·

⊗∣∣·⊗∣∣ : ∀{m n k}{d : D m n}{e : D n k} → d ⊗ ∣ ⊗ ∣ · e ⊗ ∣ ⊗ ∣ ~* (d · e) ⊗ ∣ ⊗ ∣
⊗∣∣·⊗∣∣ = ~·* -⊗⊗ ■ ·~* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* ∣∣· ■ ι ⊗⊗

∣∣⊗·∣∣⊗ : ∀{m n k}{d : D m n}{e : D n k} → ∣ ⊗ ∣ ⊗ d · ∣ ⊗ ∣ ⊗ e ~* ∣ ⊗ ∣ ⊗ (d · e)
∣∣⊗·∣∣⊗ = - (ι ·⊗·) ■ ~⊗* ∣∣·

/⁻¹∣∣/⁻¹ :    /⁻¹ ⊗ ∣
           · ∣ ⊗ /⁻¹  ~* ∣ ⊗ ∣ ⊗ ∣ ⊗   ∩
                       · ∣ ⊗ ∣ ⊗   /   ⊗ ∣
                       · ∣ ⊗   /   ⊗ ∣ ⊗ ∣
                       ·   ∪   ⊗ ∣ ⊗ ∣ ⊗ ∣
/⁻¹∣∣/⁻¹ = ~·* (⊗~* (- (·∣ ■ ·∣)) ■ ··⊗··)
           ■ ·~* (~⊗* (- (·∣ ■ ·∣)) ■ ··⊗·· ■ -·· ■ ~·* (ι ⊗⊗ ■ ~⊗* (ι ⊗⊗)))
           ■ ι ·· ■ ·∪∣∣∣·∣∣∣∩·  ■ ·~* (- ∪⊗·) ■ ~·* (⊗~* (- ·∣∣) ■ ι ·⊗·) ■ -··
           ■ ·~* (ι ·· ■ ~·* (·~* (ι ⊗⊗) ■ ~·* (-⊗⊗ ■ -⊗⊗) ■ - (ι ·⊗·) ■ ⊗~* (~·* ⊗⊗⊗ ■ ∣∣∣∣·)))
           ■ ~·* (-⊗⊗ ■ ~⊗* (- ∣∣·) ■ ⊗~* (- ·∣∣∣) ■ ι ·⊗· ■ ~·* (ι ⊗⊗))
           ■ -··
           ■ ·~* (·~* (~·* (ι ⊗⊗ ■ ~⊗* ((ι ⊗⊗) ■ ~⊗* ·⊗∣) ■ -⊗⊗))
                  ■ ~·* ((ι ⊗⊗) ■ -⊗⊗) ■ ι ·· ■ ~·* (- (ι ·⊗·) ■ ⊗~* ∣∣∣· ■ - ∣∣⊗·⊗∣∣∣ ■ ~·* (ι ⊗⊗))
                  ■ -··
                  ■ ·~* (·~* (ι ⊗⊗ ■ ~⊗* (ι ⊗⊗)) ■ ⊗∣∣·⊗∣∣
                         ■ ~⊗* (~⊗* (~·* (- ⊗∣·⊗∣ ■ ·~* (- ⊗∣·⊗∣)) ■ -··
                                     ■ ·~* (~·* (~·* -⊗⊗ ■ ·~* -⊗⊗) ■ - ··⊗·· ■ ⊗~* (-·· ■ ∣∣· ■ ∣∣·))
                                     ■ ·~* (- ∣∣∣⊗·) ■ ι ··
                                     ■ ~·* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ ∣∣⊗·∣∣⊗ ■ ⊗~* (ι ∩∪)) ■ ∣∣∣· ■ ·∣))
                         ■ - ⊗∣∣·⊗∣∣))
           ■ ι ·· ■ ι ··

//⁻¹ : / · /⁻¹ ~* ∣ ⊗ ∣
//⁻¹ = ι ··
       ■ ~·* (ι ·· ■ ~·* (·⊗∩ ■ ~⊗* ·∣∣ ■ - ∣∣⊗·⊗∣∣)) ■ -·· ■ -··
       ■ ·~* (·~* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* (ι ·· ■ ι /∣∣/∪∣) ■ -⊗⊗)
       ■ ~·* -⊗⊗ ■ ∣⊗·∣⊗ ■ ⊗~* (ι ∪∩)

∩∣∣/∪∣ : ∩ ⊗ ∣ · ∣ ⊗ / · ∪ ⊗ ∣ ~* ∣
∩∣∣/∪∣ = ·~* (~⊗* (- (ι /∪)) ■ - ⊗∣·⊗∣) ■ ι ·· ■ ~·* (ι ∩∣∣//∣) ■ ι ∪∩

∣∩/∣∣∪ : ∣ ⊗ ∩ · / ⊗ ∣ · ∣ ⊗ ∪ ~* ∣
∣∩/∣∣∪ = ~·* (~·* (⊗~* (- (ι ∩/)) ■ - ∣⊗·∣⊗)) ■ -·· ■ -·· ■ ·~* (ι ·· ■ ι ∣//∣∣∪) ■ ι ∪∩

∩/⁻¹ : ∩ · /⁻¹ ~* ∩
∩/⁻¹ = ι ·· ■ ~·* (ι ·· ■ ~·* (·⊗∩ ■ ~⊗* ·∣∣ ■ - ·⊗∣∣))
       ■ -·· ■ -·· ■ ·~* (·~* ⊗∣·⊗∣ ■ ⊗∣·⊗∣ ■ ~⊗* (ι ·· ■ ∩∣∣/∪∣))
       ■ ·∣∣

/⁻¹∪ : /⁻¹ · ∪ ~* ∪
/⁻¹∪ = -·· ■ ·~* (⊗∣∣· ■ - ∣∣⊗·) ■ ι ·· ■ ~·* (~·* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗) ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗)
       ■ ~·* (⊗~* ∣∩/∣∣∪) ■ ∣∣·
