{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities
open import InverseBraiding

infix 15 _*

subst₂~ : ∀{m n}{d : D m n}{p : m ≡ m}{q : n ≡ n} → subst₂ D p q d ~* d
subst₂~ {p = refl} {refl} = rfl

_* : ∀{m n} → D m n → D m n
ε *                    = ε
∣ *                    = ∣
(d · e) *              = d * · e *
_⊗_ {m}{n}{k}{l} d e * = subst₂ D (+-comm k m) (+-comm l n) (e * ⊗ d *)
∩ *                    = ∩
∪ *                    = ∪
/ *                    = /⁻¹
R *                    = R
M *                    = M

∣n* : ∀{n} → (∣ ^⊗ n) * ~* ∣ ^⊗ n
∣n* {zero}  = rfl
∣n* {suc n} = subst₂~ ■ ~⊗* (∣n* {n}) ■ - ∣^⊗suc

*~* : ∀{m n}{d e : D m n} → d ~ e → d * ~* e *
*~* ⊗ε = subst₂~ ■ ι ε⊗
*~* ε⊗ = subst₂~ ■ ι ⊗ε
*~* ·ε = ι ·ε
*~* ε· = ι ε·
*~* ·· = ι ··
*~* ∣n· = ~·* ∣n* ■ ι ∣n·
*~* ·∣n = ·~* ∣n* ■ ι ·∣n
*~* (~· p) = ~·* (*~* p)
*~* (·~ p) = ·~* (*~* p)
*~* ⊗⊗ = {!!}
*~* (~⊗ p) = {!!}
*~* (⊗~ p) = {!!}
*~* ·⊗· = {!!}
*~* ∩∪ = ι ∪∩
*~* ∪∩ = ι ∩∪
*~* ∩/ = ∩/⁻¹
*~* /∪ = /⁻¹∪
*~* ∣//∣∣∪ = {!!}
*~* /∣∣/∪∣ = {!!}
*~* ∩∣∣//∣ = {!!}
*~* ∣∩/∣∣/ = {!!}
*~* /// = {!!}
*~* ∩·R = {!!} ■ {!!}
*~* ∪·R = {!!}
*~* /·R = {!!}
*~* /nR = {!!}
*~* /-nR = {!!}
*~* M·R = {!!}
*~* /nM = {!!}
*~* /-nM = {!!}
