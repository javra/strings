{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities
open import InverseBraiding

infix 15 _*

record hD (m n : ℕ) : Set where
  field
   m' n' : ℕ
   em : m ≡ m'
   en : n ≡ n'
   d : D m' n'

ed : ∀{m n m' n'}(em : m ≡ m')(en : n ≡ n')(d : D m' n') → hD m n
ed em en d = record { m' = _ ; n' = _ ; em = em ; en = en ; d = d }

subst₂~ : ∀{m n}{d : D m n}{p : m ≡ m}{q : n ≡ n} → subst₂ D p q d ~* d
subst₂~ {p = refl} {refl} = rfl

_* : ∀{m n} → D m n → hD m n
ε * = ed refl refl ε
∣ * = ed refl refl ∣
(d · e) * = ed {!!} {!!} {!!}
(d ⊗ e) * = ed {!!} {!!} (hD.d (e *) ⊗ hD.d (d *))
∩ * = {!!}
∪ * = {!!}
/ * = {!!}
R * = {!!}
M * = {!!}
