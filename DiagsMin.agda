{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import StrictNat public

infixl 3 _■_
infixl 4 _~_
infixl 4 _~*_
infixl 6 _·_
infixl 10 _⊗_
infix  10 ∣⊗_
infix  10 _⊗∣
infixl 11 _^⊗_

data D : ℕ → ℕ → Set where
  ε   : D 0 0
  ∣   : D 1 1
  _·_ : ∀{m n k} → D m n → D n k → D m k
  ∣⊗_ : ∀{m n} → D m n → D (suc m) (suc n)
  _⊗∣ : ∀{m n} → D m n → D (suc m) (suc n)
  ∩   : D 0 2
  ∪   : D 2 0
  /   : D 2 2        -- line crossing
  R   : ∀{n} → D n n -- the ring
  M   : D 1 1        -- the marble

∣n⊗ : ∀{m n} → (k : ℕ) → D m n → D (k + m) (k + n)
∣n⊗ zero    d = d
∣n⊗ (suc k) d = ∣⊗ ∣n⊗ k d

⊗n∣ : ∀{m n} → (k : ℕ) → D m n → D (m + k) (n + k)
⊗n∣ zero    d = d
⊗n∣ (suc k) d = ⊗n∣ k (d ⊗∣)

_⊗_ : ∀{m n k l} → D m n → D k l → D (m + k) (n + l)
_⊗_ {m}{n}{k}{l} d e = ⊗n∣ k d · ∣n⊗ _ e

⊗⊗ : ∀{m m' n n' k k'}(d : D m m')(e : D n n')(f : D k k')
     → (d ⊗ e) ⊗ f ≡ d ⊗ (e ⊗ f)
⊗⊗ d e f = {!!}
