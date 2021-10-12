{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import StrictNat public

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (ℕ.suc n)
  succ : ∀{n} → Fin n → Fin (ℕ.suc n)

toNat : ∀{m} → Fin m → ℕ
toNat zero     = 0
toNat (succ p) = toNat p + 1

toNat' : ∀{m} → Fin m → ℕ
toNat' (zero {n}) = n
toNat' (succ p)   = toNat' p

before : ∀{m}(p : Fin m)(n : Fin m → ℕ) → Fin (toNat p) → ℕ
before zero     n ()
before (succ p) n zero     = n (succ p)
before (succ p) n (succ q) = before p (λ r → n (succ r)) q

after : ∀{m}(p : Fin m)(n : Fin m → ℕ) → Fin (toNat' p) → ℕ
after zero     n q = n (succ q)
after (succ p) n q = after p (λ r → n (succ r)) q

sum : ∀{m}(n : Fin m → ℕ) → ℕ
sum {zero}  n = 0
sum {suc m} n = n zero + sum λ x → n (succ x)

sumBefore : ∀{m}(p : Fin m)(n : Fin m → ℕ) → ℕ
sumBefore p n = sum (before p n)

sumAfter : ∀{m}(p : Fin m)(n : Fin m → ℕ) → ℕ
sumAfter p n = sum (after p n)

sumBeforeAfterEq : ∀{m}(p : Fin m)(n : Fin m → ℕ) → sumBefore p n + n p + sumAfter p n ≡ sum n
sumBeforeAfterEq = {!!}
