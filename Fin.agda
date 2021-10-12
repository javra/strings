{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import StrictNat public

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (suc n)
  succ : ∀{n} → Fin n → Fin (suc n)

inj : ∀{m} → Fin m → Fin (suc m)
inj zero     = zero
inj (succ p) = succ (inj p)

injSucc : ∀{m}{p : Fin m} → inj (succ p) ≡ succ (inj p)
injSucc {p = zero}   = refl
injSucc {p = succ p} = refl

last : ∀{m} → Fin (suc m)
last {zero}  = zero
last {suc m} = succ last

inv : ∀{m} → Fin m → Fin m
inv zero     = last
inv (succ p) = inj (inv p)

invLast : ∀{m} → inv (last {m}) ≡ zero
invLast {zero}  = refl
invLast {suc m} = cong inj invLast

invInj : ∀{m}{p : Fin m} → inv (inj p) ≡ succ (inv p)
invInj {p = zero}   = refl
invInj {p = succ p} = cong inj (invInj {p = p})

invInv : ∀{m}{p : Fin m} → inv (inv p) ≡ p
invInv {p = zero}   = invLast
invInv {p = succ p} = trans (invInj {p = inv p}) (cong succ invInv)

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

mirror : ∀{m}(n : Fin m → ℕ) → Fin m → ℕ
mirror n p = n (inv p)

mirrorMirror : ∀{m}{n : Fin m → ℕ}{p : Fin m} → mirror (mirror n) p ≡ n p
mirrorMirror {n = n} = cong n invInv

sumMirror : ∀{m}{n : Fin m → ℕ} → sum (mirror n) ≡ sum n
sumMirror {zero} = refl
sumMirror {suc m} = {!!}
