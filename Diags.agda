{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import StrictNat public
open import Data.List public
open import Data.List.Properties public

sumRev : (ns : List ℕ) → sum (reverse ns) ≡ sum ns
sumRev [] = refl
sumRev (n ∷ ns) = trans (trans (cong sum (reverse-++-commute [ n ] ns))
                    (trans (sum-++-commute (reverse ns) [ n ]) (+-comm _ n)))
                    (cong (λ m → n + m) (sumRev ns))

infixr 3 _■_
infixl 4 _~_
infixl 6 _·_
infixl 10 _⊗_
infixl 11 _^⊗_

data D : ℕ → ℕ → Set where
  ε   : D 0 0                                          -- empty diagram
  ∣   : D 1 1                                          -- object generator (string)
  _·_ : ∀{m n k} → D m n → D n k → D m k               -- composition
  _⊗_ : ∀{m n k l} → D m n → D k l → D (m + k) (n + l) -- tensor product
  ∩   : D 0 2                                          -- coevaulation
  ∪   : D 2 0                                          -- evaluation
  /   : D 2 2                                          -- braiding
  R   : ∀{n} → D n n                                   -- ring
  M   : D 0 1                                          -- marble
  B   : (ns : List ℕ) → D (sum ns) (sum ns)           -- board

_^⊗_ : ∀{m n} → D m n → (k : ℕ) → D (k * m) (k * n)
d ^⊗ zero  = ε
d ^⊗ suc k = d ⊗ (d ^⊗ k)

∣n⊗∣m : ∀{m n} → (l : ℕ) → D m n → (r : ℕ) → D (l + m + r) (l + n + r)
∣n⊗∣m l d r = ∣ ^⊗ l ⊗ d ⊗ ∣ ^⊗ r

-- braiding c_{1,n}
/n : ∀{n} → D (1 + n) (1 + n)
/n {zero}  = ∣
/n {suc n} = ∣ ^⊗ n ⊗ / · /n {n} ⊗ ∣

-- braiding c_{n,1}
/-n : ∀{n} → D (1 + n) (1 + n)
/-n {zero}  = ∣
/-n {suc n} = / ⊗ ∣ ^⊗ n · ∣ ⊗ /-n

-- braiding c_{m,n}
/mn : ∀{m n} → D (m + n) (n + m)
/mn {m} {zero}  = ∣ ^⊗ m
/mn {m} {suc n} = /n {m} ⊗ ∣ ^⊗ n · ∣ ⊗ /mn {m}{n}

-- half-twist h_n
X : ∀{m} → D m m
X {zero}  = ε
X {suc m} = /n · ∣ ⊗ X


-- inverse of c_{1,1}
/⁻¹ : D 2 2 
/⁻¹ =   ∣ ⊗ ∣ ⊗   ∩
      · ∣ ⊗   /   ⊗ ∣
      ·   ∪   ⊗ ∣ ⊗ ∣

-- inverse of c_{1,n}
/n⁻¹ : ∀{n} → D (1 + n) (1 + n)
/n⁻¹ {zero}  = ∣
/n⁻¹ {suc n} = /n⁻¹ ⊗ ∣ · ∣ ^⊗ n ⊗ /⁻¹

-- inverse of the half-twist
X⁻¹ : ∀{n} → D n n
X⁻¹ {zero}  = ε
X⁻¹ {suc n} = ∣ ⊗ X⁻¹ · /n⁻¹

coeD : ∀{m m' n n'} → m ≡ m' → n ≡ n' → D m n → D m' n'
coeD refl refl d = d

data _~_ : ∀ {m n} → D m n → D m n → Prop where
  -- reflexive, symmetric, and transitive
  rfl  : ∀{m n}{d : D m n} → d ~ d
  -    : ∀{m n}{d d' : D m n} → d ~ d' → d' ~ d
  _■_  : ∀{m n}{d e f : D m n} → d ~ e → e ~ f → d ~ f
  -- category laws
  ε·     : ∀{n}{d : D 0 n} → ε · d ~ d
  ·ε     : ∀{m}{d : D m 0} → d · ε ~ d
  ∣n·    : ∀{m n}{d : D m n} → ∣ ^⊗ m · d ~ d
  ·∣n    : ∀{m n}{d : D m n} → d · ∣ ^⊗ n ~ d
  ··     : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l} → d · (e · f) ~ d · e · f
  ~·     : ∀{m n k}{d d' : D m n}{e : D n k} → d ~ d' → d · e ~ d' · e
  ·~     : ∀{m n k}{d : D m n}{e e' : D n k} → e ~ e' → d · e ~ d · e'
  -- monoidal category
  ⊗ε     : ∀{m n}{d : D m n} → d ⊗ ε ~ d
  ε⊗     : ∀{m n}{d : D m n} → ε ⊗ d ~ d
  ⊗⊗     : ∀{m m' m'' n n' n''}{d : D m n}{e : D m' n'}{f : D m'' n''}
              → d ⊗ (e ⊗ f) ~ d ⊗ e ⊗ f
  ·⊗·    : ∀{m n k l n' l'}{d : D m n}{e : D k l}{d' : D n n'}{e' : D l l'}
              → (d · d') ⊗ (e · e') ~ d ⊗ e · d' ⊗ e'
  ~⊗     : ∀{m n k l}{d d' : D m n}{e : D k l} → d ~ d' → d ⊗ e ~ d' ⊗ e
  ⊗~     : ∀{m n k l}{d : D m n}{e e' : D k l} → e ~ e' → d ⊗ e ~ d ⊗ e'
  -- rigid category
  ∩∪     : ∩ ⊗ ∣ · ∣ ⊗ ∪ ~ ∣
  -- braiding
  ∩/     : ∩ · / ~ ∩                     -- Reidemeister type I
  ∣//∣∣∪ : ∣ ⊗ / · / ⊗ ∣ · ∣ ⊗ ∪ ~ ∪ ⊗ ∣ -- Reidemeister type II
  /∣∣/∪∣ : / ⊗ ∣ · ∣ ⊗ / · ∪ ⊗ ∣ ~ ∣ ⊗ ∪ -- Reidemeister type II
  ∩∣∣//∣ : ∩ ⊗ ∣ · ∣ ⊗ / · / ⊗ ∣ ~ ∣ ⊗ ∩ -- Reidemeister type II
  ∣∩/∣∣/ : ∣ ⊗ ∩ · / ⊗ ∣ · ∣ ⊗ / ~ ∩ ⊗ ∣ -- Reidemeister type II
  ///    : / ⊗ ∣ · ∣ ⊗ / · / ⊗ ∣ ~ ∣ ⊗ / · / ⊗ ∣ · ∣ ⊗ / -- Reidemeister Type III
  -- rigid components
  ∩·R    : ∀{l r} → ∣n⊗∣m l ∩ r · R ~ R · ∣n⊗∣m l ∩ r -- string moves through ring
  ∪·R    : ∀{l r} → ∣n⊗∣m l ∪ r · R ~ R · ∣n⊗∣m l ∪ r -- string moves through ring
  /·R    : ∀{l r} → ∣n⊗∣m l / r · R ~ R · ∣n⊗∣m l / r -- braiding moves through ring
  /nR    : ∀{n} → /n {n} · ∣ ⊗ R ~ R ⊗ ∣ · /n -- naturality of braiding wrt ring
  /-nR   : ∀{n} → /-n {n} · R ⊗ ∣ ~ ∣ ⊗ R · /-n -- naturality of braiding wrt ring
  M·R    : ∀{l r} → ∣n⊗∣m l M r · R ~ R · ∣n⊗∣m l M r -- marble and ring commute
  /M     : ∣ ⊗ M ~ M ⊗ ∣ · / -- naturality of braiding wrt m
  /-M    : M ⊗ ∣ ~ ∣ ⊗ M · / -- naturality of braiding wrt m
  ∩·B    : ∀{l r} → ∣n⊗∣m l ∩ r · B [ l + r + 2 ] ~ B [ l + r ] · ∣n⊗∣m l ∩ r
  ∪·B    : ∀{l r} → ∣n⊗∣m l ∪ r · B [ l + r ] ~ B [ l + r + 2 ] · ∣n⊗∣m l ∪ r
  ∷B     : ∀{k l p}{ns : List ℕ}{ns' : List ℕ}{d : D k _}{d' : D k _}{e : D _ l}{e' : D _ l}
             → d · B ns · e ~ d' · B ns' · e'
             → ∣ ^⊗ p ⊗ d · B (p ∷ ns) · ∣ ^⊗ p ⊗ e ~ ∣ ^⊗ p ⊗ d' · B (p ∷ ns') · ∣ ^⊗ p ⊗ e'
  XBX⁻¹  : ∀{ns} → let B' = coeD (sumRev ns) (sumRev ns) (B (reverse ns)) in
                   X · B ns · X⁻¹ ~ B' -- coherence of board with half-twist
  /nB    : ∀{ns} → /n · ∣ ⊗ B ns ~ B ns ⊗ ∣ · /n  -- naturality of braiding wrt to board
  /-nB   : ∀{ns} → /-n · B ns ⊗ ∣ ~ ∣ ⊗ B ns · /-n  -- naturality of braiding wrt to board
