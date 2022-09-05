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
infixl 7 _•_
infixl 10 _⊗_
infixl 10 _⨂_
infixl 11 _^⊗_

data A : ℕ → ℕ → Set where
  / : A 2 2
  ∩ : A 0 2
  ∪ : A 2 0
  R : ∀{n} → A n n
  M : A 0 1
  B : (ns : List ℕ) → A (sum ns) (sum ns)

data C : ℕ → ℕ → Set where
  _>A_<_ : ∀{m n} → (l : ℕ) → (a : A m n) → (r : ℕ) → C (l + m + r) (l + n + r)

data D : ℕ → ℕ → Set where
  ∣n : ∀ {n} → D n n -- unit
  _·_ : ∀{m n k} → (d : D m n) → (c : C n k) → D m k -- composition

ε : D 0 0 -- empty diagram
ε = ∣n {0}

∣ : D 1 1 -- object generator (string)
∣ = ∣n {1}

_>_<_ : ∀{m n} → (l' : ℕ) → D m n → (r' : ℕ) → D (l' + m + r') (l' + n + r') -- padding
l' > ∣n < r'                 = ∣n
l' > (d · (l >A a < r)) < r' = l' > d < r' · (l' + l) >A a < (r + r')

_⊗_ : ∀{m n m' n'} → D m n → C m' n' → D (m + m') (n + n') -- tensor product
_⊗_ {m}{n}{m'}{n'} d (l >A a < r)  = 0 > d < m' · (n + l) >A a < r

_•_ : ∀{m n k} → D m n → D n k → D m k -- \bu, maybe find a bigger symbol
d • ∣n = d
d • (e · c) = (d • e) · c

_⨂_ : ∀{m n k l} → D m n → D k l → D (m + k) (n + l)
_⨂_ {m}{n}{k}{l} d e = 0 > d < k • n > e < 0


_^⊗_ : ∀{m n} → C m n → (k : ℕ) → D (m * k) (n * k)
d ^⊗ zero  = ε
d ^⊗ suc k = d ^⊗ k ⊗ d

/n : ∀{n} → D (1 + n) (1 + n) -- braiding c_{n,1}
/n {zero}  = ∣
/n {suc n} = 1 > (/n {n}) < 0 · 0 >A / < n

/-n : ∀{n} → D (1 + n) (1 + n) -- braiding c_{1,n}
/-n {zero}  = ∣
/-n {suc n} = 0 > (/n {n}) < 1 · n >A / < 0

/mn : ∀ m n → D (m + n) (n + m) -- braiding c_{m,n}
/mn m zero    = ∣n
/mn m (suc n) = (0 > /n < n) • (1 > /mn m n < 0)

X : ∀{m} → D m m -- half-twist h_n
X {zero}  = ε
X {suc m} = /n • (1 > X < 0)

/⁻¹ : D 2 2 -- inverse of c_{1,1}
/⁻¹ = ∣n · 2 >A ∩ < 0 · 1 >A / < 1 · 0 >A ∪ < 2

/n⁻¹ : ∀{n} → D (1 + n) (1 + n) -- inverse of c_{n,1}
/n⁻¹ {zero}  = ∣
/n⁻¹ {suc n} = (0 > /n⁻¹ < 1) • (n > /⁻¹ < 0)

/-n⁻¹ : ∀{n} → D (1 + n) (1 + n) -- inverse of c_{1,n}
/-n⁻¹ {zero}  = ∣
/-n⁻¹ {suc n} = (1 > /-n⁻¹ < 0) • (0 > /⁻¹ < n)

/mn⁻¹ : ∀ m n → D (n + m) (m + n) -- inverse of c_{m,n}
/mn⁻¹ m zero    = ∣n
/mn⁻¹ m (suc n) = (1 > /mn⁻¹ m n < 0) • (0 > /n⁻¹ < n)

X⁻¹ : ∀{n} → D n n -- inverse of the half-twist
X⁻¹ {zero}  = ε
X⁻¹ {suc n} = (1 > X⁻¹ < 0) • /n⁻¹

{-
coeD : ∀{m m' n n'} → m ≡ m' → n ≡ n' → D m n → D m' n'
coeD refl refl d = d
-}

data _~_ : ∀ {m n} → D m n → D m n → Prop where
  -- reflexive, symmetric, and transitive
  rfl  : ∀{m n}{d : D m n} → d ~ d
  -    : ∀{m n}{d d' : D m n} → d ~ d' → d' ~ d
  _■_  : ∀{m n}{d e f : D m n} → d ~ e → e ~ f → d ~ f
  -- congruence
  ~·   : ∀{m n k}{d d' : D m n}{c : C n k} → d ~ d' → d · c ~ d' · c
  -- sliding law
  ↓↑   : ∀{m n m' n' l r i o}{f : D o (l + m + i + m' + r)}{d : A m n}{e : A m' n'}
         → f · l >A d < (i + m' + r) · (l + n + i) >A e < r ~ f · (l + m + i) >A e < r · l >A d < (i + n' + r)
  -- rigid category
  ∩∪     : ∀{l r o}{f : D o (l + r + 1)} → f · l >A ∩ < (r + 1) · (l + 1) >A ∪ < r ~ f
  -- braiding
  ∩/     : ∀{l r o}{f : D o (l + r)} → f · l >A ∩ < r · l >A / < r ~ f · l >A ∩ < r  -- Reidemeister type I
  ∣//∣∣∪ : ∀{l r o}{f : D o (l + r + 3)} → f · (l + 1) >A / < r · l >A / < (r + 1) · (l + 1) >A ∪ < r ~ f · l >A ∪ < (r + 1)  -- Reidemeister type II
  /∣∣/∪∣ : ∀{l r o}{f : D o (l + r + 3)} → f · l >A / < (r + 1) · (l + 1) >A / < r · l >A ∪ < (r + 1) ~ f · (l + 1) >A ∪ < r  -- Reidemeister type II
  ∩∣∣//∣ : ∀{l r o}{f : D o (l + r + 1)} → f · l >A ∩ < (r + 1) · (l + 1) >A / < r · l >A / < (r + 1) ~ f · (l + 1) >A ∩ < r  -- Reidemeister type II
  ∣∩/∣∣/ : ∀{l r o}{f : D o (l + r + 1)} → f · (l + 1) >A ∩ < r · l >A / < (r + 1) · (l + 1) >A / < r ~ f · l >A ∩ < (r + 1)  -- Reidemeister type II
  ///    : ∀{l r o}{f : D o (l + r + 3)} → f · l >A / < (r + 1) · (l + 1) >A / < r · l >A / < (r + 1)
                                         ~ f · (l + 1) >A / < r · l >A / < (r + 1) · (l + 1) >A / < r -- Reidemeister Type III
  -- rigid components
  ∩·R    : ∀{l l' r r' o}{f : D o (l' + l + r + r')} → f · (l' + l) >A ∩ < (r + r') · (l' >A R {l + 2 + r} < r')
                                                     ~ f · (l' >A R {l + r} < r') · ((l' + l) >A ∩ < (r + r')) -- string moves through ring
  ∪·R    : ∀{l l' r r' o}{f : D o (l' + l + 2 + r + r')} → f · (l' + l) >A ∪ < (r + r') · (l' >A R {l + r} < r')
                                                         ~ f · (l' >A R {l + 2 + r} < r') · ((l' + l) >A ∪ < (r + r')) -- string moves through ring
  /·R    : ∀{l l' r r' o}{f : D o (l' + l + 2 + r + r')} → f · (l' + l) >A / < (r + r') · (l' >A R {l + 2 + r} < r')
                                                         ~ f · (l' >A R {l + 2 + r} < r') · ((l' + l) >A / < (r + r')) -- braiding moves through ring
  /nR    : ∀{l r o n}{f : D o (l + 1 + n + r)} → f • (l > /n {n} < r) · (l + 1) >A R {n} < r
                                               ~ (f · (l >A R {n} < (1 + r))) • (l > /n {n} < r) -- naturality of braiding wrt ring
  /-nR   : ∀{l r o n}{f : D o (l + 1 + n + r)} → f • (l > /n {n} < r) · l >A R {n} < (r + 1)
                                               ~ (f · ((l + 1) >A R {n} < r)) • (l > /n {n} < r) -- naturality of braiding wrt ring


{-
TODO model these...
data _~_ : ∀ {m n} → D m n → D m n → Prop where
  -- rigid components
  /-nR   : ∀{n} → /-n {n} · R ⊗ ∣ ~ ∣ ⊗ R · /-n -- naturality of braiding wrt ring
  M·R    : ∀{l r} → ∣n⊗∣m l M r · R ~ R · ∣n⊗∣m l M r -- marble and ring commute
  /M     : ∣ ⊗ M ~ M ⊗ ∣ · / -- naturality of braiding wrt m
  /-M    : M ⊗ ∣ ~ ∣ ⊗ M · / -- naturality of braiding wrt m
  ∩[B]   : ∀{l r} → ∣n⊗∣m l ∩ r · B [ l + r + 2 ] ~ B [ l + r ] · ∣n⊗∣m l ∩ r -- ∩ moves through board
  ∪[B]   : ∀{l r} → ∣n⊗∣m l ∪ r · B [ l + r ] ~ B [ l + r + 2 ] · ∣n⊗∣m l ∪ r -- ∪ moves through board
  /[B]   : ∀{l r} → ∣n⊗∣m l / r · B [ l + r + 2 ] ~ B [ l + r + 2 ] · ∣n⊗∣m l / r -- / moves through board
  ∷B     : ∀{k l p}{ns : List ℕ}{ns' : List ℕ}{d : D k _}{d' : D k _}{e : D _ l}{e' : D _ l}
             → d · B ns · e ~ d' · B ns' · e'
             → ∣ ^⊗ p ⊗ d · B (p ∷ ns) · ∣ ^⊗ p ⊗ e ~ ∣ ^⊗ p ⊗ d' · B (p ∷ ns') · ∣ ^⊗ p ⊗ e'
  XBX⁻¹  : ∀{ns} → let B' = coeD (sumRev ns) (sumRev ns) (B (reverse ns)) in
                   X · B ns · X⁻¹ ~ B' -- coherence of board with half-twist
  /nB    : ∀{ns} → /n · ∣ ⊗ B ns ~ B ns ⊗ ∣ · /n  -- naturality of braiding wrt to board
  /-nB   : ∀{ns} → /-n · B ns ⊗ ∣ ~ ∣ ⊗ B ns · /-n  -- naturality of braiding wrt to board
-}
