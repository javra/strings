{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import StrictNat public

infixl 3 _■_
infixl 4 _~_
infixl 4 _~*_
infixl 6 _·_
infixl 10 _⊗_
infixl 11 _^⊗_

data D : ℕ → ℕ → Set where
  ε   : D 0 0
  ∣   : D 1 1
  _·_ : ∀{m n k} → D m n → D n k → D m k
  _⊗_ : ∀{m n k l} → D m n → D k l → D (m + k) (n + l)
  ∩   : D 0 2
  ∪   : D 2 0
  /   : D 2 2        -- line crossing
  R   : ∀{n} → D n n -- the ring
  M   : D 1 1        -- the marble

_^⊗_ : ∀{m n} → D m n → (k : ℕ) → D (k * m) (k * n)
d ^⊗ zero  = ε
d ^⊗ suc k = d ⊗ (d ^⊗ k)

∣n⊗∣m : ∀{m n} → (l : ℕ) → D m n → (r : ℕ) → D (l + m + r) (l + n + r)
∣n⊗∣m l d r = ∣ ^⊗ l ⊗ d ⊗ ∣ ^⊗ r

/n : ∀{n} → D (1 + n) (1 + n)
/n {zero} = ∣
/n {suc n} = ∣ ^⊗ n ⊗ / · /n {n} ⊗ ∣

/⁻¹ : D 2 2 
/⁻¹ =   ∣ ⊗ ∣ ⊗   ∩
      · ∣ ⊗   /   ⊗ ∣
      ·   ∪   ⊗ ∣ ⊗ ∣

data _~_ : ∀ {m n} → D m n → D m n → Prop where
  ⊗ε     : ∀{m n}{d : D m n} → d ⊗ ε ~ d
  ε⊗     : ∀{m n}{d : D m n} → ε ⊗ d ~ d
  ·ε     : ∀{m}{d : D m 0} → d · ε ~ d
  ε·     : ∀{n}{d : D 0 n} → ε · d ~ d
  ··     : ∀{m n k l}{d : D m n}{e : D n k}{f : D k l} → d · (e · f) ~ d · e · f
  ∣n·    : ∀{m n}{d : D m n} → ∣ ^⊗ m · d ~ d
  ·∣n    : ∀{m n}{d : D m n} → d · ∣ ^⊗ n ~ d
  ~·     : ∀{m n k}{d d' : D m n}{e : D n k} → d ~ d' → d · e ~ d' · e
  ·~     : ∀{m n k}{d : D m n}{e e' : D n k} → e ~ e' → d · e ~ d · e'
  ⊗⊗     : ∀{m m' m'' n n' n''}{d : D m n}{e : D m' n'}{f : D m'' n''} → d ⊗ (e ⊗ f) ~ d ⊗ e ⊗ f
  ~⊗     : ∀{m n k l}{d d' : D m n}{e : D k l} → d ~ d' → d ⊗ e ~ d' ⊗ e
  ⊗~     : ∀{m n k l}{d : D m n}{e e' : D k l} → e ~ e' → d ⊗ e ~ d ⊗ e'
  ·⊗·    : ∀{m n k l n' l'}{d : D m n}{e : D k l}{d' : D n n'}{e' : D l l'} → (d · d') ⊗ (e · e') ~ d ⊗ e · d' ⊗ e'
  ∩∪     : (∩ ⊗ ∣) · (∣ ⊗ ∪) ~ ∣
  ∪∩     : (∣ ⊗ ∩) · (∪ ⊗ ∣) ~ ∣
  ∩/     : ∩ · / ~ ∩ -- Reidemeister Type I
  /∪     : / · ∪ ~ ∪ -- Reidemeister Type I
  ∣//∣∣∪ : ∣ ⊗ / · / ⊗ ∣ · ∣ ⊗ ∪ ~ ∪ ⊗ ∣ -- Reidemeister Type II
  /∣∣/∪∣ : / ⊗ ∣ · ∣ ⊗ / · ∪ ⊗ ∣ ~ ∣ ⊗ ∪ -- Reidemeister Type II
  ∩∣∣//∣ : ∩ ⊗ ∣ · ∣ ⊗ / · / ⊗ ∣ ~ ∣ ⊗ ∩ -- Reidemeister Type II
  ∣∩/∣∣/ : ∣ ⊗ ∩ · / ⊗ ∣ · ∣ ⊗ / ~ ∩ ⊗ ∣ -- Reidemeister Type II
  ///    : /⁻¹ ⊗ ∣ · ∣ ⊗ /⁻¹ · / ⊗ ∣ ~ ∣ ⊗ / · /⁻¹ ⊗ ∣ · ∣ ⊗ /⁻¹ -- Reidemeister Type III
  ∩·R    : ∀{l r} → ∣n⊗∣m l ∩ r · R ~ R · ∣n⊗∣m l ∩ r
  ∪·R    : ∀{l r} → ∣n⊗∣m l ∪ r · R ~ R · ∣n⊗∣m l ∪ r
  /·R    : ∀{l r} → ∣n⊗∣m l / r · R ~ R · ∣n⊗∣m l / r
  /nR    : ∀{n} → /n {n} · ∣ ⊗ R ~ R ⊗ ∣ · /n
  M·R    : ∀{l r} → ∣n⊗∣m l M r · R ~ R · ∣n⊗∣m l M r

data _~*_ {m n} : D m n → D m n → Prop where
  ι    : ∀{d d'} → d ~ d' → d ~* d'
  rfl  : ∀{d} → d ~* d
  -    : ∀{d d'} → d ~* d' → d' ~* d
  _■_  : ∀{d e f} → d ~* e → e ~* f → d ~* f

~·* : ∀{m n k}{d d' : D m n}{e : D n k} → d ~* d' → d · e ~* d' · e
~·* (ι p)   = ι (~· p)
~·* rfl     = rfl
~·* (- p)   = - (~·* p)
~·* (p ■ q) = ~·* p ■ ~·* q

·~* : ∀{m n k}{d : D m n}{e e' : D n k} → e ~* e' → d · e ~* d · e'
·~* (ι p)   = ι (·~ p)
·~* rfl     = rfl
·~* (- p)   = - (·~* p)
·~* (p ■ q) = ·~* p ■ ·~* q

~⊗* : ∀{m n k l}{d d' : D m n}{e : D k l} → d ~* d' → d ⊗ e ~* d' ⊗ e
~⊗* (ι p)   = ι (~⊗ p)
~⊗* rfl     = rfl
~⊗* (- p)   = - (~⊗* p)
~⊗* (p ■ q) = ~⊗* p ■ ~⊗* q

⊗~* : ∀{m n k l}{d : D m n}{e e' : D k l} → e ~* e' → d ⊗ e ~* d ⊗ e'
⊗~* (ι p)   = ι (⊗~ p)
⊗~* rfl     = rfl
⊗~* (- p)   = - (⊗~* p)
⊗~* (p ■ q) = ⊗~* p ■ ⊗~* q
