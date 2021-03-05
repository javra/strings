{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags

⊗⊗⊗ : ∀{m m' n n' k k' l l'}{d : D m m'}{e : D n n'}{f : D k k'}{g : D l l'}
      → d ⊗ (e ⊗ (f ⊗ g)) ~* d ⊗ e ⊗ f ⊗ g
⊗⊗⊗ = ι ⊗⊗ ■ ι ⊗⊗

⊗⊗⊗⊗ : ∀{j j' k k' l l' m m' n n'}{d : D j j'}{e : D k k'}{f : D l l'}{g : D m m'}{h : D n n'}
       → d ⊗ (e ⊗ (f ⊗ (g ⊗ h))) ~* d ⊗ e ⊗ f ⊗ g ⊗ h
⊗⊗⊗⊗ = ι ⊗⊗ ■ ι ⊗⊗ ■ ι ⊗⊗

∣· : ∀{n}{d : D 1 n} → ∣ · d ~* d
∣· = ~·* (- (ι ⊗ε)) ■ ι ∣n·

·∣ : ∀{n}{d : D n 1} → d · ∣  ~* d
·∣ = - (ι (·~ ⊗ε)) ■ ι ·∣n

∣∣· : ∀{n}{d : D 2 n} → ∣ ⊗ ∣ · d ~* d
∣∣· = - (~·* (ι ⊗⊗ ■ ι ⊗ε))  ■ ι ∣n·

·∣∣ : ∀{n}{d : D n 2} → d · ∣ ⊗ ∣ ~* d
·∣∣ = - (·~* (ι ⊗⊗ ■ ι ⊗ε))  ■ ι ·∣n

∣∣∣· : ∀{n}{d : D 3 n} → ∣ ⊗ ∣ ⊗ ∣ · d ~* d
∣∣∣· = ~·* (- (ι ⊗⊗ ■ ι (⊗~ ⊗ε))) ■ ι ∣n·

·∣∣∣ : ∀{n}{d : D n 3} → d · ∣ ⊗ ∣ ⊗ ∣ ~* d
·∣∣∣ = ·~* (- (ι (⊗~ ⊗ε)) ■ - (ι ⊗⊗)) ■ ι ·∣n

∣∣∣∣· : ∀{n}{d : D 4 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ · d ~* d
∣∣∣∣· = ~·* (- ⊗⊗⊗  ■ - (ι (⊗~ (⊗~ (⊗~ ⊗ε))))) ■ ι ∣n·

·∣∣∣∣ : ∀{n}{d : D n 4} → d · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ~* d
·∣∣∣∣ = ·~* (- (ι ⊗⊗ ■ ι ⊗⊗ ■ ι (⊗~ ⊗ε))) ■ ι ·∣n

∣∣∣∣∣· : ∀{n}{d : D 5 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ · d ~* d
∣∣∣∣∣· = ~·* (- (ι ⊗⊗ ■ ι ⊗⊗ ■ ι ⊗⊗ ■ ι (⊗~ ⊗ε))) ■ ι ∣n· 

·∣∣∣∣∣ : ∀{n}{d : D n 5} → d · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ~* d
·∣∣∣∣∣ = ·~* (- (ι ⊗⊗ ■ ι ⊗⊗ ■ ι ⊗⊗ ■ ι (⊗~ ⊗ε))) ■ ι ·∣n