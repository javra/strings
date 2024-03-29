{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags

⊗⊗⊗ : ∀{m m' n n' k k' l l'}{d : D m m'}{e : D n n'}{f : D k k'}{g : D l l'}
      → d ⊗ (e ⊗ (f ⊗ g)) ~ d ⊗ e ⊗ f ⊗ g
⊗⊗⊗ = ⊗⊗ ■ ⊗⊗

⊗⊗⊗⊗ : ∀{j j' k k' l l' m m' n n'}{d : D j j'}{e : D k k'}{f : D l l'}{g : D m m'}{h : D n n'}
       → d ⊗ (e ⊗ (f ⊗ (g ⊗ h))) ~ d ⊗ e ⊗ f ⊗ g ⊗ h
⊗⊗⊗⊗ = ⊗⊗ ■ ⊗⊗ ■ ⊗⊗

⊗⊗⊗⊗⊗ : ∀{j j' k k' l l' m m' n n' o o'}{d : D j j'}{e : D k k'}{f : D l l'}{g : D m m'}{h : D n n'}{i : D o o'}
       → d ⊗ (e ⊗ (f ⊗ (g ⊗ (h ⊗ i)))) ~ d ⊗ e ⊗ f ⊗ g ⊗ h ⊗ i
⊗⊗⊗⊗⊗ = ⊗⊗ ■ ⊗⊗ ■ ⊗⊗ ■ ⊗⊗

··· : ∀{m n k l j}{d : D m n}{e : D n k}{f : D k l}{g : D l j}
      → d · (e · (f · g)) ~ d · e · f · g
··· = ·· ■ ··

···· : ∀{m n k l j i}{d : D m n}{e : D n k}{f : D k l}{g : D l j}{h : D j i}
      → d · (e · (f · (g · h))) ~ d · e · f · g · h
···· = ·· ■ ·· ■ ··

∣· : ∀{n}{d : D 1 n} → ∣ · d ~ d
∣· = ~· (- ⊗ε) ■ ∣n·

·∣ : ∀{n}{d : D n 1} → d · ∣  ~ d
·∣ = - (·~ ⊗ε) ■ ·∣n

∣∣· : ∀{n}{d : D 2 n} → ∣ ⊗ ∣ · d ~ d
∣∣· = - (~· (⊗⊗ ■ ⊗ε)) ■ ∣n·

·∣∣ : ∀{n}{d : D n 2} → d · ∣ ⊗ ∣ ~ d
·∣∣ = - (·~ (⊗⊗ ■ ⊗ε)) ■ ·∣n

∣∣∣· : ∀{n}{d : D 3 n} → ∣ ⊗ ∣ ⊗ ∣ · d ~ d
∣∣∣· = ~· (- (⊗⊗ ■ (⊗~ ⊗ε))) ■ ∣n·

·∣∣∣ : ∀{n}{d : D n 3} → d · ∣ ⊗ ∣ ⊗ ∣ ~ d
·∣∣∣ = ·~ (- (⊗~ ⊗ε) ■ - ⊗⊗) ■ ·∣n

∣∣∣∣· : ∀{n}{d : D 4 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ · d ~ d
∣∣∣∣· = ~· (- ⊗⊗⊗  ■ - (⊗~ (⊗~ (⊗~ ⊗ε)))) ■ ∣n·

·∣∣∣∣ : ∀{n}{d : D n 4} → d · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ~ d
·∣∣∣∣ = ·~ (- (⊗⊗ ■ ⊗⊗ ■ (⊗~ ⊗ε))) ■ ·∣n

∣∣∣∣∣· : ∀{n}{d : D 5 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ · d ~ d
∣∣∣∣∣· = ~· (- (⊗⊗ ■ ⊗⊗ ■ ⊗⊗ ■ (⊗~ ⊗ε))) ■ ∣n· 

·∣∣∣∣∣ : ∀{n}{d : D n 5} → d · ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ~ d
·∣∣∣∣∣ = ·~ (- (⊗⊗ ■ ⊗⊗ ■ ⊗⊗ ■ (⊗~ ⊗ε))) ■ ·∣n

∣∣∣∣∣∣· : ∀{n}{d : D 6 n} → ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ ⊗ ∣ · d ~ d
∣∣∣∣∣∣· = ~· (⊗~ (- ⊗ε) ■ - ⊗⊗⊗⊗⊗) ■ ∣n·
