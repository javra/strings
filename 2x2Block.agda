{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Identities
open import Bracket
open import Arity
open import Sliding
open import InverseBraiding

2x2Block : D 4 4
2x2Block = {!!}

puzzle : D 0 0
puzzle =     ∩   ⊗   ∩
         · ∣ ⊗   /   ⊗ ∣
         · ∣ ⊗ ∣ ⊗  /⁻¹
         · ∣ ⊗   R   ⊗ ∣
         ·   /   ⊗ ∣ ⊗ ∣
         · 2x2Block
         · M ⊗   ∪   ⊗ M
