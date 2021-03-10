{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Identities

puzzle : D 2 0
puzzle =   ∣ ⊗   ∩   ⊗ ∣
         ·   /   ⊗   /⁻¹
         ·   /   ⊗   /⁻¹
         · ∣ ⊗   R   ⊗ ∣
         ·   ∪   ⊗   ∪
