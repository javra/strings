{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Identities
open import Bracket
open import Arity
open import Sliding

puzzle : D 2 0
puzzle =         ∩n
         ·   /   ⊗   /⁻¹
         · ∣ ⊗   R   ⊗ ∣
         ·   ∪   ⊗   ∪

solution : puzzle ~* ∪ ⊗ R
solution = - ···
           ■ ~·* (- ∩∣n∩·∪n)
           ■ -··
           ■ ·~* (- ∣⊗∣·∪n)
           ■ {!!}
