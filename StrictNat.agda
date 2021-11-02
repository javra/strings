{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality public using (_≡_; refl; cong; cong-app; subst; subst₂; trans) public
open import Data.Nat public
open import Data.Nat.Properties public

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE *-identityʳ #-}
{-# REWRITE *-assoc #-}
{-# REWRITE *-distribʳ-+ #-}
{-# REWRITE +-identityʳ #-}
{-# REWRITE *-zeroʳ #-}
{-# REWRITE +-assoc #-}
{-# REWRITE +-suc #-}


*-suc : ∀{m n : ℕ} → m * (suc n) ≡ m * n + m
*-suc {m}{n} = *-distribˡ-+ m n 1

{-# REWRITE *-suc #-}
