{-# OPTIONS --safe #-}
module Preludes.Relation where

open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)
  public

open import Relation.Nullary.Decidable
  using ( True; toWitness; fromWitness)
  renaming (⌊_⌋ to ⟨_⟩)
  public
  
open import Relation.Binary
  using (Decidable)
  public
  
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong-app)
  renaming (subst to eq-subst)
  public
