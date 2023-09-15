{-# OPTIONS --safe #-}
module Rome.Entailment.Syntax where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Unit.Polymorphic
open import Data.Product renaming (Σ to Sum)

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax

--------------------------------------------------------------------------------
-- Environments & weakening.

data PEnv : KEnv → Set where
  ε : ∀ {Δ : KEnv } →
        PEnv Δ
  _,_ : ∀ {Δ : KEnv } {κ : Kind } →
          PEnv Δ → Pred Δ κ → PEnv Δ


weakΦ : ∀  {Δ : KEnv } {κ : Kind } →
          PEnv Δ → PEnv (Δ , κ)
weakΦ ε = ε
weakΦ (Φ , π) = weakΦ Φ , renamePred S π

--------------------------------------------------------------------------------
-- Predicate variables.

data PVar : ∀  {Δ : KEnv } {κ : Kind } →
              PEnv Δ → Pred Δ κ → Set where
  Z : ∀  {Δ : KEnv}
        {Φ : PEnv Δ} {κ : Kind } {π : Pred Δ κ} →
        PVar (Φ , π) π
  S : ∀  {Δ : KEnv } {Φ : PEnv Δ}
         {ι : Kind } {κ : Kind }
        {π : Pred Δ ι} {ψ : Pred Δ κ} →
        PVar Φ π → PVar (Φ , ψ) π

--------------------------------------------------------------------------------
-- Entailment in the minimal row theory.

private
  variable
    Δ : KEnv 
    Φ : PEnv Δ
    κ κ₁ κ₂ κ₃ : Kind 
    π : Pred Δ κ

data Ent : (Δ : KEnv ) → PEnv Δ → Pred Δ κ → Set where

  n-var : ∀  {π : Pred Δ κ} →

           PVar Φ π →
           
           Ent Δ Φ π

  n-refl : ∀  {τ : Type Δ R[ κ ]} →

          
          Ent Δ Φ (τ ≲ τ)

  n-trans : ∀  {τ₁ τ₂ τ₃ : Type Δ R[ κ ]} →

          Ent Δ Φ (τ₁ ≲ τ₂) → Ent Δ Φ (τ₂ ≲ τ₃) →
          
          Ent Δ Φ (τ₁ ≲ τ₃)

  n-≡ : ∀ {π₁ π₂ : Pred Δ κ} →
        
        π₁ ≡p π₂ → Ent Δ Φ π₁ →
        
        Ent Δ Φ π₂

  n-≲lift₁ : ∀ {κ¹ : Kind¹ κ}
             {ρ₁ ρ₂ : Type Δ R[ κ¹ `→ κ₂ ]}
             {τ : Type Δ κ} →
  
             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             
             Ent Δ Φ (( ρ₁ ·⌈ τ ⌉) ≲ (ρ₂ ·⌈ τ ⌉))
  
  n-≲lift₂ : ∀  {κ¹ : Kind¹ κ₁}
             {ρ₁ ρ₂ : Type Δ R[ κ₁ ]}
             {τ : Type Δ (κ¹ `→ κ₂)} →
  
             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             
             Ent Δ Φ ((⌈ τ ⌉· ρ₁) ≲ (⌈ τ ⌉· ρ₂))

  n-·lift₁ : ∀ {κ¹ : Kind¹ κ₁}
             {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ¹ `→ κ₂ ]}
             {τ : Type Δ κ₁} →
  
             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             
             Ent Δ Φ ((ρ₁ ·⌈ τ ⌉) · (ρ₂ ·⌈ τ ⌉) ~ (ρ₃ ·⌈ τ ⌉))

  n-·lift₂ : ∀  {κ¹ : Kind¹ κ₁}
             {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ₁ ]}
             {τ : Type Δ (κ¹ `→ κ₂)} →
  
             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             
             Ent Δ Φ ((⌈ τ ⌉· ρ₁) · (⌈ τ ⌉· ρ₂) ~ (⌈ τ ⌉· ρ₃))
          
  n-·≲L : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        
        Ent Δ Φ (ρ₁ ≲ ρ₃)
        

  n-·≲R : ∀  {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        
        Ent Δ Φ (ρ₂ ≲ ρ₃)
