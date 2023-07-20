module PreROmega.Lang.Typing where

open import Data.String using (String; _≟_)
open import Data.Bool
open import Data.List 
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq  

open import Function using (_∘_)

open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

import PreROmega.Lib.Biimplication as Bi
import PreROmega.IndexCalculus

open Bi
  using (_⇔_)
  renaming (Equivalence to E)

open import PreROmega.Lib.AssocList
open import PreROmega.Lang.Syntax

--------------------------------------------------------------------------------
-- Typing and kinding
--------------------------------------------------------------------------------

infix 7 _⊩_
infix 7 _⊢π_

-- We now codify the relations of §4.
data ⊢ₑ     : Env → Set
data _⊢π_     : Env → Pred → Set
data _⊢ₖ_⦂_ : Env → Type → Kind → Set
data _⊢ₜ_⦂_ : Env → Term → Type → Set
data _⊩_ : Env → Pred → Set

--------------------------------------------------------------------------------
-- Environment well-formedness, or
--    ∣ ————— ∣
--    ∣ ⊢ Γ   ∣
--    ∣ ————— ∣

-- An environment Γ is well-formed if each atom is bound at most at once and
-- each bound type (or predicate) is well-defined. Types and predicates are well-defined
-- (WDₜ and WDπ, resp.) when they are locally-closed (LCₜ and LCπ, resp.) with each
-- free variable bound in Γ.

data ⊢ₑ where
  c-emp :
      --------
        ⊢ₑ ε
        
  c-tvar :  ∀ Γ a k →
            ⊢ₑ Γ   → {- I want something here so that I can interpret it... -}   a ∉ dom Γ →
            -------------------------
               ⊢ₑ ((a ⦂ₖ k) ∷ Γ)
                
  c-var : ∀ Γ a t →
          Γ ⊢ₖ t ⦂ ★   →   ⊢ₑ Γ   →   a ∉ dom Γ →
          ------------------------------------------
                      ⊢ₑ ((a ⦂ₜ t) ∷ Γ)
                             
  c-pred : ∀ Γ a p →
           ⊢ₑ Γ   →   Γ ⊢π p   →   a ∉ dom Γ →
           -------------------------------------
                   ⊢ₑ ((a ⦂π p) ∷ Γ)

--------------------------------------------------------------------------------
-- Kinding relation

--    ∣ ——————————— ∣
--    ∣  Γ ⊢ τ : κ  ∣
--    ∣ ——————————— ∣


data _⊢ₖ_⦂_ where
 k-var : ∀ Γ a k →
         ⊢ₑ Γ   →   (a ⦂ₖ k) ∈ Γ →
         ---------------------------
           Γ ⊢ₖ (fvar a) ⦂ k
           
 k-→ : ∀ Γ t₁ t₂ →
        Γ ⊢ₖ t₁ ⦂ ★   →   Γ ⊢ₖ t₂ ⦂ ★ →
        ---------------------------------
                Γ ⊢ₖ t₁ `→ t₂ ⦂ ★
                
 k-⇒ : ∀ Γ p t L →
       Γ ⊢π p   →   cofinite L (λ a → ((a ⦂π p) ∷ Γ) ⊢ₖ (t ^ₜ fvar a) ⦂ ★) →
       -------------------------------------------------------------
                      Γ ⊢ₖ (p ⇒ t) ⦂ ★
                      
 k-∀ : ∀ Γ k t L →
       cofinite L (λ a → ((a ⦂ₖ k) ∷ Γ) ⊢ₖ (t ^ₜ fvar a) ⦂ ★) →
       -------------------------------------------------
                        Γ ⊢ₖ (`∀ k t) ⦂ ★
                        
 k-→I : ∀ Γ k₁ k₂ t L →
       cofinite L (λ a → ((a ⦂ₖ k₁) ∷ Γ) ⊢ₖ (t ^ₜ fvar a) ⦂ k₂) →
       -------------------------------------------------------
                   Γ ⊢ₖ (`λ k₁ t) ⦂ k₁ `→ k₂
                   
 k-→E : ∀ {Γ t t₂ k₁ k₂} →
       Γ ⊢ₖ t ⦂ k₁ `→ k₂   →   Γ ⊢ₖ t₂ ⦂ k₁ →
       ------------------------------------------
                  Γ ⊢ₖ t · t₂ ⦂ k₂       
 k-lab : ∀ Γ l →

       --------------
       Γ ⊢ₖ ℓ l ⦂ L

 k-lty : ∀ Γ t₁ t₂ k →
        Γ ⊢ₖ t₁ ⦂ L   →   Γ ⊢ₖ t₂ ⦂ k → 
       -------------------------------
              Γ ⊢ₖ t₁ ▹ t₂ ⦂ k
 k-sing : ∀ Γ t →
       Γ ⊢ₖ t ⦂ L →
       --------------
       Γ ⊢ₖ ⌊ t ⌋ ⦂ ★

              
 k-row : ∀ Γ t₁ t₂ k →
        Γ ⊢ₖ t₁ ⦂ L   →   Γ ⊢ₖ t₂ ⦂ k → 
       -------------------------------
              Γ ⊢ₖ t₁ ▹ t₂ ⦂ R[ k ]
              
 k-Π : ∀ Γ z k →
       Γ ⊢ₖ z ⦂ R[ k ] →
       ------------------
        Γ ⊢ₖ Π z ⦂ k
        
 k-Σ : ∀ Γ z k →
       Γ ⊢ₖ z ⦂ R[ k ] →
       ------------------
         Γ ⊢ₖ Σ z ⦂ k
         
 k-lift₁ : ∀ {Γ z k₁ k₂ t} →
   Γ ⊢ₖ z ⦂ R[ k₁ `→ k₂ ]   →   Γ ⊢ₖ t ⦂ k₁ →
   ----------------------------------------------
               Γ ⊢ₖ z · t ⦂ R[ k₂ ]
               
 k-lift₂ : ∀ {Γ z k₁ k₂ t} →
   Γ ⊢ₖ z ⦂ R[ k₁ ]   →   Γ ⊢ₖ t ⦂ k₁ `→ k₂ →
   -------------------------------------------
               Γ ⊢ₖ t · z  ⦂ R[ k₂ ]

 k-O : ∀ {Γ} →

       ------------
        Γ ⊢ₖ O ⦂ ★
--------------------------------------------------------------------------------
-- Predicate kinding
--  
--    ∣ —————————— ∣
--    ∣  Γ ⊢ π : o ∣
--    ∣ —————————— ∣
--
data _⊢π_ where
  ⊢π≲ : ∀ Γ t₁ t₂ k →
        Γ ⊢ₖ t₁ ⦂ R[ k ]   →   Γ ⊢ₖ t₂ ⦂ R[ k ] →
        -------------------------------------------
                      Γ ⊢π t₁ ≲ t₂
                      
  ⊢π· : ∀ Γ t₁ t₂ t₃ k →
        Γ ⊢ₖ t₁ ⦂ R[ k ]   →   Γ ⊢ₖ t₂ ⦂ R[ k ] →   Γ ⊢ₖ t₃ ⦂ R[ k ] →
        -----------------------------------------------------------------
                                Γ ⊢π (t₁ · t₂ ~ t₃)

--------------------------------------------------------------------------------
-- Type equivalence
--  
--    ∣ ——————————— ∣
--    ∣   τ₁ ≡ τ₂   ∣
--    ∣ ——————————— ∣
--
data _≡ₜ_ : Type → Type → Set
data _≡π_ : Pred → Pred → Set

infix 5 _≡ₜ_ 
infix 5 _≡π_ 

data _≡ₜ_ where
  ≡ₜrefl  : ∀ t →
  
            ------
            t ≡ₜ t
            
  ≡ₜsym   : ∀ {t₁ t₂} →
            t₁ ≡ₜ t₂ →
            --------
            t₂ ≡ₜ t₁
            
  ≡ₜtrans : ∀ {t₁ t₂ t₃} →
            t₁ ≡ₜ t₂   →   t₂ ≡ₜ t₃ →
            --------------------------
                    t₁ ≡ₜ t₃
                    
  ≡ₜ⇒    : ∀ p₁ p₂ t₁ t₂ →
            p₁ ≡π p₂   →   t₁ ≡ₜ t₂ →
           -----------------------------
             (p₁ ⇒ t₁) ≡ₜ (p₂ ⇒ t₂)
             
  ≡ₜ∀     : ∀ L k t v →
            cofinite L (λ a → (t ^ₜ fvar a) ≡ₜ (v ^ₜ fvar a)) →
            ------------------------------------------
                           `∀ k t ≡ₜ `∀ k v
  ≡ₜβ     : ∀ L k t v →
  
            ---------------
            cofinite L (λ a → (`λ k t) · v ≡ₜ (t ^ₜ v))
            
  ≡ₜ·    : ∀ t₁ t₂ v₁ v₂ →
           t₁ ≡ₜ v₁   →   t₂ ≡ₜ v₂ →
           ---------------------------
             t₁ · t₂ ≡ₜ v₁ · v₂

  ≡ₜ▹    : ∀ t₁ t₂ v₁ v₂ →
          t₁ ≡ₜ v₁   →   t₂ ≡ₜ v₂ →
          -------------------------
           (t₁ ▹ t₂) ≡ₜ (v₁ ▹ v₂)

  ≡ₜ⌊⌋    : ∀ t v →
               t ≡ₜ v →
           -------------
           ⌊ t ⌋ ≡ₜ ⌊ v ⌋
           
           
  ≡ₜlift1 : ∀ t₁ t₂ v →
            --------------------------------
            (t₁ ▹ t₂) · v ≡ₜ (t₁ ▹ (t₂ · v))
            
  ≡ₜlift2 : ∀ t₁ t₂ v →
            ---------------------------------
            v · (t₁ ▹ t₂) ≡ₜ (t₁ ▹ (v · t₂))
  
  ≡ₜΠ    : ∀ z₁ z₂ →
             z₁ ≡ₜ z₂ →
           --------------
            Π z₁ ≡ₜ Π z₂
            
  ≡ₜΣ    : ∀ z₁ z₂ →
             z₁ ≡ₜ z₂ →
           --------------
            Σ z₁ ≡ₜ Σ z₂

  ≡ₜΠ▹   : ∀ t₁ t₂ →

           ----------------------
           Π (t₁ ▹ t₂) ≡ₜ (t₁ ▹ t₂)

  ≡ₜΣ▹   : ∀ t₁ t₂ →

           ----------------------
           Σ (t₁ ▹ t₂) ≡ₜ (t₁ ▹ t₂)

--    ∣ ——————————— ∣
--    ∣   π₁ ≡ π₂   ∣
--    ∣ ——————————— ∣
--

data _≡π_ where
  ≡π≲   :  ∀ t₁ t₂ v₁ v₂ →
           t₁ ≡ₜ v₁   →   t₂ ≡ₜ v₂ →
           ---------------------------
             t₁ ≲ t₂ ≡π v₁ ≲ v₂

  ≡π·   :  ∀ t₁ t₂ t₃ v₁ v₂ v₃ →
           t₁ ≡ₜ v₁   →   t₂ ≡ₜ v₂   →    t₃ ≡ₜ v₃ →
           -------------------------------------------
                  t₁ · t₂ ~ t₃ ≡π v₁ · v₂ ~ v₃


--------------------------------------------------------------------------------
-- Predicate Entailment
--    ∣ ————————— ∣
--    ∣   Γ ⊩ π  ∣
--    ∣ ————————— ∣

data _⊩_ where

  ⊩var : ∀ Γ a p →
         ⊢ₑ Γ   →   (a ⦂π p) ∈ Γ →
         ---------------------------
                  Γ ⊩ p
  ⊩refl : ∀ Γ t →

         -----------------
            Γ ⊩ t ≲ t
            
  ⊩trans : ∀ Γ p₁ p₂ p₃ →
            Γ ⊩ (p₁ ≲ p₂)   →   Γ ⊩ p₂ ≲ p₃ →
            ---------------------------------
                   Γ ⊩ p₁ ≲ p₃

  ⊩≲cong₁ : ∀ Γ p₁ p₂ t →
                  Γ ⊩ p₁ ≲ p₂ →
              -----------------------
              Γ ⊩ (t · p₁) ≲ (t · p₂)
              
  ⊩≲cong₂ : ∀ Γ p₁ p₂ t →
                  Γ ⊩ p₁ ≲ p₂ →
              -----------------------
              Γ ⊩ (p₁ · t) ≲ (p₂ · t)               

  ⊩·cong₁ : ∀ Γ p₁ p₂ p₃ t →
                      Γ ⊩ (p₁ · p₂ ~ p₃) →
               ----------------------------------
               Γ ⊩ ((p₁ · t) · (p₂ · t) ~ (p₃ · t))

  ⊩·cong₂ : ∀ Γ p₁ p₂ p₃ t →
                      Γ ⊩ (p₁ · p₂ ~ p₃) →
               ----------------------------------
               Γ ⊩ ((t · p₁) · (t · p₂) ~ (t · p₃))

  ⊩·≲congL : ∀ Γ p₁ p₂ p₃ →
               Γ ⊩ (p₁ · p₂ ~ p₃) →
               -------------------
                 Γ ⊩ p₁ ≲ p₃

  ⊩·≲congR : ∀ Γ p₁ p₂ p₃ →
               Γ ⊩ (p₁ · p₂ ~ p₃) →
               -------------------
                 Γ ⊩ p₂ ≲ p₃
                 
  ⊩⊔       : ∀ Γ p₁ p₂ p₃ p →
              Γ ⊩ (p₁ · p₂ ~ p₃)   →   Γ ⊩ p₁ ≲ p   →   Γ ⊩ (p₂ ≲ p) →
              ---------------------------------------------------------
                                  Γ ⊩ p₃ ≲ p
              
              

--------------------------------------------------------------------------------
-- Typing Rules
--    ∣ ————————— ∣
--    ∣ Γ ⊢ M ⦂ τ ∣
--    ∣ ————————— ∣
--

-- These are helpers for the (rather large) ana, syn, and fold rules below.
l u y : Type
l = bvar 2
u = bvar 1 
y = bvar 0

∀l⦂L,u⦂_,y⦂R[k] : Kind → Type → Type
∀l⦂L,u⦂ k ,y⦂R[k] t = `∀ L (`∀ k (`∀ R[ k ] t))


data _⊢ₜ_⦂_ where
  t-var : ∀ Γ x t →
          ⊢ₑ Γ   →   (x ⦂ₜ t) ∈ Γ →
          ---------------------------
            Γ ⊢ₜ (fvar x) ⦂ t

  t-sing : ∀ Γ l →
  
          ----------------------
             Γ ⊢ₜ ℓ l ⦂ ⌊ ℓ l ⌋

  t-→I : ∀ Γ M t₁ t₂ L →
       Γ ⊢ₖ t₁ ⦂ ★   →   cofinite L (λ x → ((x ⦂ₜ t₁) ∷ Γ) ⊢ₜ (M ^ fvar x) ⦂ t₂) →
       ----------------------------------------------------------
                  Γ ⊢ₜ (`λ t₁ M) ⦂ (t₁ `→ t₂)
  
  t-→E : ∀ Γ M₁ M₂ t₁ t₂ →
          Γ ⊢ₜ M₁ ⦂ (t₁ `→ t₂)   →   Γ ⊢ₜ M₂ ⦂ t₁ →
          ---------------------------------------
                     Γ ⊢ₜ M₁ · M₂ ⦂ t₂

  t-⇒I : ∀ Γ p M t L →
         Γ ⊢π p   →   cofinite L (λ x → ((x ⦂π p) ∷ Γ) ⊢ₜ (M ^ fvar x) ⦂ (t ^ₜ fvar x)) →
         -----------------------------------------------------------
                   Γ ⊢ₜ M ⦂ (p ⇒ t)

  t-⇒E : ∀ Γ p M t →
         Γ ⊢ₜ M ⦂ (p ⇒ t)   →   Γ ⊩ p →
         ---------------------------------
                Γ ⊢ₜ M ⦂ t

  t-∀I : ∀ Γ M t k L →
         cofinite L (λ x → ((x ⦂ₖ k) ∷ Γ) ⊢ₜ (M ^' fvar x) ⦂ (t ^ₜ fvar x)) →
         -------------------------------------------
                    Γ ⊢ₜ `Λ k M ⦂ (`∀ k t)
  t-∀E : ∀ Γ M t v k →
         Γ ⊢ₜ M ⦂ `∀ k t   →   Γ ⊢ₖ v ⦂ k →
         --------------------------------
             Γ ⊢ₜ (M ·[ v ]) ⦂ (t ^ₜ v)

  t-▹I : ∀ Γ M₁ M₂ t₁ t₂ →
         Γ ⊢ₜ M₁ ⦂ ⌊ t₁ ⌋   →   Γ ⊢ₜ M₂ ⦂ t₂ →
         -----------------------------------
             Γ ⊢ₜ (M₁ ▹ M₂) ⦂ (t₁ ▹ t₂)

  t-▹E : ∀ Γ M₁ M₂ t₁ t₂ →
        Γ ⊢ₜ M₁ ⦂ (t₁ ▹ t₂)   →   Γ ⊢ₜ M₂ ⦂ ⌊ t₁ ⌋ →
        ------------------------------------------
                    Γ ⊢ₜ (M₁ / M₂) ⦂ t₂

  t-ΠE : ∀ Γ M p₁ p₂ →
        Γ ⊢ₜ M ⦂ Π p₁   →   Γ ⊩ p₂ ≲ p₁ →
        ----------------------------------
                Γ ⊢ₜ prj M ⦂ Π p₂
  t-ΠI : ∀ Γ M₁ M₂ p₁ p₂ p₃ →
        Γ ⊢ₜ M₁ ⦂ Π p₁   →   Γ ⊢ₜ M₂ ⦂ Π p₂   →   Γ ⊩ (p₁ · p₂ ~ p₃) → 
        --------------------------------------------------------------
                              Γ ⊢ₜ M₁ ⊹ M₂ ⦂ Π p₃
  t-ΣI : ∀ Γ M p₁ p₂ →
        Γ ⊢ₜ M ⦂ Σ p₁   →   Γ ⊩ p₁ ≲ p₂ →
        ---------------------------------
                Γ ⊢ₜ inj M ⦂ Σ p₂

  t-ΣE : ∀ Γ M₁ M₂ p₁ p₂ p₃ t →
        Γ ⊢ₜ M₁ ⦂ Σ p₁ `→ t   →   Γ ⊢ₜ M₂ ⦂ Σ p₂ `→ t   →   Γ ⊩ (p₁ · p₂ ~ p₃) →
        -------------------------------------------------------------------------
                                    Γ ⊢ₜ M₁ ▿ M₂ ⦂ Σ p₃ `→ t
  t-≡ : ∀ Γ M t v →
         Γ ⊢ₜ M ⦂ t   →   t ≡ₜ v →
         ------------------------
               (Γ ⊢ₜ M ⦂ v)

  t-ana : ∀ Γ M z φ t k →
           Γ ⊢ₖ z ⦂ R[ k ]   →   Γ ⊢ₖ φ ⦂ k `→ ★                                             →
           Γ ⊢ₜ M ⦂ (∀l⦂L,u⦂ k ,y⦂R[k] (((l ▹ u) · y ~ z) ⇒ (⌊ l ⌋ `→ φ · u `→ t)))         → 
          ---------------------------------------------------------------------------------------
                                       Γ ⊢ₜ ana φ M ⦂ (Σ (φ · z) `→ t)
            
  t-syn : ∀ Γ M z φ k →
           Γ ⊢ₖ z ⦂ R[ k ]   →   Γ ⊢ₖ φ ⦂ k `→ ★                                        →
           Γ ⊢ₜ M ⦂ (∀l⦂L,u⦂ k ,y⦂R[k] (((l ▹ u) · y ~ z) ⇒ ⌊ l ⌋ `→ φ · u))             →               
           --------------------------------------------------------------------------------
                                                     Γ ⊢ₜ syn φ M ⦂ Π (φ · z)
  t-fold : ∀ Γ M₁ M₂ M₃ N z t τ k →
          Γ ⊢ₜ M₂ ⦂ τ `→ (τ `→ τ)   →   Γ ⊢ₜ M₃ ⦂ τ   →   Γ ⊢ₜ N ⦂ Π z                  →
          Γ ⊢ₜ M₁ ⦂ (∀l⦂L,u⦂ k ,y⦂R[k] (((l ▹ u) · y ~ z) ⇒ ⌊ l ⌋ `→ t `→ τ))            →
          ---------------------------------------------------------------------------------
                                    Γ ⊢ₜ (fold M₁ M₂ M₃ N) ⦂ τ

  t-o : ∀ {Γ} →

        ----------------
          Γ ⊢ₜ o ⦂ O
  
  
  
