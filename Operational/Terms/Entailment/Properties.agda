{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Entailment.Properties where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars



--------------------------------------------------------------------------------
-- The sum of two labeled rows is not a labeled row

·-impossible :  ∀ {l₁ l₂ l₃ : NormalType ∅ L} {τ₁ τ₂ τ₃ :  NormalType ∅ κ} → 
                Ent ∅ ((l₁ ▹ τ₁) · (l₂ ▹ τ₂) ~ (l₃ ▹ τ₃)) → ⊥ 
·-impossible  (n-·lift {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} e x x₁ x₂) = ·-impossible e

--------------------------------------------------------------------------------
-- If two rows combine to be the empty type then both are the empty row

ε-sum : Ent ∅ (ρ₁ · ρ₂ ~ ε) → ρ₁ ≡ ε × ρ₂ ≡ ε 
ε-sum n-ε-R = refl , refl
ε-sum n-ε-L = refl , refl
ε-sum (n-·lift {ρ₁ = ne x} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
ε-sum (n-·lift {ρ₁ = ε} {ne x} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
ε-sum (n-·lift {ρ₁ = ε} {ε} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ρ₁-eq , ρ₂-eq
ε-sum (n-·lift {ρ₁ = ε} {l ▹ τ} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
... | () 
ε-sum (n-·lift {ρ₁ = ρ₃ ▹ ρ₅} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
... | ()

--------------------------------------------------------------------------------
-- ε forms a least upper bound on rows

ε-minimum :  Ent ∅ (ρ ≲ ε) → ρ ≡ ε
ε-minimum (n-var ())
ε-minimum n-refl = refl
ε-minimum (n-trans e e₁) rewrite ε-minimum e₁ = ε-minimum e 
ε-minimum {ρ = ρ} (n-·≲L e) = fst (ε-sum e)
ε-minimum (n-·≲R e) = snd (ε-sum e)
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ne x₁} {ε} {F} e x y) = ⊥-elim (noNeutrals x₁) 
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ε} {ε} {F} e x y) = x
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = l ▹ τ} {ε} {f} e x y) with ε-minimum e
... | () 


--------------------------------------------------------------------------------
-- ε is the *unique* right identity

ε-right-unique : Ent ∅ (ρ₁ · ρ₂ ~ ρ₁) → ρ₂ ≡ ε
ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-R = refl
ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-L = refl
ε-right-unique {ρ₁ = ne x} {_} (n-·lift e _ _ _) = ⊥-elim (noNeutrals x)
ε-right-unique {ρ₁ = _} {ne x} (n-·lift e _ _ _ ) = ⊥-elim (noNeutrals x)
ε-right-unique {ρ₁ = ε} {ε} (n-·lift e x x₁ x₂) = refl
ε-right-unique {ρ₁ = ε} {l ▹ τ} (n-·lift {ρ₁ = ε} {ρ₂ = l' ▹ τ'} {ε} {F = `λ F} e x x₁ x₂) with ε-right-unique e
... | () 
ε-right-unique {ρ₁ = ρ₁ ▹ ρ₂} {ε} (n-·lift e x x₁ x₂) = refl
ε-right-unique {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ ▹ ρ₃} {l₄ ▹ τ₄} e x x₁ x₂) = ⊥-elim (·-impossible e) 

--------------------------------------------------------------------------------
-- Reflection of combination equality to propositional equality

ε-right-identity : Ent ∅ (ρ₁ · ε ~ ρ₂) → ρ₁ ≡ ρ₂
ε-left-identity : Ent ∅ (ε · ρ₁ ~ ρ₂) → ρ₁ ≡ ρ₂

ε-right-identity n-ε-R = refl
ε-right-identity n-ε-L = refl
ε-right-identity (n-·lift {ρ₁ = ne x₃} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = ε} {ρ₂ = ne x₃} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = ε} {ρ₂ = ε} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = refl
ε-right-identity {ρ₁ = ε} {ρ₂ = ρ₂ ▹ ρ₄} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃ ▹ ρ₅} e x x₁ x₂) with ε-right-identity e
... | () 
ε-right-identity {ρ₁ = ρ₁ ▹ ρ₂} {ne x₃} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = l₁ ▹ τ₁} {ε} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) with trans (ε-right-identity e) (ε-<$>' (sym x₂))
... | () 
ε-right-identity {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ = ε} {l₄ ▹ τ₄} {F} e x x₁ x₂) = 
  trans x (trans (cong₂ _▹_ (inj-▹ₗ (ε-right-identity e)) (cong (F ·'_) (inj-▹ᵣ (ε-right-identity e)))) (sym x₂))


ε-left-identity n-ε-R = refl
ε-left-identity n-ε-L = refl
ε-left-identity (n-·lift {ρ₁ = ε} {ne x₃} {_} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-left-identity (n-·lift {ρ₁ = ε} {_} {ne x₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ε} e x x₁ x₂) = trans x₁ (sym x₂)
ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ρ₃ ▹ ρ₄} e x x₁ x₂) with  ε-left-identity e  
... | () 
ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ε} e x x₁ x₂) with ε-left-identity e
... | ()
ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ρ₄ ▹ ρ₅} {F} e x x₁ x₂) = 
  trans 
    x₁ 
    (trans 
      (cong₂ _▹_ 
        (inj-▹ₗ (ε-left-identity e)) 
        (cong (F ·'_) (inj-▹ᵣ (ε-left-identity e)))) 
      (sym x₂)) 


--------------------------------------------------------------------------------
-- Reflection of labeled row reflexivity to propositional equality

≲-refl :  ∀ {l₁ l₂ : NormalType ∅ L} {τ₁ τ₂ :  NormalType ∅ κ} → Ent ∅ ((l₁ ▹ τ₁) ≲ (l₂ ▹ τ₂)) → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂)
≲-refl (n-var ())
≲-refl n-refl = refl
≲-refl (n-trans {ρ₂ = ne x} e e₁) = ⊥-elim (noNeutrals x) 
≲-refl (n-trans {ρ₂ = ε} e e₁) with ε-minimum e
... | () 
≲-refl (n-trans {ρ₂ = l₂ ▹ τ₂} e e₁) = trans (≲-refl e) (≲-refl e₁)
≲-refl (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
≲-refl (n-·≲L {ρ₂ = ε} e) = ε-right-identity e
≲-refl (n-·≲L {ρ₂ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e)  
≲-refl (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
≲-refl (n-·≲R {ρ₁ = ε} e) = ε-left-identity e
≲-refl (n-·≲R {ρ₁ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e) 
≲-refl (n-≲lift {ρ₁ = l₃ ▹ τ₃} {l₄ ▹ τ₄} {F} e x x₁) = 
  trans 
    x 
    (trans 
      (cong₂ _▹_ 
        (inj-▹ₗ (≲-refl e)) 
        (cong (F ·'_) (inj-▹ᵣ (≲-refl e)))) 
      (sym x₁))     
 