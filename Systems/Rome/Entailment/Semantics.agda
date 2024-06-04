module Rome.Entailment.Semantics where

open import Prelude
open import Preludes.Level
open import Data.Product as DP

open import Rome.Kinds
open import Rome.Types
open import Rome.Equivalence -- extensionality
open import Rome.Terms.Syntax
open import Rome.Entailment.Syntax
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- The meaning of predicate environments.


⟦_⟧pe : PEnv Δ ℓΦ → ⟦ Δ ⟧ke → Potatoes → Set (lsuc ℓΦ)
⟦ ε ⟧pe H n = ⊤
⟦ Φ , π ⟧pe H n = ⟦ Φ ⟧pe H n × ⟦ π ⟧p H n

--------------------------------------------------------------------------------
-- The meaning of predicate variables.

⟦_⟧pv : {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
        PVar Φ π → (H : ⟦ Δ ⟧ke) → (n : Potatoes) →
        ⟦ Φ ⟧pe H n → ⟦ π ⟧p H n
⟦ Z ⟧pv H n (φ , x) = x
⟦ S v ⟧pv H n (φ , x) = ⟦ v ⟧pv H n φ

--------------------------------------------------------------------------------
-- The meaning of entailment in the "Simple Rows" theory.

⟦_⟧n : ∀ {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
         Ent Δ Φ π → (H : ⟦ Δ ⟧ke) → (n : Potatoes) →
         ⟦ Φ ⟧pe H n → ⟦ π ⟧p H n
⟦ n-var x ⟧n H n φ =  ⟦ x ⟧pv H n φ
⟦ n-refl ⟧n H n φ = λ i → i , refl
⟦ n-·≲L π ⟧n H n φ with ⟦ π ⟧n H n φ
... | _ , ρ₁≲ρ₃ , _ = ρ₁≲ρ₃
⟦ n-·≲R π ⟧n H n φ with ⟦ π ⟧n H n φ
... | _ , _ , ρ₁≲ρ₂ = ρ₁≲ρ₂
⟦ n-≲lift₁ π ⟧n H n φ i with ⟦ π ⟧n H n φ i
... | j , eq rewrite eq = j , refl
⟦ n-≲lift₂ π ⟧n H n φ i with ⟦ π ⟧n H n φ i
... | j , eq rewrite eq = j , refl
⟦ n-≡ eq π ⟧n H n φ rewrite sym (⟦ eq ⟧eq-π H n) = ⟦ π ⟧n H n φ
⟦ n-trans t₁≲t₂ t₂≲t₃ ⟧n H n φ i with ⟦ t₁≲t₂ ⟧n H n φ i
... | j , eq with ⟦ t₂≲t₃ ⟧n H n φ j
...   | k , eq' = k , trans eq eq'
⟦ n-·lift₁ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H n φ with ⟦ π ⟧n H n φ
... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = ρ₃τ≲ρ₁τ·ρ₂τ , ρ₁τ≲ρ₃τ , ρ₂τ≲ρ₃τ
  where
    ρ₃τ≲ρ₁τ·ρ₂τ : (i : Fin (fst (⟦ ρ₃ ⟧t H n))) →
                  DP.Σ (Fin (fst (⟦ ρ₁ ⟧t H n)))
                  (λ j → snd (⟦ ρ₁ ⟧t H n) j (⟦ τ ⟧t H n) ≡ snd (⟦ ρ₃ ⟧t H n) i (⟦ τ ⟧t H n))
                  or
                  DP.Σ (Fin (fst (⟦ ρ₂ ⟧t H n)))
                  (λ j → snd (⟦ ρ₂ ⟧t H n) j (⟦ τ ⟧t H n) ≡ snd (⟦ ρ₃ ⟧t H n) i (⟦ τ ⟧t H n))
    ρ₃τ≲ρ₁τ·ρ₂τ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong-app P (⟦ τ ⟧t H n))
    ... | right (j , P) = right (j , cong-app P (⟦ τ ⟧t H n))
    ρ₁τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₁ ⟧t H n))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H n)))
              (λ j → snd (⟦ ρ₁ ⟧t H n) i (⟦ τ ⟧t H n) ≡ snd (⟦ ρ₃ ⟧t H n) j (⟦ τ ⟧t H n))
    ρ₁τ≲ρ₃τ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong-app P (⟦ τ ⟧t H n)

    ρ₂τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₂ ⟧t H n))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H n)))
              (λ j → snd (⟦ ρ₂ ⟧t H n) i (⟦ τ ⟧t H n) ≡ snd (⟦ ρ₃ ⟧t H n) j (⟦ τ ⟧t H n))
    ρ₂τ≲ρ₃τ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong-app P (⟦ τ ⟧t H n)
⟦ n-·lift₂ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H n φ with ⟦ π ⟧n H n φ
... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = τρ₃≲τρ₁·τρ₂ , τρ₁≲τρ₃ , τρ₂τ≲τρ₃
  where
    τρ₃≲τρ₁·τρ₂ : (i : Fin (fst (⟦ ρ₃ ⟧t H n))) →
                  DP.Σ (Fin (fst (⟦ ρ₁ ⟧t H n)))
                  (λ j → (⟦ τ ⟧t H n) (snd (⟦ ρ₁ ⟧t H n) j)  ≡ (⟦ τ ⟧t H n) (snd (⟦ ρ₃ ⟧t H n) i))
                  or
                  DP.Σ (Fin (fst (⟦ ρ₂ ⟧t H n)))
                  (λ j → (⟦ τ ⟧t H n) (snd (⟦ ρ₂ ⟧t H n) j) ≡ (⟦ τ ⟧t H n) (snd (⟦ ρ₃ ⟧t H n) i))
    τρ₃≲τρ₁·τρ₂ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong (⟦ τ ⟧t H n) P)
    ... | right (j , P) = right (j , cong (⟦ τ ⟧t H n) P)
    
    τρ₁≲τρ₃ : (i : Fin (fst (⟦ ρ₁ ⟧t H n))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H n)))
              (λ j → (⟦ τ ⟧t H n) (snd (⟦ ρ₁ ⟧t H n) i) ≡ (⟦ τ ⟧t H n) (snd (⟦ ρ₃ ⟧t H n) j))
    τρ₁≲τρ₃ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong (⟦ τ ⟧t H n) P

    τρ₂τ≲τρ₃ : (i : Fin (fst (⟦ ρ₂ ⟧t H n))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H n)))
              (λ j → (⟦ τ ⟧t H n) (snd (⟦ ρ₂ ⟧t H n) i) ≡ (⟦ τ ⟧t H n) (snd (⟦ ρ₃ ⟧t H n) j))
    τρ₂τ≲τρ₃ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong (⟦ τ ⟧t H n) P
  
  
