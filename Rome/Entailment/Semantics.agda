open import Prelude
open import Preludes.Level
open import Data.Product as DP

module Rome.Entailment.Semantics (g : Potatoes) where

open import IndexCalculus.Properties
import IndexCalculus as Ix

open import Rome.Kinds
open import Rome.Types.Syntax
open import Rome.Types.Semantics g
open import Rome.Equivalence.Syntax 
open import Rome.Equivalence.Semantics g -- extensionality
open import Rome.Terms.Syntax
open import Rome.Entailment.Syntax
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- The meaning of predicate environments.

⟦_⟧pe : PEnv Δ ℓΦ → ⟦ Δ ⟧ke → Set (lsuc ℓΦ)
⟦ ε ⟧pe H = ⊤
⟦ Φ , π ⟧pe H = ⟦ Φ ⟧pe H × ⟦ π ⟧p H

--------------------------------------------------------------------------------
-- The meaning of predicate variables.

⟦_⟧pv : {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
          PVar Φ π → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ π ⟧p H
⟦ Z ⟧pv H (φ , x) = x
⟦ S v ⟧pv H (φ , x) = ⟦ v ⟧pv H φ

--------------------------------------------------------------------------------
-- Meaning of multi-row inclusion.

⟦_⟧∈ : ∀ {l : Label} {τ : Type Δ κ} {m : Row Δ κ} {Φ : PEnv Δ ℓΦ} → 
       (lab {ℓ = ℓ} l R▹ τ) ∈ m → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → 
       (⟦ (lab {ℓ = ℓ} l R▹ τ) ⟧t H) Ix.≲ (⟦ m ⟧Row H)
⟦ end ⟧∈ H φ = λ i → i , refl
⟦ here ⟧∈ H φ = λ { fzero → fzero , refl }
⟦ there ev ⟧∈ H φ fzero with ⟦ ev ⟧∈ H φ fzero
... | i , P = (fsuc i) , P 


--------------------------------------------------------------------------------
-- The meaning of entailment in the "Simple Rows" theory.

⟦_⟧n : ∀ {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
         Ent Δ Φ π → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ π ⟧p H
⟦ n-var x ⟧n H φ =  ⟦ x ⟧pv H φ
⟦ n-refl ⟧n H φ = λ i → i , refl
⟦ n-·≲L π ⟧n H φ with ⟦ π ⟧n H φ
... | _ , ρ₁≲ρ₃ , _ = ρ₁≲ρ₃
⟦ n-·≲R π ⟧n H φ with ⟦ π ⟧n H φ
... | _ , _ , ρ₁≲ρ₂ = ρ₁≲ρ₂
⟦ n-≲lift₁ π ⟧n H φ i with ⟦ π ⟧n H φ i
... | j , eq rewrite eq = j , refl
⟦ n-≲lift₂ π ⟧n H φ i with ⟦ π ⟧n H φ i
... | j , eq rewrite eq = j , refl
⟦ n-≡ eq π ⟧n H φ rewrite sym (⟦ eq ⟧eq-π H) = ⟦ π ⟧n H φ
⟦ n-trans t₁≲t₂ t₂≲t₃ ⟧n H φ i with ⟦ t₁≲t₂ ⟧n H φ i
... | j , eq with ⟦ t₂≲t₃ ⟧n H φ j
...   | k , eq' = k , trans eq eq'
⟦ n-·lift₁ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H φ with ⟦ π ⟧n H φ
... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = ρ₃τ≲ρ₁τ·ρ₂τ , ρ₁τ≲ρ₃τ , ρ₂τ≲ρ₃τ
  where
    ρ₃τ≲ρ₁τ·ρ₂τ : (i : Fin (fst (⟦ ρ₃ ⟧t H))) →
                  DP.Σ (Fin (fst (⟦ ρ₁ ⟧t H)))
                  (λ j → snd (⟦ ρ₁ ⟧t H) j (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) i (⟦ τ ⟧t H))
                  or
                  DP.Σ (Fin (fst (⟦ ρ₂ ⟧t H)))
                  (λ j → snd (⟦ ρ₂ ⟧t H) j (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) i (⟦ τ ⟧t H))
    ρ₃τ≲ρ₁τ·ρ₂τ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong-app P (⟦ τ ⟧t H))
    ... | right (j , P) = right (j , cong-app P (⟦ τ ⟧t H))
    ρ₁τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₁ ⟧t H))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
              (λ j → snd (⟦ ρ₁ ⟧t H) i (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) j (⟦ τ ⟧t H))
    ρ₁τ≲ρ₃τ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong-app P (⟦ τ ⟧t H)

    ρ₂τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₂ ⟧t H))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
              (λ j → snd (⟦ ρ₂ ⟧t H) i (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) j (⟦ τ ⟧t H))
    ρ₂τ≲ρ₃τ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong-app P (⟦ τ ⟧t H)
⟦ n-·lift₂ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H φ with ⟦ π ⟧n H φ
... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = τρ₃≲τρ₁·τρ₂ , τρ₁≲τρ₃ , τρ₂τ≲τρ₃
  where
    τρ₃≲τρ₁·τρ₂ : (i : Fin (fst (⟦ ρ₃ ⟧t H))) →
                  DP.Σ (Fin (fst (⟦ ρ₁ ⟧t H)))
                  (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₁ ⟧t H) j)  ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) i))
                  or
                  DP.Σ (Fin (fst (⟦ ρ₂ ⟧t H)))
                  (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₂ ⟧t H) j) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) i))
    τρ₃≲τρ₁·τρ₂ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong (⟦ τ ⟧t H) P)
    ... | right (j , P) = right (j , cong (⟦ τ ⟧t H) P)
    
    τρ₁≲τρ₃ : (i : Fin (fst (⟦ ρ₁ ⟧t H))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
              (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₁ ⟧t H) i) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) j))
    τρ₁≲τρ₃ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong (⟦ τ ⟧t H) P

    τρ₂τ≲τρ₃ : (i : Fin (fst (⟦ ρ₂ ⟧t H))) →
              DP.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
              (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₂ ⟧t H) i) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) j))
    τρ₂τ≲τρ₃ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong (⟦ τ ⟧t H) P
⟦ n-ε-R ⟧n H φ = ε-id-R
⟦ n-ε-L ⟧n H φ = ε-id-L
⟦ n-row≲ ρ₁ ρ₂ f ⟧n H Φ = help ρ₁ ρ₂ f H Φ
  where
    help : ∀ {Φ : PEnv Δ ℓΦ} → (ρ₁ ρ₂ : Row Δ κ) →
         ρ₁ ⊆ ρ₂ → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → (⟦ ⦃- ρ₁ -⦄ ≲ ⦃- ρ₂ -⦄ ⟧p H)
    help (l ▹ τ) ρ₂ ι H φ = ⟦ ι {ℓ = lzero} l τ end ⟧∈ H φ 
    help (l ▹ τ ， ρ₁) ρ₂ ι H φ fzero = ⟦ ι {ℓ = lzero} l τ here ⟧∈ H φ fzero
    help (l ▹ τ ， ρ₁) ρ₂ ι H φ (fsuc i) = help ρ₁ ρ₂ (there⊆ _ _ ι) H φ i

-- TODO:
-- - prove separately the injections from ρ₁ and ρ₂ into (ρ₁ ++ ρ₂);
--   you should be able to prove that ρ₁ ⊆ (ρ₁ ++ ρ₂) and so forth.
-- - Not sure on the other direction; way in which syntactic rows
--   translate to semantic rows may fuck me here, as I think order may
--   be reversed.
     
-- ⟦ n-row· ρ₁ ρ₂ ρ₃ {ev} eq ⟧n H Φ rewrite ⟦ eq ⟧eq-ρ H = 
--   (λ i → {!!}) , ((λ i → {!!} , {!!}) , (λ i → {!!} , {!!}))
  
