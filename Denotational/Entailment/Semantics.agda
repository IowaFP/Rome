open import Rome.Prelude
open import Rome.Preludes.Level
open import Data.Product as DP

module Rome.Denotational.Entailment.Semantics (g : Potatoes) where

open import Rome.IndexCalculus.Properties
import Rome.IndexCalculus as Ix

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Types.Semantics g
open import Rome.Denotational.Equivalence.Syntax 
open import Rome.Denotational.Equivalence.Semantics g -- extensionality
open import Rome.Denotational.Terms.Syntax
open import Rome.Denotational.Entailment.Syntax
open import Rome.Denotational.GVars.Kinds

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

⟦_⟧∈ : ∀ {l : String} {τ : Type Δ κ} {m : Row Δ κ} {Φ : PEnv Δ ℓΦ} → 
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
    ρ₃τ≲ρ₁τ·ρ₂τ : (i : Fin (⟦ ρ₃ ⟧t H .fst)) →
      DP.Σ (Fin (⟦ ρ₁ ⟧t H .fst))
      (λ j →
         (⟦ ρ₁ ⟧t H .snd j .fst , ⟦ ρ₁ ⟧t H .snd j .snd (⟦ τ ⟧t H)) ≡
         (⟦ ρ₃ ⟧t H .snd i .fst , ⟦ ρ₃ ⟧t H .snd i .snd (⟦ τ ⟧t H)))
      or
      DP.Σ (Fin (⟦ ρ₂ ⟧t H .fst))
      (λ j →
         (⟦ ρ₂ ⟧t H .snd j .fst , ⟦ ρ₂ ⟧t H .snd j .snd (⟦ τ ⟧t H)) ≡
         (⟦ ρ₃ ⟧t H .snd i .fst , ⟦ ρ₃ ⟧t H .snd i .snd (⟦ τ ⟧t H)))
    ρ₃τ≲ρ₁τ·ρ₂τ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong₂ _,_ (cong fst P) (cong (λ x → x .snd (⟦ τ ⟧t H)) P)) -- cong-app P (⟦ τ ⟧t H)
    ... | right (j , P) = right (j , cong₂ _,_ (cong fst P) ((cong (λ x → x .snd (⟦ τ ⟧t H)) P)))
    ρ₁τ≲ρ₃τ : (i : Fin (⟦ ρ₁ ⟧t H .proj₁)) →
      DP.Σ (Fin (⟦ ρ₃ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₁ ⟧t H .snd i .proj₁ , ⟦ ρ₁ ⟧t H .snd i .snd (⟦ τ ⟧t H)) ≡
         (⟦ ρ₃ ⟧t H .snd j .proj₁ , ⟦ ρ₃ ⟧t H .snd j .snd (⟦ τ ⟧t H)))
    ρ₁τ≲ρ₃τ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong₂ _,_ (cong fst P) ( cong (λ x → x .snd (⟦ τ ⟧t H)) P)

    ρ₂τ≲ρ₃τ : (i : Fin (⟦ ρ₂ ⟧t H .proj₁)) →
      DP.Σ (Fin (⟦ ρ₃ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₂ ⟧t H .snd i .proj₁ , ⟦ ρ₂ ⟧t H .snd i .snd (⟦ τ ⟧t H)) ≡
         (⟦ ρ₃ ⟧t H .snd j .proj₁ , ⟦ ρ₃ ⟧t H .snd j .snd (⟦ τ ⟧t H)))
    ρ₂τ≲ρ₃τ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong₂ _,_ (cong fst P) (cong (λ x → x .snd (⟦ τ ⟧t H)) P) 
⟦ n-·lift₂ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H φ with ⟦ π ⟧n H φ
... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = τρ₃≲τρ₁·τρ₂ , τρ₁≲τρ₃ , τρ₂τ≲τρ₃
  where
    τρ₃≲τρ₁·τρ₂ : (i : Fin (⟦ ρ₃ ⟧t H .proj₁)) →
      DP.Σ (Fin (⟦ ρ₁ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₁ ⟧t H .snd j .proj₁ , ⟦ τ ⟧t H (⟦ ρ₁ ⟧t H .snd j .snd)) ≡
         (⟦ ρ₃ ⟧t H .snd i .proj₁ , ⟦ τ ⟧t H (⟦ ρ₃ ⟧t H .snd i .snd)))
      or
      DP.Σ (Fin (⟦ ρ₂ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₂ ⟧t H .snd j .proj₁ , ⟦ τ ⟧t H (⟦ ρ₂ ⟧t H .snd j .snd)) ≡
         (⟦ ρ₃ ⟧t H .snd i .proj₁ , ⟦ τ ⟧t H (⟦ ρ₃ ⟧t H .snd i .snd)))
    τρ₃≲τρ₁·τρ₂ i with ρ₃≲ρ₁·ρ₂ i
    ... | left (j , P) = left (j , cong₂ _,_ (cong fst P) (cong (λ x → ⟦ τ ⟧t H (x .snd)) P)) -- 
    ... | right (j , P) = right (j , cong₂ _,_ (cong fst P) (cong (λ x → ⟦ τ ⟧t H (x .snd)) P)) -- 
    
    τρ₁≲τρ₃ : (i : Fin (⟦ ρ₁ ⟧t H .proj₁)) →
      DP.Σ (Fin (⟦ ρ₃ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₁ ⟧t H .snd i .proj₁ , ⟦ τ ⟧t H (⟦ ρ₁ ⟧t H .snd i .snd)) ≡
         (⟦ ρ₃ ⟧t H .snd j .proj₁ , ⟦ τ ⟧t H (⟦ ρ₃ ⟧t H .snd j .snd)))
    τρ₁≲τρ₃ i with ρ₁≲ρ₃ i
    ... | j , P = j , cong₂ _,_ (cong fst P) (cong (λ x → ⟦ τ ⟧t H (x .snd)) P) 

    τρ₂τ≲τρ₃ : (i : Fin (⟦ ρ₂ ⟧t H .proj₁)) →
      DP.Σ (Fin (⟦ ρ₃ ⟧t H .proj₁))
      (λ j →
         (⟦ ρ₂ ⟧t H .snd i .proj₁ , ⟦ τ ⟧t H (⟦ ρ₂ ⟧t H .snd i .snd)) ≡
         (⟦ ρ₃ ⟧t H .snd j .proj₁ , ⟦ τ ⟧t H (⟦ ρ₃ ⟧t H .snd j .snd)))
    τρ₂τ≲τρ₃ i with ρ₂≲ρ₃ i
    ... | j , P = j , cong₂ _,_ (cong fst P) (cong (λ x → ⟦ τ ⟧t H (x .snd)) P)
⟦ n-ε-R ⟧n H φ = ε-id-R
⟦ n-ε-L ⟧n H φ = ε-id-L
⟦ n-row≲ ρ₁ ρ₂ f ⟧n H Φ = help ρ₁ ρ₂ f H Φ
  where
    help : ∀ {Φ : PEnv Δ ℓΦ} → (ρ₁ ρ₂ : Row Δ κ) →
         ρ₁ ⊆ ρ₂ → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → (⟦ ⦃- ρ₁ -⦄ ≲ ⦃- ρ₂ -⦄ ⟧p H)
    help (l ▹ τ) ρ₂ ι H φ = ⟦ ι {ℓ = lzero} l τ end ⟧∈ H φ 
    help (l ▹ τ ， ρ₁) ρ₂ ι H φ fzero = ⟦ ι {ℓ = lzero} l τ here ⟧∈ H φ fzero
    help (l ▹ τ ， ρ₁) ρ₂ ι H φ (fsuc i) = help ρ₁ ρ₂ (there⊆ _ _ ι) H φ i
