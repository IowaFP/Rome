{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Congruence where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Renaming


open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Decidability

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation

--------------------------------------------------------------------------------
-- - Uniformity is preserved under renaming (ren-Uniform)
--   (This is actually just what uniformity means.)

ren-Uniform : ∀ {F : KripkeFunction Δ₁ κ₁ κ₂} → (ρ : Renamingₖ Δ₁ Δ₂) → Uniform F → Uniform (renKripke ρ F) 
ren-Uniform ρ Unif-F ρ₁ ρ₂ V₁ V₂ q = Unif-F (ρ₁ ∘ ρ) ρ₂ V₁ V₂ q

--------------------------------------------------------------------------------
-- renaming respects ≋

ren-≋ : ∀ {V₁ V₂ : SemType Δ₁ κ} 
        (ρ : Renamingₖ Δ₁ Δ₂) → 
        V₁ ≋ V₂ → 
        (renSem ρ V₁) ≋ (renSem ρ V₂)
ren-≋ {κ = ★} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = L} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = F} {G} ρ₁ (unif-F , unif-G , Ext) = 
  (λ ρ₂ ρ₃ V₁  → unif-F (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  (λ ρ₂ ρ₃ V₁  → unif-G (ρ₂ ∘ ρ₁) ρ₃ V₁) ,  
  λ ρ₃ q → Ext (ρ₃ ∘ ρ₁) q
ren-≋ {κ = R[ κ ]} {V₁ = left x} {left y} ρ refl = refl
ren-≋ {κ = R[ κ ]} {V₁ = right (n , P)} {right (m , Q)} ρ (refl , eq) = 
  refl , λ { i → (ren-≋ {κ = L} ρ (eq i .fst)) , ren-≋ ρ (eq i .snd) }

-- --------------------------------------------------------------------------------
-- -- Application respects ≋

cong-App : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
cong-App {V₁ = F} {G} (unif-F , unif-G , Ext) q = Ext id q           

-- --------------------------------------------------------------------------------
-- -- Singleton formation respects ≋

cong-⁅⁆ : ∀ {V₁ V₂ : SemType Δ L × SemType Δ κ} → V₁ ≋₂ V₂ → (right (⁅ V₁ ⁆ , tt)) ≋ (right (⁅ V₂ ⁆ , tt))
cong-⁅⁆ {V₁ = V₁} {V₂} v = refl , (λ { fzero → v })

--------------------------------------------------------------------------------
-- Mapping respects ≋

cong-<$> : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ R[ κ₁ ]} → 
           _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <$>V W₁)  (V₂ <$>V W₂)
cong-<$> v {left x} {left x₁} refl = cong (_<$> x) (reify-≋ v)
cong-<$> v {right ((n , P) , _)} {right ((m , Q) , _)} (refl , eq) =  refl , λ { i → eq i .fst , cong-App v (eq i .snd) }

--------------------------------------------------------------------------------
-- Given a : κ₁, The semantic image of (λ f : κ₁ `→ κ₂. f a) is uniform.
-- (This goal appears with the use of the flapping operator (??).)

Unif-apply : ∀ {V₁ V₂ : SemType Δ κ₁} → 
               V₁ ≋ V₂ → 
               Uniform {Δ} {κ₁ `→ κ₂} {κ₂} (apply V₂)
Unif-apply {V₁ = V₁} {V₂} v ρ₁ ρ₂ V₃ V₄ x = 
  trans-≋
    (fst x id ρ₂ (renSem ρ₁ V₂) (renSem ρ₁ V₂) (ren-≋ ρ₁ (refl-≋ᵣ v)))
    (third x ρ₂ (sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ v)))) 

cong-apply : ∀ {V₁ V₂ : SemType Δ κ₁} → 
               V₁ ≋ V₂ → 
               _≋_ {κ = (κ₁ `→ κ₂) `→ κ₂} (apply V₁)  (apply V₂)
cong-apply v = 
  Unif-apply (sym-≋ v) , 
  Unif-apply v , 
  λ ρ v' → third v' id (ren-≋ ρ v)  

-- --------------------------------------------------------------------------------
-- -- Mapping respects ≋

cong-<?> : ∀ {V₁ V₂ : SemType Δ R[ κ₁ `→ κ₂ ]} → 
           _≋_ {κ = R[ κ₁ `→ κ₂ ]} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           _≋_ {κ = κ₁} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <?>V W₁)  (V₂ <?>V W₂)
cong-<?> v {W₁} {W₂} w = 
  cong-<$> 
  (cong-apply w) v

--------------------------------------------------------------------------------
-- Congruence over complements

cong-compl : {n m : ℕ} 
             (A B : Fin n → SemType Δ L × SemType Δ κ)
             (C D : Fin m → SemType Δ L × SemType Δ κ) → 
             ((i : Fin n) → A i ≋₂ B i) → 
             ((i : Fin m) → C i ≋₂ D i) → 
             compl A C ≋R compl B D
cong-compl {n = zero} A B C D i₁ i₂ = refl , λ ()
cong-compl {n = suc n} A B C D i₁ i₂ with i₁ fzero | A fzero .fst ∈Row C | B fzero .fst ∈Row D 
... | eq , rel  | yes p         | yes q = cong-compl (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂
... | eq₁ , rel | yes (j , eq₂) | no q = ⊥-elim (q (j , (trans (trans (sym eq₁) eq₂) (i₂ j .fst))))
... | eq₁ , rel | no  q         | yes (j , eq₂) = ⊥-elim (q (j , (trans (trans eq₁ eq₂) (sym (i₂ j .fst)))))
... | eq , rel  | no  p         | no q  with 
      (compl (A ∘ fsuc) C)
    | (compl (B ∘ fsuc) D)
    | cong-compl (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂
    | cong-compl (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂ .fst
... | n₁ , P | n₂ , Q | (refl , P≋Q) | refl = 
  refl , (λ { fzero    → i₁ fzero ; 
              (fsuc i) → P≋Q i })

cong-─v : ∀ {V₁ V₂ W₁ W₂ : Row Δ R[ κ ]} → 
           V₂ ≋R W₂ → 
           V₁ ≋R W₁ → 
           (V₂ ─v V₁) ≋R (W₂ ─v W₁)
cong-─v {V₁ = zero , P} {zero , Q} {l , R} {j , I} (refl , v₂) (refl , v₁) = refl , λ ()
cong-─v {V₁ = zero , P} {suc m , Q} {l , R} {j , I} (refl , v₂) (refl , v₁) = refl , v₂
cong-─v {V₁ = suc n , P} {zero , Q} {l , R} {j , I} (refl , v₂) (refl , v₁) = refl , λ ()
cong-─v {V₁ = suc n , P} {suc m , Q} {l , R} {j , I} (refl , v₂) (refl , v₁) = cong-compl Q I P R v₂ v₁ 

cong-─V : ∀ {V₁ V₂ W₁ W₂ : SemType Δ R[ κ ]} → 
           V₂ ≋ W₂ → 
           V₁ ≋ W₁ → 
           (V₂ ─V V₁) ≋ (W₂ ─V W₁)
cong-─V {V₁ = left x₁} {left x₂} {left x₃} {left x₄} refl refl = refl
cong-─V {V₁ = left x} {right ((n , P) , _)} {left y} {right ((m , Q) , _)} (refl , rel) refl = 
  cong-─₂ (cong-NormalSimpleRow (reifyRow-≋ P Q rel )) refl
cong-─V {V₁ = right ((n , P) , _)} {left x} {right ((m , Q) , _)} {left y} refl (refl , rel) = 
  cong₂ _─₁_ refl (cong-NormalSimpleRow (reifyRow-≋ P Q rel))
cong-─V {V₁ = right ((n , P) , _)} {right ((m , Q) , _)} {right ((l , R) , _)} {right ((j , I) , _)} v₂ v₁ = 
  cong-─v v₂ v₁ 
