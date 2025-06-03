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
-- open import Rome.Operational.Types.Normal.Properties.Decidability

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
ren-≋ {κ = R[ κ ]} {V₁ = ne x} {ne y} ρ refl = refl
ren-≋ {κ = R[ κ ]} {V₁ = (l₁ ▹ τ₁)} {(l₂ ▹ τ₂)} ρ (refl , rel) = refl , (ren-≋ ρ rel)
ren-≋ {κ = R[ κ ]} {V₁ = row _ _ } {row _ _} ρ (refl , eq) = 
  refl , λ { i → eq i .fst , ren-≋ ρ (eq i .snd) }
ren-≋ {κ = R[ κ ]} {V₁ = ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} r (rel₁ , rel₂) = (ren-≋ r rel₁) , (ren-≋ r rel₂)

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

-- cong-⁅⁆ : ∀ {V₁ V₂ : Label × SemType Δ κ} → V₁ ≋₂ V₂ → (row (⁅ V₁ ⁆ , tt)) ≋ (right (⁅ V₂ ⁆ , tt))
-- cong-⁅⁆ {V₁ = V₁} {V₂} v = refl , (λ { fzero → v })

--------------------------------------------------------------------------------
-- Mapping respects ≋

cong-<$> : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ R[ κ₁ ]} → 
           _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <$>V W₁)  (V₂ <$>V W₂)
cong-<$> v {ne x} {ne x₁} refl = cong (_<$> x) (reify-≋ v)
cong-<$> v {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , rel) = refl , (cong-App v rel)
cong-<$> v {row (n , P) _} {row (m , Q) _} (refl , eq) =  refl , λ { i → eq i .fst , cong-App v (eq i .snd) }
cong-<$> v {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (cong-<$> v rel₁) , (cong-<$> v rel₂)

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

-- -- --------------------------------------------------------------------------------
-- -- -- Mapping respects ≋

cong-<?> : ∀ {V₁ V₂ : SemType Δ R[ κ₁ `→ κ₂ ]} → 
           _≋_ {κ = R[ κ₁ `→ κ₂ ]} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           _≋_ {κ = κ₁} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <?>V W₁)  (V₂ <?>V W₂)
cong-<?> v {W₁} {W₂} w = 
  cong-<$> 
  (cong-apply w) v

-- --------------------------------------------------------------------------------
-- -- Congruence over complements

cong-compl : {n m : ℕ} 
             (A B : Fin n → Label × SemType Δ κ)
             (C D : Fin m → Label × SemType Δ κ) → 
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
... | n₁ , P | n₂ , Q | (refl , P≋Q) = 
  refl , (λ { fzero    → i₁ fzero ; 
              (fsuc i) → P≋Q i })

cong-─v : ∀ {V₁ V₂ W₁ W₂ : Row (SemType Δ κ)} → 
           V₂ ≋R W₂ → 
           V₁ ≋R W₁ → 
           (V₂ ─v V₁) ≋R (W₂ ─v W₁)
cong-─v {V₁ = n , P} {m , Q} {l , R} {j , I} (refl , v₂) (refl , v₁) = cong-compl Q I P R v₂ v₁ 

cong-─V : ∀ {V₁ V₂ W₁ W₂ : SemType Δ R[ κ ]} → 
           V₂ ≋ W₂ → 
           V₁ ≋ W₁ → 
           (V₂ ─V V₁) ≋ (W₂ ─V W₁)
cong-─V {V₁ = ne x₁} {ne x₂} {ne x₃} {ne x₄} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = ne x₁} {x₂ ▹ x₃} {ne x₄} {x₅ ▹ x₆} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = ne x₁} {row ρ x₂} {ne x₃} {row ρ₁ x₄} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = ne x₁} {V₂ ─ V₃} {ne x₂} {W₂ ─ W₃} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = x₁ ▹ x₂} {ne x₃} {x₄ ▹ x₅} {ne x₆} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = x₁ ▹ x₂} {x₃ ▹ x₄} {x₅ ▹ x₆} {x₇ ▹ x₈} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = x₁ ▹ x₂} {row ρ x₃} {x₄ ▹ x₅} {row ρ₁ x₆} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = x₁ ▹ x₂} {V₂ ─ V₃} {x₃ ▹ x₄} {W₂ ─ W₃} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = row ρ x₁} {ne x₂} {row ρ₁ x₃} {ne x₄} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = row ρ x₁} {x₂ ▹ x₃} {row ρ₁ x₄} {x₅ ▹ x₆} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = row ρ x₁} {row ρ₁ x₂} {row ρ₂ x₃} {row ρ₃ x₄} rel₁ rel₂ = cong-─v rel₁ rel₂
cong-─V {V₁ = row ρ x₁} {V₂ ─ V₃} {row ρ₁ x₂} {W₂ ─ W₃} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = V₁ ─ V₂} {ne x₁} {W₁ ─ W₂} {ne x₂} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = V₁ ─ V₂} {x₁ ▹ x₂} {W₁ ─ W₂} {x₃ ▹ x₄} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = V₁ ─ V₂} {row ρ x₁} {W₁ ─ W₂} {row ρ₁ x₂} rel₁ rel₂ = rel₁ , rel₂
cong-─V {V₁ = V₁ ─ V₂} {V₃ ─ V₄} {W₁ ─ W₂} {W₃ ─ W₄} rel₁ rel₂ = rel₁ , rel₂
