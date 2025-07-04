{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Commutativity where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation
open import Rome.Operational.Types.Theorems.Completeness.Congruence

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with application.

↻-renSem-app : ∀ (r : Renamingₖ Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≋_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≋ V₂ →  
                renSem r (F ·V V₁) ≋ (renSem {κ = κ₁ `→ κ₂} r G ·V renSem r V₂)
↻-renSem-app r {F} {G} (Unif-F , Unif-G , Ext) {V₁} {V₂} v = 
  trans-≋ (Unif-F id r V₁ V₂ v) ((Ext r (ren-≋ r (refl-≋ₗ (sym-≋ v)))))

-- --------------------------------------------------------------------------------
-- -- Renamingₖ commutes with <$>

↻-renSem-<$> : ∀ (r : Renamingₖ Δ₁ Δ₂) 
            {V₁ V₂ : SemType Δ₁ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ₁ R[ κ₁ ]} → 
            _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (renSem {κ = R[ κ₂ ]} r (V₁ <$>V W₁)) (renSem {κ = κ₁ `→ κ₂} r V₂ <$>V renSem {κ = R[ κ₁ ]} r W₂)
↻-renSem-<$> r {F} {G} (Unif-F , Unif-G , Ext) {ne x} {ne _} refl = 
  refl , 
  (λ r₁ r₂ n → trans-≋
    (Unif-F (r₁ ∘ r) r₂ (reflect n) (reflect n) (reflect-≋ refl)) (refl-Extₗ Ext (r₂ ∘ r₁ ∘ r) (↻-ren-reflect r₂ n))) , 
  (λ r₁ r₂ n → trans-≋
    (Unif-G (r₁ ∘ r) r₂ (reflect n) (reflect n) (reflect-≋ refl)) (refl-Extᵣ Ext (r₂ ∘ r₁ ∘ r) (↻-ren-reflect r₂ n))) , 
  (λ r' v → Ext (r' ∘ r) (reflect-≋ refl)) , 
  refl 
↻-renSem-<$> r {V₁} {V₂} v {l₁ ▹ τ₁} {l₁ ▹ τ₂} (refl , rel) = refl , (↻-renSem-app r v rel)
↻-renSem-<$> r {V₁} {V₂} v {row (n , P) _} {row (_ , Q) _} (refl , eq) = refl , λ i → eq i .fst , (↻-renSem-app r v (eq i .snd))
↻-renSem-<$> r {V₁} {V₂} v {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (↻-renSem-<$> r v rel₁) , (↻-renSem-<$> r v rel₂)
↻-renSem-<$> r {F} {G} (Unif-F , Unif-G , Ext-FG) {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Unif-φ₁ , Unif-φ₂ , Ext-φ , refl) = 
  refl , 
  (λ r₁ r₂ n → 
    trans-≋ 
      (Unif-F (r₁ ∘ r) r₂ (φ₁ (r₁ ∘ r) n) (φ₁ (r₁ ∘ r) n) (trans-≋ (Ext-φ (r₁ ∘ r) n) (sym-≋ (Ext-φ (r₁ ∘ r) n)))) 
      (refl-Extₗ Ext-FG _ (Unif-φ₁ _ _ n))) , 
  (λ r₁ r₂ n → 
    trans-≋ 
      (Unif-G (r₁ ∘ r) r₂ (φ₂ (r₁ ∘ r) n) (φ₂ (r₁ ∘ r) n) (trans-≋ (sym-≋ (Ext-φ (r₁ ∘ r) n)) (Ext-φ (r₁ ∘ r) n))) 
      (refl-Extᵣ Ext-FG _ (Unif-φ₂ _ _ n))), 
  (λ r' v → Ext-FG (r' ∘ r) (Ext-φ _ v)) , 
  refl
-- --------------------------------------------------------------------------------
-- -- Renaming commutes over complement

↻-renSem-compl : {n m : ℕ} 
                 (r : Renamingₖ Δ₁ Δ₂) → 
                 (A B : Fin n → Label × SemType Δ₁ κ)
                 (C D : Fin m → Label × SemType Δ₁ κ) → 
                 ((i : Fin n) → A i ≋₂ B i) → 
                 ((i : Fin m) → C i ≋₂ D i) → 
                 renRow r (compl A C) ≋R 
                 compl (overᵣ (renSem r) ∘ B) (overᵣ (renSem r) ∘ D)
↻-renSem-compl {n = zero} r A B C D i₁ i₂ = refl , (λ ())
↻-renSem-compl {n = suc n} r A B C D i₁ i₂ with
      A fzero .fst ∈Row? C 
    | (B fzero .fst) ∈Row? (overᵣ (renSem r) ∘ D)
... | yes p         | yes q  =
  ↻-renSem-compl r (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂
... | yes (j , eq₂) | no q          = 
  ⊥-elim (q (j , (trans (sym (i₁ fzero .fst)) (trans eq₂ (i₂ j .fst)))))
... | no q          | yes (j , eq₂) = ⊥-elim (q (j , trans (i₁ fzero .fst) (trans eq₂ (sym (i₂ j .fst)))))
... | no  p         | no q  with
      (compl (A ∘ fsuc) C) 
    | compl (overᵣ (renSem r) ∘ (B ∘ fsuc)) (overᵣ (renSem r) ∘ D)
    | (↻-renSem-compl r (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂) 
... | n₁ , P | n₂ , Q | refl , ih =  refl , λ { fzero → i₁ fzero .fst  , (ren-≋ r (i₁ fzero .snd)) ; (fsuc i) → ih i }

↻-renSem-─v : (r : Renamingₖ Δ₁ Δ₂) → 
              {V₁ V₂ W₁ W₂ : Row (SemType Δ₁ κ)} → 
              V₂ ≋R W₂ → 
              V₁ ≋R W₁ → 
              renRow r (V₂ ─v V₁) ≋R (renRow r W₂ ─v renRow r W₁)
↻-renSem-─v r {n , P} {m , Q} {_ , R} {_ , I} (refl , V₂≋) (refl , V₁≋) = ↻-renSem-compl r Q I P R V₂≋ V₁≋

↻-renSem-─V : (r : Renamingₖ Δ₁ Δ₂) → 
              {V₁ V₂ W₁ W₂ : SemType Δ₁ R[ κ ]} → 
              V₂ ≋ W₂ → 
              V₁ ≋ W₁ → 
              renSem r (V₂ ─V V₁) ≋ (renSem r W₂ ─V renSem r W₁)
↻-renSem-─V r ρ₁@{ne x₁} ρ₂@{ne x₂} ρ₃@{ne x₃} ρ₄@{ne x₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{ne x₁} ρ₂@{x₂ ▹ x₃} ρ₃@{ne x₄} ρ₄@{x₅ ▹ x₆} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{ne x₁} ρ₂@{row _ x₂} ρ₃@{ne x₃} ρ₄@{row _ x₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{ne x₁} ρ₂@{V₂ ─ V₃} ρ₃@{ne x₂} ρ₄@{W₂ ─ W₃} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{ne x₁} ρ₂@{_ <$> _} ρ₃@{ne x₂} ρ₄@{_ <$> _} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{x₁ ▹ x₂} ρ₂@{ne x₃} ρ₃@{x₄ ▹ x₅} ρ₄@{ne x₆} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{x₁ ▹ x₂} ρ₂@{x₃ ▹ x₄} ρ₃@{x₅ ▹ x₆} ρ₄@{x₇ ▹ x₈} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{x₁ ▹ x₂} ρ₂@{row _ x₃} ρ₃@{x₄ ▹ x₅} ρ₄@{row _ x₆} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{x₁ ▹ x₂} ρ₂@{(V₂ ─ V₃) {nr₁}} ρ₃@{x₃ ▹ x₄} ρ₄@{(W₂ ─ W₃) {nr₂}} rel₁ rel₂ =  ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{x₁ ▹ x₂} ρ₂@{_ <$> _} ρ₃@{x₃ ▹ x₄} ρ₄@{_ <$> _} rel₁ rel₂ =  ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{row _ x₁} ρ₂@{ne x₂} ρ₃@{row _ x₃} ρ₄@{ne x₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{row _ x₁} ρ₂@{x₂ ▹ x₃} ρ₃@{row _ x₄} ρ₄@{x₅ ▹ x₆} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {row ρ x₁} {row ρ₁ x₂} {row ρ₂ x₃} {row ρ₃ x₄} rel₁ rel₂ = ↻-renSem-─v r rel₁ rel₂
↻-renSem-─V r ρ₁@{row _ x₁} ρ₂@{V₂ ─ V₃} ρ₃@{row _ x₂} ρ₄@{W₂ ─ W₃} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{row _ x₁} ρ₂@{_ <$> _} ρ₃@{row _ x₂} ρ₄@{_ <$> _} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{V₁ ─ V₂} ρ₂@{ne x₁} ρ₃@{W₁ ─ W₂} ρ₄@{ne x₂} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{V₁ ─ V₂} ρ₂@{x₁ ▹ x₂} ρ₃@{W₁ ─ W₂} ρ₄@{x₃ ▹ x₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{V₁ ─ V₂} ρ₂@{row _ x₁} ρ₃@{W₁ ─ W₂} ρ₄@{row _ x₂} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{V₁ ─ V₂} ρ₂@{V₃ ─ V₄} ρ₃@{W₁ ─ W₂} ρ₄@{W₃ ─ W₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r ρ₁@{V₁ ─ V₂} ρ₂@{_ <$> _} ρ₃@{W₁ ─ W₂} ρ₄@{_ <$> _} rel₁ rel₂ = ren-≋ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {ρ₁@(φ₁ <$> n₁)} ρ₂@{φ <$> x₁} {ρ₃@(φ₂ <$> n₂)} ρ₄@{φ₃ <$> x₂} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {ρ₁@(φ₁ <$> n₁)} ρ₂@{ne x₁} {ρ₃@(φ₂ <$> n₂)}    ρ₄@{ne x₂} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {ρ₁@(φ₁ <$> n₁)} ρ₂@{x₁ ▹ x₂} {ρ₃@(φ₂ <$> n₂)}  ρ₄@{x₃ ▹ x₄} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {ρ₁@(φ₁ <$> n₁)} ρ₂@{row ρ x₁} {ρ₃@(φ₂ <$> n₂)} ρ₄@{row _ _} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-─V r {ρ₁@(φ₁ <$> n₁)} ρ₂@{_ ─ _} {ρ₃@(φ₂ <$> n₂)}  ρ₄@{_ ─  _} rel₁ rel₂ = ren-≋ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≋ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂

--------------------------------------------------------------------------------
-- Uniformity of <?>V

Unif-<?> : ∀ (f : SemType Δ R[ κ₁ `→ κ₂ ]) → f ≋ f → 
            Uniform (λ r v → (renSem r f <?>V v))
Unif-<?> f q ρ₁ ρ₂ V₁ V₂ v = 
  trans-≋ 
  (↻-renSem-<$> ρ₂ 
    (cong-apply (refl-≋ₗ v))
    (ren-≋ ρ₁ q)) 
  (cong-<$> 
    (ren-Uniform ρ₂ (Unif-apply (refl-≋ₗ v)) , 
      Unif-apply (ren-≋ ρ₂ (refl-≋ᵣ v)) , 
      λ r v' → third v' id ((renSem-comp-≋ ρ₂ r v))) 
    (sym-≋ (renSem-comp-≋ ρ₁ ρ₂ q))) 
    
--------------------------------------------------------------------------------
-- - Renamingₖ commutes with ξ
-- - ξ is congruent w.r.t. semantic equivalence 


Unif-ξ : ∀ {Δ} {κ} (Ξ : Xi) → Uniform {Δ = Δ} {κ₁ = R[ κ ]} {κ₂ = κ} (ξ-Kripke Ξ)
↻-renSem-ξ : ∀ {Δ₁} {Δ₂} (Ξ : Xi) {κ : Kind} (r : Renamingₖ Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          _≋_ {κ = R[ κ ]} V₁ V₂ → renSem r (ξ Ξ V₁) ≋ ξ Ξ (renSem {κ = R[ κ ]} r V₂) 
cong-ξ : ∀ (Ξ : Xi) {κ} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → ξ Ξ τ₁ ≋ ξ Ξ τ₂

Unif-ξ Ξ r = ↻-renSem-ξ Ξ

Unif-ξ<?> : ∀ (Ξ : Xi) (f : SemType Δ R[ κ₁ `→ κ₂ ]) → f ≋ f → Uniform (λ r v → ξ Ξ (renSem r f <?>V v))
Unif-ξ<?> Ξ f f≋f ρ₂ ρ₃ V₁ V₂ v = 
  trans-≋
    (Unif-ξ Ξ id ρ₃ (renSem ρ₂ f <?>V V₁) (renSem ρ₂ f <?>V V₁) 
      (cong-<$> 
        (Unif-apply (sym-≋ v) , Unif-apply (sym-≋ v) , (λ r v' → third v' id (ren-≋ r (refl-≋ₗ v)))) 
        (ren-≋ ρ₂ f≋f)))
    (cong-ξ Ξ (Unif-<?> f f≋f ρ₂ ρ₃ V₁ V₂  v))

open Xi
↻-renSem-ξ Ξ {★} r x y x≋y = 
  trans 
    (Ξ .ren-★ r (reify x)) 
    (cong (Ξ .Ξ★) 
      (trans 
        (↻-ren-reify r x≋y) 
        (reify-≋ (ren-≋ r (refl-≋ᵣ x≋y)))))
↻-renSem-ξ Ξ {L} r x y x≋y = refl
  -- trans 
  --   (Ξ .ren-L r (reify x)) 
  --   (cong (Ξ .ΞL) 
  --     (trans 
  --       (↻-ren-reify r x≋y) 
  --       (reify-≋ (ren-≋ r (refl-≋ᵣ x≋y)))))
↻-renSem-ξ Ξ {κ₁ `→ κ₂} r f g f≋g =
  ren-Uniform 
    {F = λ ρ₁ v → ξ Ξ (renSem ρ₁ f <?>V  v)} 
    r 
    (Unif-ξ<?> Ξ f (refl-≋ₗ f≋g)) , 
  Unif-ξ<?> Ξ (renSem r g) (ren-≋ r (refl-≋ᵣ f≋g)) , 
  λ r' v → cong-ξ Ξ 
    (cong-<$> 
      (cong-apply v) 
      (renSem-comp-≋ r r' f≋g))
↻-renSem-ξ Ξ {R[ κ ]} r x y x≋y = ↻-renSem-<$> r (Unif-ξ Ξ , Unif-ξ Ξ , λ r → cong-ξ Ξ) x≋y

cong-ξ Ξ {κ = ★} {x} {y} x≋y = cong (Ξ .Ξ★) (reify-≋ x≋y)
cong-ξ Ξ {κ = L} {x} {y} x≋y = refl
cong-ξ Ξ {κ = κ₁ `→ κ₂} {f} {g} f≋g  =
  Unif-ξ<?> Ξ f (refl-≋ₗ f≋g)  , 
  Unif-ξ<?> Ξ g (refl-≋ᵣ f≋g) , 
  λ r {V₁} {V₂} v → cong-ξ Ξ 
    (cong-<$> 
      (cong-apply v) 
      (ren-≋ r f≋g))
cong-ξ Ξ {κ = R[ κ ]} {x} {y} x≋y = cong-<$> (Unif-ξ Ξ , Unif-ξ Ξ , (λ r → cong-ξ Ξ {_})) x≋y

---------------------------------------
-- instantiations for Π

↻-renSem-Π : ∀ {Δ₁} {Δ₂} (r : Renamingₖ Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≋ V₂ → renSem r (ΠV V₁) ≋ ΠV (renSem {κ = R[ κ ]} r V₂) 
↻-renSem-Π = ↻-renSem-ξ Π-rec

cong-Π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → ΠV τ₁ ≋ ΠV τ₂
cong-Π = cong-ξ Π-rec

Unif-Π : ∀ {Δ} {κ} → Uniform (Π-Kripke {Δ = Δ} {κ = κ})
Unif-Π ρ₁ = ↻-renSem-Π

---------------------------------------
-- instantiations for σ

↻-renSem-Σ : ∀ {Δ₁} {Δ₂} (r : Renamingₖ Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≋ V₂ → renSem r (ΣV V₁) ≋ ΣV (renSem {κ = R[ κ ]} r V₂) 
↻-renSem-Σ = ↻-renSem-ξ Σ-rec

cong-Σ : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → ΣV τ₁ ≋ ΣV τ₂
cong-Σ = cong-ξ Σ-rec

Unif-Σ : ∀ {Δ} {κ} → Uniform (Σ-Kripke {Δ = Δ} {κ = κ})
Unif-Σ ρ₁ = ↻-renSem-Σ


--------------------------------------------------------------------------------
-- semantic renaming commutes with evaluation
--
--            eval in (renSem r ∘ η₂)
--  Type Δ₁ κ  ------
--  |                \            
--  | eval in η₁       \          
--  |                    \          
--  V                      V        
-- NormalType Δ₂ κ ----------> SemType Δ₂ κ
--                  renSem r 


↻-renSem-eval : ∀ (r : Renamingₖ Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renSem r (eval τ η₁)) ≋ eval τ (renSem r ∘ η₂)
↻-renSem-eval-pred : ∀ (r : Renamingₖ Δ₂ Δ₃) (π : Pred Type Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renPredₖNF r (evalPred π η₁)) ≡ evalPred π (renSem r ∘ η₂)
↻-renSem-evalRow : ∀ (r : Renamingₖ Δ₂ Δ₃) (ρ : SimpleRow Type Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                     (Ρ : Env-≋ η₁ η₂) → renRow r (evalRow ρ η₁) ≋R evalRow ρ (renSem r ∘ η₂)  

idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
idext-pred : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (π : Pred Type Δ₁ R[ κ ]) →
               evalPred π η₁ ≡ evalPred π η₂

idext-row :  {η₁ η₂ : Env Δ₁ Δ₂} → (e : Env-≋ η₁ η₂) → 
             (ρ : SimpleRow Type Δ₁ R[ κ ]) → 
             (evalRow ρ η₁) ≋R evalRow ρ η₂

↻-renSem-eval-pred ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} P rewrite 
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-renSem-eval ρ ρ₂ P)  
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₃) | reify-≋ (↻-renSem-eval ρ ρ₃ P)  = refl
↻-renSem-eval-pred ρ (ρ₁ ≲ ρ₂) P rewrite
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-renSem-eval ρ ρ₂ P)  = refl


↻-renSem-eval {κ = κ} r (` α) e = ren-≋ r (e α)
↻-renSem-eval ρ₁ (`λ τ) {η₁} {η₂} e = 
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-renSem-eval ρ₃ τ (extend-≋ {η₂ = renSem (ρ₂ ∘ ρ₁) ∘ η₂}  (λ x → ren-≋ (ρ₂ ∘ ρ₁) (e x)) v)) 
      (idext (λ { Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) ; (S x) → sym-≋ (renSem-comp-≋ (ρ₂ ∘ ρ₁) ρ₃ (e x)) }) τ)) ,
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-renSem-eval ρ₃ τ (extend-≋ {η₂ = renSem ρ₂ ∘ (renSem ρ₁ ∘ η₂)}  (λ x → ren-≋ ρ₂ (sym-≋ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x)))))) v)) 
      (idext 
        (λ {     Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) 
           ; (S x) → sym-≋ (renSem-comp-≋ ρ₂ ρ₃ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x))))) }) τ)) ,
  λ ρ₂ q → idext (λ { Z → q ; (S x) → renSem-comp-≋ ρ₁ ρ₂ (e x) }) τ
↻-renSem-eval {κ = .κ₂} r (_·_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {η₁} {η₂} e = 
  trans-≋
    (↻-renSem-app r (idext (refl-≋ₗ ∘ e) τ₁) (idext (refl-≋ₗ ∘ e) τ₂))     
    (cong-App (↻-renSem-eval r τ₁ e) (↻-renSem-eval r τ₂ e))
↻-renSem-eval r (τ₁ `→ τ₂) e = cong₂ _`→_ (↻-renSem-eval r τ₁ e) (↻-renSem-eval r τ₂ e)
↻-renSem-eval r (`∀ τ) {η₁} {η₂} e = cong (`∀) 
  (trans 
    (↻-renSem-eval (liftₖ r) τ {lifte η₁} {lifte η₂} 
      (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl))) 
    (idext E τ))
  where
    E : Env-≋ (renSem (liftₖ r) ∘ lifte {κ = κ} η₂) (lifte (renSem r ∘ η₂))
    E Z = ↻-ren-reflect (liftₖ r) (` Z)
    E (S x) = 
      trans-≋ 
        (sym-≋ (renSem-comp-≋ S (liftₖ r) (refl-≋ₗ (sym-≋ (e x))))) 
        (renSem-comp-≋ r S (refl-≋ᵣ (e x)))
↻-renSem-eval r (μ τ) {η₁} {η₂} e = cong μ 
  (trans 
    (↻-ren-reify r (idext e τ)) 
    (reify-≋ (↻-renSem-eval r τ (refl-≋ᵣ ∘ e))))
↻-renSem-eval r (π ⇒ τ) e = cong₂ _⇒_ (↻-renSem-eval-pred r π e) (↻-renSem-eval r τ e)
↻-renSem-eval r (lab l) e = refl
↻-renSem-eval r ⌊ τ ⌋ e = cong ⌊_⌋ (↻-renSem-eval r τ e)
↻-renSem-eval r Π e = Unif-Π , Unif-Π , (λ ρ₁ x → cong-Π x) 
↻-renSem-eval r Σ e = Unif-Σ , Unif-Σ , (λ ρ₁ x → cong-Σ x) 
↻-renSem-eval r (τ₁ <$> τ₂) {η₁} {η₂} e = 
  trans-≋ 
    (↻-renSem-<$> r (idext e τ₁) (idext e τ₂)) 
    (cong-<$> (↻-renSem-eval r τ₁ (refl-≋ᵣ ∘ e)) (↻-renSem-eval r τ₂ (refl-≋ᵣ ∘ e)))
↻-renSem-eval r (⦅ ρ ⦆ oρ) {η₁} {η₂} e = ↻-renSem-evalRow r ρ e
↻-renSem-eval r (ρ₂ ─ ρ₁) {η₁} {η₂} e =
  trans-≋ 
    (↻-renSem-─V r (idext e ρ₂) (idext e ρ₁)) 
    (cong-─V (↻-renSem-eval r ρ₂ (refl-≋ᵣ ∘ e)) (↻-renSem-eval r ρ₁ (refl-≋ᵣ ∘ e)))
↻-renSem-eval r (l ▹ τ) {η₁} e with eval l η₁ | ↻-renSem-eval r l e 
... | ne x | ih rewrite (sym ih)   = refl , (↻-renSem-eval r τ e) 
... | lab l' | ih rewrite (sym ih) = refl , (λ { fzero → refl , (↻-renSem-eval r τ e) })

↻-renSem-evalRow r [] e = refl , (λ { () })
↻-renSem-evalRow r (x ∷ ρ) {η₁} e with evalRow ρ η₁ | ↻-renSem-evalRow r ρ e
... | (n , P) | refl , eq = 
  refl  , 
  λ { fzero → refl , (↻-renSem-eval r (x . snd) e) ; (fsuc i) → eq i }


-- ------------------------------------------------------------------------------
-- idext 

-- Evaluating types in related environments yields related semantic types.


idext-pred e (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂)) 
  | sym (reify-≋ (idext e ρ₃))  = refl
idext-pred e (ρ₁ ≲ ρ₂) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂))  = refl

idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) τ)) ,
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ sym-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) τ)) , 
  λ r q → idext (extend-≋ (ren-≋ r ∘ e) q) τ
idext {κ = κ} e (τ₁ · τ₂) = snd (snd (idext e τ₁)) id (idext e τ₂)
idext {κ = κ} e (τ₁ `→ τ₂) = cong₂ _`→_ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (π ⇒ τ) = cong₂ _⇒_ (idext-pred e π) (idext e τ)
idext {κ = κ} e (`∀ τ) = cong (`∀) (idext (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) τ)
idext {κ = ★} {η₁} {η₂} e (μ τ) with eval τ η₁ | eval τ η₂ | idext e τ
... | F | G | (Unif-F , Unif-G , Ext) = cong μ (cong `λ (Ext S refl))
idext {κ = κ} e (lab x) = refl
-- idext {κ = R[ κ ]} {η₁} {η₂} e (l ▹ τ) = cong-⁅⁆ (idext e τ)
idext {κ = κ} e ⌊ τ ⌋ = cong ⌊_⌋ (idext e τ)
idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
  Unif-Π , 
  Unif-Π , 
  λ r x → cong-Π x 
idext {κ = κ} e Σ =
  Unif-Σ , 
  Unif-Σ , 
  λ r x → cong-Σ x 
idext {κ = .(R[ κ₂ ])} e (_<$>_ {κ₁} {κ₂} τ₁ τ₂) = cong-<$> (idext e τ₁) (idext e τ₂) 
idext e (ρ₂ ─ ρ₁) = cong-─V (idext e ρ₂) (idext e ρ₁)
idext e (⦅ xs ⦆ _) = idext-row e xs
idext {η₁ = η₁} {η₂} e (l ▹ τ) with eval l η₁ | idext e l
... | ne x | ih rewrite (sym ih) = refl , (idext e τ)
... | lab l' | ih rewrite (sym ih) = refl , (λ { fzero → refl , (idext e τ) })

idext-row e [] = refl , (λ { () })
idext-row {η₁ = η₁} e (x ∷ ρ)  with evalRow ρ η₁ | idext-row e ρ 
... | n , P | refl , eq = refl , (λ { fzero → refl , (idext e (x .snd)) ; (fsuc i) → eq i })


--------------------------------------------------------------------------------
-- Syntactic renaming commutes with evaluation
-- 

--            eval in (η₂ ∘ r)
--  Type Δ₁ κ  -------
--  |                 \            
--  | ren r            \          
--  |                   \          
--  V                    V        
-- Type Δ₂ κ ----------> SemType Δ₃ κ
--           eval in η₁ 

↻-renₖ-eval : ∀ (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₂ Δ₃} → 
                  (e : Env-≋ η₁ η₂) → eval (renₖ r τ) η₁ ≋ eval τ (η₂ ∘ r)
↻-renₖ-eval-pred : ∀ (r : Renamingₖ Δ₁ Δ₂) (τ : Pred Type Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₂ Δ₃} → 
                  (e : Env-≋ η₁ η₂) → evalPred (renPredₖ r τ) η₁ ≡ evalPred τ (η₂ ∘ r)
↻-renₖ-evalRow : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : SimpleRow Type Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₂ Δ₃} → 
                  (e : Env-≋ η₁ η₂) → evalRow (renRowₖ r ρ) η₁ ≋R evalRow ρ (η₂ ∘ r)


↻-renₖ-eval-pred r (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} e rewrite
    reify-≋ (↻-renₖ-eval r ρ₁ e)
  | reify-≋ (↻-renₖ-eval r ρ₂ e)  
  | reify-≋ (↻-renₖ-eval r ρ₃ e)  = refl
↻-renₖ-eval-pred r (ρ₁ ≲ ρ₂) e rewrite
    reify-≋ (↻-renₖ-eval r ρ₁ e)
  | reify-≋ (↻-renₖ-eval r ρ₂ e)  = refl

↻-renₖ-eval r (` α) {η₁} {η₂} e = e (r α)
↻-renₖ-eval r (`λ τ) {η₁} {η₂} e = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
  trans-≋ 
    (↻-renSem-eval ρ₂ 
      (renₖ (liftₖ r) τ) 
      (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q)) 
    (idext 
      (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) 
         ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) 
      (renₖ (liftₖ r) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e ∘ r) q)) 
      (idext 
        (λ { Z     → ren-≋ ρ₂ (refl-≋ᵣ q) 
           ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e (r x)))) }) 
        τ)) , 
  λ r' q → 
    trans-≋ 
      (↻-renₖ-eval (liftₖ r) τ (extend-≋ (ren-≋ r' ∘ e) q) ) 
      (idext 
        (λ { Z     → refl-≋ᵣ q 
           ; (S x) → ren-≋ r' (refl-≋ᵣ (e (r x))) }) 
        τ)
↻-renₖ-eval r (τ₁ · τ₂) {η₁} {η₂} e = cong-App (↻-renₖ-eval r τ₁ e) (↻-renₖ-eval r τ₂ e)
↻-renₖ-eval r (τ₁ `→ τ₂) {η₁} {η₂} e = cong₂ _`→_ (↻-renₖ-eval r τ₁ e) (↻-renₖ-eval r τ₂ e)
↻-renₖ-eval r (`∀ τ) {η₁} {η₂} e = cong (`∀) 
  (trans 
    (↻-renₖ-eval (liftₖ r) τ 
      (extend-≋ 
        (ren-≋ S ∘ e) 
        (reflect-≋ {τ₁ = ` Z} refl))) 
    (idext 
      (λ { Z     → reflect-≋ refl 
         ; (S x) → (ren-≋ S ∘ refl-≋ᵣ ∘ e) (r x) }) τ))
↻-renₖ-eval r (μ τ) {η₁} {η₂} e = cong μ (reify-≋ (↻-renₖ-eval r τ e))
↻-renₖ-eval r (π ⇒ τ) {η₁} {η₂} e = cong₂ _⇒_ (↻-renₖ-eval-pred r π e) (↻-renₖ-eval r τ e)
↻-renₖ-eval r (lab l) {η₁} {η₂} e = refl
↻-renₖ-eval r ⌊ τ ⌋ {η₁} {η₂} e = cong ⌊_⌋ (↻-renₖ-eval r τ e)
↻-renₖ-eval r Π {η₁} {η₂} e = Unif-Π , Unif-Π , λ r x → cong-Π x
↻-renₖ-eval r Σ {η₁} {η₂} e = Unif-Σ , Unif-Σ , λ r x → cong-Σ x
↻-renₖ-eval r (τ₁ <$> τ₂) {η₁} {η₂} e = cong-<$> (↻-renₖ-eval r τ₁ e) (↻-renₖ-eval r τ₂ e)
↻-renₖ-eval r (⦅ ρ ⦆ oρ) {η₁} {η₂} e = ↻-renₖ-evalRow r ρ e  
↻-renₖ-eval r (ρ₂ ─ ρ₁) {η₁} {η₂} e = cong-─V (↻-renₖ-eval r ρ₂ e) (↻-renₖ-eval r ρ₁ e)
↻-renₖ-eval r (l ▹ τ) {η₁} {η₂} e with eval (renₖ r l) η₁ | ↻-renₖ-eval r l e 
... | ne x  | ih rewrite (sym ih) = refl , (↻-renₖ-eval r τ e)
... | lab l | ih rewrite (sym ih) = refl , λ { fzero → refl , (↻-renₖ-eval r τ e) }

↻-renₖ-evalRow r [] {η₁} {η₂} e = refl , λ ()
↻-renₖ-evalRow r (x ∷ ρ) {η₁} {η₂} e with evalRow (renRowₖ r ρ) η₁ | ↻-renₖ-evalRow r ρ e 
... | n , P | refl , eq = 
  refl , (λ { fzero → refl , ↻-renₖ-eval r (x .snd) e  ; (fsuc i) → eq i })


--------------------------------------------------------------------------------
-- Substitution lemma
-- 
-- Evaluation commutes with syntactic substitution

↻-subₖ-eval : ∀ (τ : Type Δ κ) {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →
                        (σ : Substitutionₖ Δ Δ₁) → 
                    eval (subₖ σ τ) η₁ ≋ eval τ (λ x → eval (σ x) η₂)
↻-subₖ-eval-pred : ∀ (π : Pred Type Δ R[ κ ]) {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →
                        (σ : Substitutionₖ Δ Δ₁) → 
                    evalPred (subPredₖ σ π) η₁ ≡ evalPred π (λ x → eval (σ x) η₂)
↻-subₖ-evalRow : ∀ (ρ : SimpleRow Type Δ R[ κ ]) {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →
                   (σ : Substitutionₖ Δ Δ₁) → 
                   evalRow (subRowₖ σ ρ) η₁ ≋R evalRow ρ (λ x → eval (σ x) η₂)

↻-subₖ-eval-pred (ρ₁ · ρ₂ ~ ρ₃) e σ rewrite 
    reify-≋ (↻-subₖ-eval ρ₁ e σ) 
  | reify-≋ (↻-subₖ-eval ρ₂ e σ) 
  | reify-≋ (↻-subₖ-eval ρ₃ e σ) = refl
↻-subₖ-eval-pred (ρ₁ ≲ ρ₂) e σ rewrite
    reify-≋ (↻-subₖ-eval ρ₁ e σ) 
  | reify-≋ (↻-subₖ-eval ρ₂ e σ) = refl

↻-subₖ-eval (` α) e σ = idext e (σ α)
↻-subₖ-eval (`λ τ) {η₁} {η₂} e σ =  
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ 
        (subₖ (liftsₖ σ) τ) 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q)) 
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) 
        (subₖ (liftsₖ σ) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ idext (refl-≋ᵣ ∘ e) ∘ σ) q)) 
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) 
           ; (S x) → sym-≋ 
                       (renSem-comp-≋ ρ₁ ρ₂ 
                         (idext (refl-≋ᵣ ∘ e) (σ x)))})
        τ)) , 
  λ r q → 
    trans-≋ 
    (↻-subₖ-eval τ 
      (extend-≋ (ren-≋ r ∘ e) q) 
      (liftsₖ σ)) 
    (idext 
      (λ { Z →  refl-≋ᵣ q 
         ; (S x) → trans-≋ 
                     (↻-renₖ-eval S (σ x) (extend-≋ (ren-≋ r ∘ refl-≋ᵣ ∘ e) (refl-≋ᵣ q))) 
                     (sym-≋ (↻-renSem-eval r (σ x) (refl-≋ᵣ ∘ e)))})
      τ)  
↻-subₖ-eval (`∀ τ) e σ = cong (`∀) 
  (trans 
    (↻-subₖ-eval τ (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) (liftsₖ σ) ) 
    (idext 
      (λ { Z     → reflect-≋ refl 
         ; (S x) → trans-≋ 
                      (↻-renₖ-eval S (σ x) (extend-≋ (ren-≋ S ∘ refl-≋ᵣ ∘ e) (reflect-≋ refl))) 
                      (sym-≋ (↻-renSem-eval S (σ x) (refl-≋ᵣ ∘ e) )) }) 
      τ))
↻-subₖ-eval (τ₁ · τ₂) e σ = cong-App (↻-subₖ-eval τ₁ e σ) (↻-subₖ-eval τ₂ e σ) 
↻-subₖ-eval (τ₁ `→ τ₂) e σ = cong₂ _`→_ (↻-subₖ-eval τ₁ e σ) (↻-subₖ-eval τ₂ e σ)
↻-subₖ-eval (μ τ) e σ = cong μ (reify-≋ (↻-subₖ-eval τ e σ))
↻-subₖ-eval (π ⇒ τ) e σ = cong₂ _⇒_ (↻-subₖ-eval-pred π e σ) (↻-subₖ-eval τ e σ)
↻-subₖ-eval (lab l) e σ = refl
↻-subₖ-eval ⌊ τ₁ ⌋ e σ = cong ⌊_⌋ (↻-subₖ-eval τ₁ e σ)
↻-subₖ-eval Π e σ = Unif-Π , Unif-Π , λ r v → cong-Π v
↻-subₖ-eval Σ e σ = Unif-Σ , Unif-Σ , λ r v → cong-Σ v
↻-subₖ-eval (τ₁ <$> τ₂) e σ = cong-<$> (↻-subₖ-eval τ₁ e σ) (↻-subₖ-eval τ₂ e σ)
↻-subₖ-eval (⦅ ρ ⦆ _) {η₁} e σ = ↻-subₖ-evalRow ρ e σ
↻-subₖ-eval (ρ₂ ─ ρ₁) {η₁} e σ = cong-─V (↻-subₖ-eval ρ₂ e σ) (↻-subₖ-eval ρ₁ e σ)
↻-subₖ-eval (l ▹ τ) {η₁} {η₂} e σ with eval (subₖ σ l) η₁ | ↻-subₖ-eval l e σ  
... | ne x₁ | ih rewrite (sym ih) = refl , ↻-subₖ-eval τ e σ
... | lab l₁ | ih rewrite (sym ih) = refl , (λ { fzero → refl , ((↻-subₖ-eval τ e σ)) })

↻-subₖ-evalRow [] {η₁} e σ = refl , λ ()
↻-subₖ-evalRow (x ∷ ρ) {η₁} e σ with evalRow (subRowₖ σ ρ) η₁ | ↻-subₖ-evalRow ρ e σ 
... | n , P | refl , eq = 
  refl , λ { fzero   → refl , ↻-subₖ-eval (x .snd) e σ ; 
            (fsuc i) → eq i }

↻-eval-Kripke : ∀ (f : Type Δ₁ (κ₁ `→ κ₂)) → (r : Renamingₖ Δ₂ Δ₃) 
                {V₁ V₂ : SemType Δ₃ κ₁} → (V₁ ≋ V₂) → 
                {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →  
                eval f (renSem r ∘ η₁) id V₁ ≋ eval f η₂ r V₂
↻-eval-Kripke (` α) r v e = snd (snd (e α)) r v
↻-eval-Kripke (`λ f) r v {η₁} {η₂} e = 
  idext (λ { Z → v
           ; (S x) → renSem-id-≋ 
                      {V₁ = (renSem r ∘ η₁) x} 
                      {(renSem r ∘ η₂) x} 
                      (ren-≋ r (e x)) }) f
↻-eval-Kripke (f · a) r {V₁} {V₂} v {η₁} {η₂} e with 
    ↻-eval-Kripke f r {eval a (renSem r ∘ η₁)} {eval a (renSem r ∘ η₂)} (idext (ren-≋ r ∘ e) a) {η₁} {η₂} e
  | ↻-eval-Kripke f id {eval a η₁} {eval a η₂} (idext e a) e
... | (Unif-ρ₁ , Unif-ρ₂ , Ext-ρ) | (Unif-id₁ , Unif-id₂ , Ext-id) =
    trans-≋ 
      (Ext-ρ id v) 
      (sym-≋ (trans-≋ 
        (third ((fst ∘ snd) (idext e f) id r (eval a η₂) (eval a η₂) (refl-≋ᵣ (idext e a))) id (refl-≋ᵣ v)) 
        (third (third (idext (refl-≋ᵣ ∘ e) f) r (↻-renSem-eval r a (refl-≋ᵣ ∘ e))) id (refl-≋ᵣ v))))
↻-eval-Kripke Π r v e = cong-Π v
↻-eval-Kripke Σ r v e = cong-Σ v

--------------------------------------------------------------------------------
-- Evaluating a weakened typed in an extended environment is cancellative

weaken-extend : ∀ (τ : Type Δ₁ κ₁) → 
                  {η₁ η₂ : Env Δ₁ Δ₂} → 
                  Env-≋ η₁ η₂ → 
                  {V : SemType Δ₂ κ₂}  → 
                  V ≋ V →
                  eval (weakenₖ τ) (extende η₁ V) ≋ eval τ η₂
weaken-extend τ {η₁} {η₂} e {V} v = ↻-renₖ-eval S τ {extende η₁ V} {extende η₂ V} (extend-≋ e v)   

--------------------------------------------------------------------------------
-- The length of a reified row is the index of the row 

length-reify : (n : ℕ) (P : Fin n → Label × SemType Δ κ) → 
                 length (reifyRow (n , P)) ≡ n
length-reify zero P = refl
length-reify (suc n) P = cong suc (length-reify n (P ∘ fsuc))

--------------------------------------------------------------------------------
-- Length of a row is preserved by embedding

length-⇑ : ∀ (xs : SimpleRow NormalType Δ R[ κ ]) → 
            length (⇑Row xs) ≡ length xs
length-⇑ [] = refl
length-⇑ (x ∷ xs) = cong suc (length-⇑ xs)

-- Combining the two above 
length-⇑-reify : ∀ (n : ℕ) (P : Fin n → Label × SemType Δ κ) → 
                  length (⇑Row (reifyRow (n , P))) ≡ n
length-⇑-reify n P = trans (length-⇑ (reifyRow (n , P))) (length-reify n P)        

--------------------------------------------------------------------------------
--<$>V commutes over complement operators

↻-<$>V-compl₁ : ∀ (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              (λ {Δ} → F {Δ}) ≋ (λ {Δ} → G {Δ}) → 
              (n , P) ≋R (n , P') → 
              (m , Q) ≋R (m , Q') → 
              compl P Q .fst ≡ compl (overᵣ (G id) ∘ P') (overᵣ (G id) ∘ Q') .fst
↻-<$>V-compl₁ F G zero zero P P' Q Q' (_ , _ , Ext) (refl , PP) Q≋Q' = Q≋Q' .fst
↻-<$>V-compl₁ F G zero (suc m) P P' Q Q' (_ , _ , Ext) (refl , PP) Q≋Q' = refl
↻-<$>V-compl₁ F G (suc n) zero P P' Q Q' F≋G (refl , PP) Q≋Q' = cong suc (↻-<$>V-compl₁ F G n zero (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) Q≋Q')
↻-<$>V-compl₁ F G (suc n) (suc m) P P' Q Q' F≋G (refl , PP) (refl , QQ) with P fzero .fst ∈Row? Q | (overᵣ (G id) ∘ P') fzero .fst ∈Row? (overᵣ (G id) ∘ Q')
... | yes p | yes q  = ↻-<$>V-compl₁ F G n (suc m) (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ)
... | yes (i , eq) | no q  = ⊥-elim (q (i , trans (sym (PP fzero .fst)) (trans eq (QQ i .fst))))
... | no p | yes (i , eq)  = ⊥-elim (p (i , trans (PP fzero .fst) (trans eq (sym (QQ i .fst)))))
... | no p | no q  = cong suc (↻-<$>V-compl₁ F G n (suc m) (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ))


↻-<$>V-compl₂ : ∀ (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              (λ {Δ} → F {Δ}) ≋ (λ {Δ} → G {Δ}) → 
              (n , P) ≋R (n , P') → 
              (m , Q) ≋R (m , Q') → 
              compl (overᵣ (F id) ∘ P) (overᵣ (F id) ∘ Q) ≋R compl (overᵣ (G id) ∘ P') (overᵣ (G id) ∘ Q')
↻-<$>V-compl₂ F G n m P P' Q Q' F≋G@(_ , _ , Ext) (refl , PP) (refl , QQ) = 
  cong-compl 
    (overᵣ (F id) ∘ P) (overᵣ (G id) ∘ P') 
    (overᵣ (F id) ∘ Q) (overᵣ (G id) ∘ Q') 
    (λ i → (PP i .fst) , cong-App F≋G (PP i .snd)) 
    (λ i → (QQ i .fst) , cong-App F≋G (QQ i .snd))

lem : ∀ (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin (suc n) → Label × SemType Δ κ₁)
              (Q Q' : Fin m → Label × SemType Δ κ₁) → 
              (PP : ∀ i → P i ≋₂ P' i) → 
              (QQ : ∀ i → Q i ≋₂ Q' i) →
              (f : (λ {Δ} → F {Δ}) ≋ (λ {Δ} → G {Δ})) → 
              (pf : compl (P ∘ fsuc) Q .fst ≡ compl (overᵣ (G id) ∘ (P' ∘ fsuc)) (overᵣ (G id) ∘ Q') .fst) → 
              (i' : Fin
                (compl
                  (λ Δ₂ → P' (fsuc Δ₂) .fst , G (λ i₁ → i₁) (P' (fsuc Δ₂) .snd))
                  (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd)) .fst)) → 
              subst-Row pf
             (λ x₁ →
               compl (λ x₂ → P (fsuc x₂)) Q .snd x₁ .fst ,
             F (λ x₂ → x₂) (compl (λ x₂ → P (fsuc x₂)) Q .snd x₁ .snd))
            i'
          ≋₂
          compl
          (λ x₁ → P' (fsuc x₁) .fst , G (λ x₂ → x₂) (P' (fsuc x₁) .snd))
          (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd)) .snd i'
lem F G (suc n) m P P' Q Q' PP QQ f pf i' with 
     P (fsuc fzero) .fst ∈Row? Q 
    | P' (fsuc fzero) .fst ∈Row? (overᵣ (G id) ∘ Q') 
... | yes (j , eq) | yes q = lem F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' (PP ∘ fsuc) QQ f pf i'
... | yes (j , eq) | no q  = ⊥-elim (q (j , trans (sym (PP (fsuc fzero) .fst)) (trans eq (QQ j .fst))))
... | no q         | yes (j , eq)   = ⊥-elim (q (j , trans (PP (fsuc fzero) .fst) (trans eq (sym (QQ j .fst)))))
... | no _         | no _  with 
        compl (P ∘ fsuc ∘ fsuc) Q 
     | compl (λ x → (P' ∘ fsuc ∘ fsuc) x .fst , G id (P' (fsuc (fsuc x)) .snd))
             (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd))
     | lem F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' (PP ∘ fsuc) QQ f
lem F G (suc n) m P P' Q Q' PP QQ f refl fzero | no _ | no _ | h , H | j , J | e = PP (fsuc fzero) .fst , f .snd .snd id (PP (fsuc fzero) .snd)
lem F G (suc n) m P P' Q Q' PP QQ f refl (fsuc i') | no _ | no _ | h , H | j , J | e = e refl i'

↻-<$>V-─V : ∀ (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              {oP : OrderedRow (n , P)}
              {oP' : OrderedRow (n , P')}
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              {oQ : OrderedRow (m , Q)}
              {oQ' : OrderedRow (m , Q')} →
              (λ {Δ} → F {Δ}) ≋ (λ {Δ} → G {Δ}) → 
              (n , P) ≋R (n , P') → 
              (m , Q) ≋R (m , Q') → 
              (F <$>V (row (n , P) oP ─V row (m , Q) oQ)) ≋ 
              ((G <$>V row (n , P') oP') ─V (G <$>V row (m , Q') oQ'))
             
↻-<$>V-─V F G zero m P P' {oP} {oP'} Q Q' {oQ} {oQ'} F≋G P≋P' Q≋Q' = refl , (λ ())
↻-<$>V-─V F G (suc n) m P P' {oP} {oP'} Q Q' {oQ} {oQ'} F≋G (refl , PP) (refl , QQ) with
      P fzero .fst ∈Row? Q | P' fzero .fst ∈Row? (overᵣ (G id) ∘ Q') | PP fzero 
    | ↻-<$>V-compl₂ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ)
... | yes (i , eq) | yes (j , q) | e , d | fst-eq , snd-eq = 
  ↻-<$>V-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ) , 
  λ i' → lem F G n m P P' Q Q' PP QQ F≋G (↻-<$>V-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ)) i' 
... | yes (i , eq) | no q | e , d | cc = ⊥-elim (q (i , trans (sym e) (trans eq (QQ i .fst))))
... | no q | yes (i , eq) | e , d | cc = ⊥-elim (q (i , trans e (trans eq (sym (QQ i .fst)))))
... | no  p | no q | _ | compl₂ with 
       compl (P ∘ fsuc) Q 
    |  ↻-<$>V-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ) 
    | lem F G n m P P' Q Q' PP QQ F≋G (↻-<$>V-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≋G (refl , PP ∘ fsuc) (refl , QQ))
... | a | refl | lem₁ = refl , λ { fzero → (PP fzero .fst) , (F≋G .snd .snd id (PP fzero .snd)) ; (fsuc i) → lem₁ i }

--------------------------------------------------------------------------------
--


