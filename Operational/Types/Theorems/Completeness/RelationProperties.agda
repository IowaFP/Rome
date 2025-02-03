{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.RelationProperties where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Normal.Renaming as N
open import Rome.Operational.Types.Normal.Properties.Renaming as NTypeProps
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation

--------------------------------------------------------------------------------
-- Reflecting propositional equality of neutral types into semantic equality.
-- (Well kinded neutral types are in the logical relation.)

reflectNE-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflectNE τ₁ ≋ reflectNE τ₂
reflectNE-≋ {κ = ★} refl = refl
reflectNE-≋ {κ = L} refl = refl
reflectNE-≋ {κ = κ `→ κ₁} eq = eq
reflectNE-≋ {κ = R[ ★ ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ L ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ κ `→ κ₁ ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ R[ κ ] ]} {τ₁ = τ₁} refl = refl

--------------------------------------------------------------------------------
-- Reify semantic equality back to propositional equality

reify-≋  : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → reify τ₁ ≡ reify τ₂ 
reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ₁ `→ κ₂} {left τ₁} {left τ₂} refl = refl
reify-≋ {κ = κ₁ `→ κ₂} {right F} {right  G}
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflectNE-≋ refl)))
reify-≋ {κ = R[ ★ ]} sem-eq = sem-eq
reify-≋ {κ = R[ L ]} sem-eq = sem-eq
reify-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , left F)} {right (l₂ , left G)} (refl , refl) = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , right F)} {right (l₂ , right G)} (refl , unif-F , unif-G , Ext) = 
  cong row (cong (_▹_ l₁) (cong `λ (reify-≋ (Ext S (reflectNE-≋ refl)))))
reify-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ R[ κ ] ]} {right y} {right y₁} ( refl , sem-eq ) 
 rewrite reify-≋ sem-eq = refl

--------------------------------------------------------------------------------
-- related applicands yield related applications

cong-App : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
cong-App {V₁ = left x} {left .x} refl q = reflectNE-≋ (cong (x ·_) (reify-≋ q))
cong-App {V₁ = left x} {right y} () q
cong-App {V₁ = right y} {left x} () q
cong-App {V₁ = right F} {right G} (unif-F , unif-G , Ext) q = Ext id q           

cong-▹ : ∀ {L₁ L₂ : NormalType Δ L} → 
           _≋_ {κ = L} L₁ L₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (L₁ ▹V W₁) ≋ (L₂ ▹V W₂)
cong-▹ {κ₁ = ★} refl refl = refl
cong-▹ {κ₁ = L} refl refl = refl
cong-▹ {κ₁ = κ₁ `→ κ₂} refl {left x} {left x₁} w = refl , w
cong-▹ {κ₁ = κ₁ `→ κ₂} refl {right F} {right G} ≋W = 
  refl , ≋W
cong-▹ {κ₁ = R[ κ₁ ]} refl w = refl , w

--------------------------------------------------------------------------------
-- renaming respects ≋

ren-≋ : ∀ {V₁ V₂ : SemType Δ₁ κ} 
        (ρ : Renaming Δ₁ Δ₂) → 
        V₁ ≋ V₂ → 
        (renSem ρ V₁) ≋ (renSem ρ V₂)
ren-≋ {κ = ★} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = L} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = left _} {left _} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = right F} {right G} ρ₁ (unif-F , unif-G , Ext) = 
  (λ ρ₂ ρ₃ V₁  → unif-F (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  (λ ρ₂ ρ₃ V₁  → unif-G (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  λ ρ₃ q → Ext (ρ₃ ∘ ρ₁) q
ren-≋ {κ = R[ ★ ]} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = R[ L ]} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = left x} {left x₁} ρ refl = refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = right (l , left F)} {right (.l , left G)} ρ (refl , refl) = refl , refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = right (l , right F)} {right (.l , right G)} ρ₁
  (refl , q) = refl , ren-≋ {κ = κ₁ `→ κ₂} {V₁ = right F} {V₂ = right G}  ρ₁ q
ren-≋ {κ = R[ R[ κ ] ]} {V₁ = left _} {left _} ρ refl = refl
ren-≋ {κ = R[ R[ κ ] ]} {V₁ = right (l , F)} {right (.l , G)} ρ (refl , q) = refl , (ren-≋ {κ = R[ κ ]} ρ q)

--------------------------------------------------------------------------------
-- Renaming commutes with reflection of neutral types

--             
--            ren ρ 
-- Type Δ₁ κ -------------> Type Δ₂ κ 
--  |                        |
--  | reflectNE              | reflectNE
--  |                        |
--  V                        V 
-- SemType Δ₁ κ ----------> SemType Δ₂ κ
--               renSem ρ 

↻-ren-reflectNE  : 
  ∀ (ρ : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
    (renSem ρ (reflectNE τ)) ≋ (reflectNE (renNE ρ τ))
↻-ren-reflectNE {κ = ★} ρ τ = refl
↻-ren-reflectNE {κ = L} ρ τ = refl
↻-ren-reflectNE {κ = κ `→ κ₁} ρ τ = refl
↻-ren-reflectNE {κ = R[ ★ ]} ρ τ = refl
↻-ren-reflectNE {κ = R[ L ]} ρ τ = refl
↻-ren-reflectNE {κ = R[ κ `→ κ₁ ]} ρ τ = refl
↻-ren-reflectNE {κ = R[ R[ κ ] ]} ρ τ = refl

↻-ren-reflectNE-▹  : 
  ∀ (ρ : Renaming Δ₁ Δ₂) (l : NormalType Δ₁ L) (τ : NeutralType Δ₁ κ) → 
    _≋_ {κ = R[ κ ]} (renSem ρ (l ▹V (reflectNE τ)))  (N.ren ρ l ▹V (reflectNE (renNE ρ τ)))
↻-ren-reflectNE-▹ {κ = ★} ρ l τ = refl
↻-ren-reflectNE-▹ {κ = L} ρ l τ = refl
↻-ren-reflectNE-▹ {κ = κ `→ κ₁} ρ l τ = refl , refl
↻-ren-reflectNE-▹ {κ = R[ κ ]} ρ l τ = refl , (↻-ren-reflectNE ρ τ)

--------------------------------------------------------------------------------
-- Renaming commutes with reification.

--             
--                renSem ρ 
-- SemType Δ₁ κ -------------> SemType Δ₂ Κ
--  |                          |
--  | reify                    | reify
--  |                          |
--  V                          V 
-- NormalType Δ₁ κ ----------> NormalType Δ₂ κ
--                   ren ρ 

↻-ren-reify-kripke : ∀ (ρ : Renaming Δ₁ Δ₂) (F G : KripkeFunction Δ₁ κ₁ κ₂) → 
        _≋_ {Δ = Δ₁} {κ = κ₁ `→ κ₂} (right F) (right G) → 
        N.ren (lift ρ) (reify (F S (reflectNE (` Z)))) ≡ reify (renKripke ρ G S (reflectNE (` Z)))
↻-ren-reify : ∀ {Δ₁} {Δ₂} {κ} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≋ V₂ →  N.ren ρ (reify V₁) ≡ reify (renSem ρ V₂)

↻-ren-reify-kripke {κ₁ = κ₁} {κ₂} ρ F G q@(Unif-F , Unif-G , Ext) = (trans 
    (↻-ren-reify (lift ρ) (Ext S (reflectNE-≋ (refl {x = ` Z})))) 
    (reify-≋ 
      ((renSem (lift ρ) (G S (reflectNE (` Z)))) 
      ≋⟨ (Unif-G S (lift ρ) _ _ (reflectNE-≋ refl)) ⟩ 
      ((G (λ x → lift ρ (S x)) (renSem (lift ρ) (reflectNE (` Z)))) 
      ≋⟨ (cong-App 
          {κ₁ = κ₁} {κ₂ = κ₂} 
          {V₁ = (renSem {κ = κ₁ `→ κ₂} (S ∘ ρ) (right G))} 
          {V₂ = (renSem {κ = κ₁ `→ κ₂} (S ∘ ρ) (right G))}  
          ((λ ρ₁ ρ₂ v → Unif-G (ρ₁ ∘ S ∘ ρ) ρ₂ v) , 
           (λ ρ₁ ρ₂ v → Unif-G (ρ₁ ∘ S ∘ ρ) ρ₂ v) , 
           (λ ρ' q' →  (snd (snd G≋G)) (ρ' ∘ S ∘ ρ) q'))
          {W₂ = (reflectNE (` Z))} 
          (↻-ren-reflectNE (lift ρ) (` Z))) ⟩∎))))
  where
    G≋G : _≋_ {κ = κ₁ `→ κ₂} (right G) (right G)
    G≋G = refl-≋ₗ {κ = κ₁ `→ κ₂} {V₁ = right G} {V₂ = right F} (sym-≋ {κ = κ₁ `→ κ₂} {τ₁ = right F} {τ₂ = right G} q)

↻-ren-reify {κ = ★} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = L} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = κ₁ `→ κ₂} ρ {left _} {left _} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{right F} g@{right G} q@(Unif-F , Unif-G , Ext) = 
  cong `λ 
  (↻-ren-reify-kripke ρ F G q)
↻-ren-reify {κ = R[ ★ ]} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = R[ L ]} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = R[ κ `→ κ₁ ]} ρ {left x} {left x₁} refl = refl
↻-ren-reify {κ = R[ κ `→ κ₁ ]} ρ {right (l , left f)} {right (.l , left g)} (refl , refl) = refl
↻-ren-reify {κ = R[ κ₁ `→ κ₂ ]} ρ {right (l , f@(right F))} {right (.l , g@(right G))} (refl , q@(Unif-F , Unif-G , Ext)) = 
  cong row (cong₂ _▹_ refl (cong `λ (↻-ren-reify-kripke ρ F G q)))
↻-ren-reify {κ = R[ R[ κ ] ]} ρ {left _} {left _} refl = refl
↻-ren-reify {κ = R[ R[ κ ] ]} ρ {right (l , τ₁)} {right (.l , τ₂)} (refl , q) = cong row (cong₂ _▹_ refl (↻-ren-reify ρ q))

--------------------------------------------------------------------------------
-- Renaming commutes with application.

↻-ren-app : ∀ (ρ : Renaming Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≋_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≋ V₂ →  
                renSem ρ (F ·V V₁) ≋ (renSem {κ = κ₁ `→ κ₂} ρ G ·V renSem ρ V₂)
↻-ren-app {κ₂ = ★} ρ {left x} {right y} () r
↻-ren-app {κ₂ = ★} ρ {right y} {left x} () r
↻-ren-app {κ₂ = L} ρ {left x} {right y} () r
↻-ren-app {κ₂ = L} ρ {right y} {left x} () r
↻-ren-app {κ₂ = ★} ρ {left x} {left .x} refl r = 
  cong (ne ∘ (renNE ρ x ·_)) (trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))
↻-ren-app {κ₂ = L} ρ {left x} {left .x} refl r = 
  cong (ne ∘ (renNE ρ x ·_)) (trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))
↻-ren-app {κ₂ = κ₂ `→ κ₃} ρ {left τ} {left .τ} refl r = 
  cong (renNE ρ τ ·_) ((trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r))))
↻-ren-app {κ₂ = R[ ★ ]} ρ {left f} {left .f} refl r = 
  cong ne (cong (renNE ρ f ·_) ((trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))))
↻-ren-app {κ₂ = R[ L ]} ρ {left f} {left .f} refl r = 
  cong ne (cong (renNE ρ f ·_) ((trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))))
↻-ren-app {κ₂ = R[ κ₂ `→ κ₃ ]} ρ {left f} {left .f} refl r = 
  cong (renNE ρ f ·_) (trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))
↻-ren-app {κ₂ = R[ R[ κ₂ ] ]} ρ {left f} {left .f} refl r = 
  cong (renNE ρ f ·_) (trans (↻-ren-reify ρ (refl-≋ₗ r)) (reify-≋ (ren-≋ ρ r)))
↻-ren-app {κ₂ = κ₂} ρ {right F} {right G} (Unif-F , Unif-G , Ext) {V₁} {V₂} r = 
  trans-≋ (Unif-F id ρ V₁ V₂ r) ((Ext ρ (ren-≋ ρ (refl-≋ₗ (sym-≋ r)))))
              

--------------------------------------------------------------------------------
-- - Renaming commutes with labeled rows (↻-ren-▹)
-- - Renaming under labeled rows respects functor composition laws (renSem-comp-▹; implied by ↻-ren-▹)
-- - Renaming commutes with labeled rows housing applications of Kripke functions (ren-comp-Kripke-▹)

↻-ren-▹ : ∀ (ρ : Renaming Δ₁ Δ₂) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
                   V₁ ≋ V₂ → renSem ρ (l ▹V V₁) ≋ (N.ren ρ l ▹V renSem ρ V₂)
↻-ren-▹ {κ = ★} ρ l V .V refl = refl
↻-ren-▹ {κ = L} ρ l V .V refl = refl
↻-ren-▹ {κ = κ₁ `→ κ₂} ρ l (left f) (left .f) refl = refl , refl
↻-ren-▹ {κ = κ₁ `→ κ₂} ρ₁ l (right F) (right G) (Unif-F , Unif-G , Ext) = 
  refl ,
  (λ ρ₂ ρ₃ → Unif-F (ρ₂ ∘ ρ₁) ρ₃) ,
  ((λ ρ₂ ρ₃ → Unif-G (ρ₂ ∘ ρ₁) ρ₃)) , 
  λ ρ₂ → Ext (ρ₂ ∘ ρ₁)
↻-ren-▹ {κ = R[ κ ]} ρ l V₁ V₂ q = refl , (ren-≋ ρ q)

renSem-comp-▹ : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
                   V₁ ≋ V₂ → renSem ρ₂ ((N.ren ρ₁ l) ▹V renSem ρ₁ V₁) ≋ (N.ren (ρ₂ ∘ ρ₁) l ▹V renSem (ρ₂ ∘ ρ₁) V₂)
renSem-comp-▹ ρ₁ ρ₂ l V₁ V₂ q = 
  trans-≋ 
  (↻-ren-▹ ρ₂ (N.ren ρ₁ l) (renSem ρ₁ V₁) (renSem ρ₁ V₂) (ren-≋ ρ₁ q)) 
  (cong-▹ (sym (ren-comp ρ₁ ρ₂ l)) (sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (sym-≋ q)))))

ren-comp-Kripke-▹ : ∀ {ρ₁ : Renaming Δ₁ Δ₂} {ρ₂ : Renaming Δ₂ Δ₃} (l : NormalType Δ₁ L) (F G : KripkeFunction Δ₁ κ₁ κ₂) → 
                    (V₁ V₂ : SemType Δ₂ κ₁) → V₁ ≋ V₂ → _≋_ {κ = κ₁ `→ κ₂} (right F)  (right G) → 
                    renSem ρ₂ (N.ren ρ₁ l ▹V F ρ₁ V₁) ≋ (N.ren (ρ₂ ∘ ρ₁) l ▹V G (ρ₂ ∘ ρ₁) (renSem ρ₂ V₂))
ren-comp-Kripke-▹ {κ₁ = κ₁} {κ₂} {ρ₁} {ρ₂} l F G V₁ V₂ q (Unif-F , Unif-G , Ext) rewrite sym (ren-id (N.ren ρ₁ l)) | sym (renSem-id (F ρ₁ V₁)) = 
     trans-≋ 
      (renSem-comp-▹ id ρ₂ (N.ren ρ₁ l) (F ρ₁ V₁) (G ρ₁ V₂) (Ext ρ₁ q)) 
      (cong-▹ (sym (ren-comp ρ₁ ρ₂ l)) (Unif-G ρ₁ (ρ₂ ∘ id) V₂ V₂ (refl-≋ₗ (sym-≋ q))))

--------------------------------------------------------------------------------
-- - Uniformity is preserved under renaming (ren-Uniform)
--   (This is actually just what uniformity means.)

ren-Uniform : ∀ {F : KripkeFunction Δ₁ κ₁ κ₂} → (ρ : Renaming Δ₁ Δ₂) → Uniform F → Uniform (renKripke ρ F) 
ren-Uniform ρ Unif-F ρ₁ ρ₂ V₁ V₂ q = Unif-F (ρ₁ ∘ ρ) ρ₂ V₁ V₂ q

--------------------------------------------------------------------------------
-- - Renaming commutes with π (↻-ren-π)
-- - π is congruent w.r.t. semantic equivalence (cong-π)
-- - Neutral functions f and Kripke functions F are uniform under λ x. π (l ▹ F x)
--   (Auxilliary lemmas reused a bunch)
-- - Π applied to neutral types are semantically equivalent to themselvse (refl-πNE)

↻-ren-π : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → V₁ ≋ V₂ → renSem ρ (π V₁) ≋ π (renSem ρ V₂) 
cong-π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → τ₁ ≋ τ₂ → π τ₁ ≋ π τ₂
Unif-NE-π▹· : ∀ (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) →
            Uniform (λ ρ' v → π (N.ren ρ' l ▹V reflectNE (renNE ρ' f · reify v)))
Unif-π▹· : ∀ (l : NormalType Δ L) (F : KripkeFunction Δ κ₁ κ₂) → _≋_ {κ = κ₁ `→ κ₂} (right F)  (right F) →             
              Uniform (λ ρ' v → π (N.ren ρ' l ▹V F ρ' v))
refl-πNE : ∀ {Δ}{κ} → (x : NeutralType Δ R[ κ ]) → πNE x ≋ πNE x

refl-πNE {κ = ★} x = refl
refl-πNE {κ = L} x = refl
refl-πNE {κ = κ `→ κ₁} x = refl
refl-πNE {κ = R[ ★ ]} x = refl
refl-πNE {κ = R[ L ]} x = refl
refl-πNE {κ = R[ κ `→ κ₁ ]} x = refl
refl-πNE {κ = R[ R[ κ ] ]} x = refl

↻-ren-π {★} ρ (ne x) V₂ refl = refl
↻-ren-π {★} ρ (row ρ₁) V₂ refl = refl
↻-ren-π {L} ρ (ne x) V₂ refl = refl
↻-ren-π {L} ρ (row ρ₁) V₂ refl = refl
↻-ren-π {κ `→ κ₁} ρ (left f) (left .f) refl = refl
↻-ren-π {κ₁ `→ κ₂} ρ (right (l , left F)) (right (.l , left G)) (refl , refl) = 
  ren-Uniform ρ (Unif-NE-π▹· l F) , Unif-NE-π▹· (N.ren ρ l) (renNE ρ F) , 
  λ _ x → cong-π (cong-▹ (ren-comp _ _ _) (reflectNE-≋ (cong₂ _·_ (ren-comp-ne _ _ _) (reify-≋ x))))
↻-ren-π {κ `→ κ₁} ρ (right (l , right F)) (right (.l , right G)) (refl , Unif-F , Unif-G , Ext) = 
  ren-Uniform ρ (Unif-π▹· l F (Unif-F , Unif-F , refl-Extₗ Ext)) , 
  Unif-π▹· (N.ren ρ l) (renKripke ρ G) ((ren-Uniform ρ Unif-G) , ((ren-Uniform ρ Unif-G) , (λ ρ₁ x → refl-Extᵣ Ext (ρ₁ ∘ ρ) x ))) , 
  λ ρ₁ x → cong-π (cong-▹ (ren-comp _ _ _) (Ext (ρ₁ ∘ ρ) x))
↻-ren-π {R[ ★ ]} ρ (left _) (left _) refl = refl
↻-ren-π {R[ ★ ]} ρ (right (l , ne _)) (right (.l , .(ne _))) (refl , refl) = refl
↻-ren-π {R[ ★ ]} ρ (right (l , row _)) (right (.l , .(row _))) (refl , refl) = refl
↻-ren-π {R[ L ]} ρ (left _) (left _) refl = refl
↻-ren-π {R[ L ]} ρ (right (l , ne _)) (right (.l , .(ne _))) (refl , refl) = refl
↻-ren-π {R[ L ]} ρ (right (l , row _)) (right (.l , .(row _))) (refl , refl) = refl
↻-ren-π {R[ κ₁ `→ κ₂ ]} ρ (left x) (left x₁) refl = refl
↻-ren-π {R[ κ₁ `→ κ₂ ]} ρ (right (l , left F)) (right (.l , left G)) (refl , refl) = refl , refl
↻-ren-π {R[ κ₁ `→ κ₂ ]} ρ (right (l , right (l' , left F))) (right (.l , right (.l' , left .F))) (refl , refl , refl) = 
  refl , ↻-ren-π {κ₁ `→ κ₂} ρ (right (l' , left F)) (right (l' , left F)) (refl , refl)
↻-ren-π {R[ κ₁ `→ κ₂ ]} ρ (right (l , right (l' , right F))) (right (.l , right (.l' , right G))) (refl , refl , q) = 
  refl , ↻-ren-π {κ₁ `→ κ₂} ρ (right (l' , right F)) (right (l' , right G)) (refl , q)
↻-ren-π {R[ R[ κ ] ]} ρ (left _) (left _) refl = refl
↻-ren-π {R[ R[ ★ ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) = refl , refl
↻-ren-π {R[ R[ L ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) = refl , refl
↻-ren-π {R[ R[ κ `→ κ₁ ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) = refl , refl
↻-ren-π {R[ R[ R[ κ ] ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) = refl , refl
↻-ren-π {R[ R[ κ ] ]} ρ (right (l , right (l' , τ₁))) (right (.l , right (.l' , τ₂))) (refl , refl , q) = 
  refl , ↻-ren-π ρ (right (l' , τ₁)) (right (l' , τ₂)) (refl , q)

Unif-NE-π▹· l f ρ₁ ρ₂ V₁ V₂ q = 
  (renSem ρ₂ (π (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))))
  ≋⟨ 
      ↻-ren-π ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁)) (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))  
      (cong-▹ refl (reflectNE-≋ refl)) 
    ⟩ 
  (π (renSem ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))))
  ≋⟨ cong-π {τ₂ = (N.ren (λ x → ρ₂ (ρ₁ x)) l ▹V reflectNE (renNE (λ x → ρ₂ (ρ₁ x)) f · reify (renSem ρ₂ V₂)))} 
      (renSem ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁)) 
      ≋⟨ 
        ↻-ren-reflectNE-▹ ρ₂ (N.ren ρ₁ l) (renNE ρ₁ f · reify V₁) 
        ⟩ 
      cong-▹ (sym (ren-comp _ _ _)) (reflectNE-≋ (cong₂ _·_ (sym (ren-comp-ne _ _ _)) (↻-ren-reify ρ₂ q)))) 
    ⟩ 
  cong-π (cong-▹ refl (reflectNE-≋ refl))

Unif-π▹· l F e@(Unif-F , _ , Ext) ρ₁ ρ₂ V₁ V₂ q = 
  renSem ρ₂ (π (N.ren ρ₁ l ▹V F ρ₁ V₁)) 
  ≋⟨ (↻-ren-π ρ₂ (N.ren ρ₁ l ▹V F ρ₁ V₁) (N.ren ρ₁ l ▹V F ρ₁ V₁) (cong-▹ refl (Ext ρ₁ (refl-≋ₗ q)))) ⟩ 
  cong-π (ren-comp-Kripke-▹ l F F V₁ V₂ q (Unif-F , Unif-F , Ext))

cong-π {κ = ★} e = cong (π {κ = ★}) e
cong-π {κ = L} e = cong (π {κ = L}) e
cong-π {κ = κ₁ `→ κ₂} {left x} {left x₁} refl = refl
cong-π {κ = κ₁ `→ κ₂} {right (l , left f)} {right (.l , left .f)} (refl , refl) = 
  Unif-NE-π▹· l f , 
  Unif-NE-π▹· l f , 
  λ ρ q → (cong-π (cong-▹ refl (reflectNE-≋ ((cong₂ _·_ refl (reify-≋ q))))))

cong-π {κ = κ₁ `→ κ₂} {right (l , right F)} {right (l , right G)} (refl , e@(Unif-F , Unif-G , Ext)) = 
  Unif-π▹· l F (Unif-F , (Unif-F , refl-Extₗ Ext)) ,
  Unif-π▹· l G (Unif-G , (Unif-G , refl-Extᵣ Ext)),
  λ ρ x → cong-π (cong-▹ refl (Ext ρ x))
cong-π {κ = R[ ★ ]} {left x} {left x₁} refl = refl
cong-π {κ = R[ L ]} {left x} {left x₁} refl = refl
cong-π {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
cong-π {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
cong-π {κ = R[ ★ ]} {right (l , τ)} {right (.l , τ')} (refl , refl) = refl
cong-π {κ = R[ L ]} {right (l , τ)} {right (.l , τ')} (refl , refl) = refl
cong-π {κ = R[ κ₁ `→ κ₂ ]} {right (l , left x)} {right (.l , left x₁)} (refl , refl) = refl , refl
cong-π {κ = R[ κ₁ `→ κ₂ ]} {right (l , right (l' , left f))} {right (.l , right (l' , left .f))} (refl , refl , refl) = 
  refl , cong-π {κ = κ₁ `→ κ₂} {right (l' , left f)} {right (l' , left f)} (refl , refl)
cong-π {κ = R[ κ₁ `→ κ₂ ]} {right (l , right (l' , right F))} {right (.l , right (l' , right G))} (refl , refl , q) = 
  refl , cong-π {κ = κ₁ `→ κ₂} {right (l' , right F)} {right (l' , right G)} (refl , q)
cong-π {κ = R[ R[ κ ] ]} {right (l , left x)} {right (.l , left .x)} (refl , refl) = refl , refl-πNE x
cong-π {κ = R[ R[ κ ] ]} {right (l , right (l' , F))} {right (.l , right (.l' , G))} (refl , refl , q) = refl , cong-π (refl , q)

-- --------------------------------------------------------------------------------
-- π (which does not use its renaming) is uniform.


Unif-π : ∀ {Δ} {κ} → Uniform (π-Kripke {Δ = Δ} {κ = κ})
Unif-π {κ = κ} ρ₁ = ↻-ren-π {κ = κ}

--------------------------------------------------------------------------------
-- id extension
--
-- Lemma needed for semantic renaming commutation theorem.
-- States that if we evaluate a single term in related environments, we get related results.
-- 
-- Mutually recursive with commutativity of semantic renaming and evaluation (↻-ren-eval):

--            eval in (renSem (ρ ∘ η₂))
--  Type Δ₁ κ  ------
--  |                \            
--  | eval in η₁       \          
--  |                    \          
--  V                      V        
-- NormalType Δ₂ κ ----------> SemType Δ₂ κ
--                  renSem ρ 


↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)
↻-ren-eval-pred : ∀ (ρ : Renaming Δ₂ Δ₃) (π : Pred Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (N.renPred ρ (evalPred π η₁)) ≡ evalPred π (renSem ρ ∘ η₂)
idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
idext-pred : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (π : Pred Δ₁ R[ κ ]) →
               evalPred π η₁ ≡ evalPred π η₂

↻-ren-eval-pred ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} P rewrite 
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-ren-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-ren-eval ρ ρ₂ P)  
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₃) | reify-≋ (↻-ren-eval ρ ρ₃ P)  = refl
↻-ren-eval-pred ρ (ρ₁ ≲ ρ₂) P rewrite
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-ren-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-ren-eval ρ ρ₂ P)  = refl

↻-ren-eval ρ Unit e = refl
↻-ren-eval {κ = κ} ρ (` α) e = ren-≋ ρ (e α)
↻-ren-eval ρ₁ (`λ τ) {η₁} {η₂} e = 
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-ren-eval ρ₃ τ (extend-≋ {η₂ = renSem (ρ₂ ∘ ρ₁) ∘ η₂}  (λ x → ren-≋ (ρ₂ ∘ ρ₁) (e x)) v)) 
      (idext (λ { Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) ; (S x) → sym-≋ (ren-comp-≋ (ρ₂ ∘ ρ₁) ρ₃ (e x)) }) τ)) ,
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-ren-eval ρ₃ τ (extend-≋ {η₂ = renSem ρ₂ ∘ (renSem ρ₁ ∘ η₂)}  (λ x → ren-≋ ρ₂ (sym-≋ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x)))))) v)) 
      (idext 
        (λ {     Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) 
           ; (S x) → sym-≋ (ren-comp-≋ ρ₂ ρ₃ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x))))) }) τ)) ,
  λ ρ₂ q → idext (λ { Z → q ; (S x) → ren-comp-≋ ρ₁ ρ₂ (e x) }) τ
↻-ren-eval {κ = .κ₂} ρ (_·_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {η₁} {η₂} e = 
  trans-≋
    (↻-ren-app ρ (idext (refl-≋ₗ ∘ e) τ₁) (idext (refl-≋ₗ ∘ e) τ₂))     
    (cong-App (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e))
↻-ren-eval ρ (τ₁ `→ τ₂) e = cong₂ _`→_ (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)
↻-ren-eval ρ (`∀ κ τ) {η₁} {η₂} e = cong (`∀ κ) 
  (trans 
    (↻-ren-eval (lift ρ) τ {↑e η₁} {↑e η₂} 
      (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl))) 
    (idext E τ))
  where
    E : Env-≋ (renSem (lift ρ) ∘ ↑e {κ = κ} η₂) (↑e (renSem ρ ∘ η₂))
    E Z = ↻-ren-reflectNE (lift ρ) (` Z)
    E (S x) = 
      trans-≋ 
        (sym-≋ (ren-comp-≋ S (lift ρ) (refl-≋ₗ (sym-≋ (e x))))) 
        (ren-comp-≋ ρ S (refl-≋ᵣ (e x)))
↻-ren-eval ρ (μ τ) {η₁} {η₂} e = cong μ 
  (trans 
    (↻-ren-reify ρ {eval τ η₁} {eval τ η₂} (idext e τ)) 
    (reify-≋ (↻-ren-eval ρ τ (refl-≋ᵣ ∘ e))))
↻-ren-eval ρ (π ⇒ τ) e = cong₂ _⇒_ (↻-ren-eval-pred ρ π e) (↻-ren-eval ρ τ e)
↻-ren-eval ρ (lab l) e = refl
↻-ren-eval ρ (l ▹ τ) {η₁} {η₂} e = 
  trans-≋ 
    (ren-≋ {V₁ = (eval l η₁ ▹V eval τ η₁)} {V₂ = (eval l η₁ ▹V eval τ η₂)} ρ (cong-▹ refl (idext e τ))) 
    (trans-≋ 
      (↻-ren-▹ ρ (eval l η₁) (eval τ η₂) (eval τ η₂) (refl-≋ₗ (sym-≋ (idext e τ)))) 
      (cong-▹ (↻-ren-eval ρ l e) (↻-ren-eval ρ τ (refl-≋ₗ ∘ sym-≋ ∘ e))))
↻-ren-eval ρ ⌊ τ ⌋ e = cong ⌊_⌋ (↻-ren-eval ρ τ e)
↻-ren-eval ρ Π e = Unif-π , Unif-π , (λ ρ₁ x → cong-π x) 
↻-ren-eval ρ Σ e = {!   !}
↻-ren-eval ρ (τ <$> τ₁) e = {!   !}

idext-pred e (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂)) 
  | sym (reify-≋ (idext e ρ₃))  = refl
idext-pred e (ρ₁ ≲ ρ₂) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂))  = refl

idext {κ = κ} e Unit = refl
idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-ren-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) τ)) ,
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-ren-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ sym-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) τ)) , 
  λ ρ q → idext (extend-≋ (ren-≋ ρ ∘ e) q) τ
idext {κ = ★} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
idext {κ = L} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
idext {κ = κ `→ κ₁} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
idext {κ = R[ κ ]} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (τ₁ `→ τ₂) = cong₂ _`→_ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (π ⇒ τ) = cong₂ _⇒_ (idext-pred e π) (idext e τ)
idext {κ = κ} e (`∀ κ₁ τ) = cong (`∀ κ₁) (idext (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) τ)
idext {κ = ★} {η₁} {η₂} e (μ τ) with eval τ η₁ | eval τ η₂ | reify-≋ (idext e τ)
... | left x | left x₁ | refl = refl
... | right F | right G | r = cong μ r
idext {κ = κ} e (lab x) = refl
idext {κ = R[ ★ ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
idext {κ = R[ L ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
idext {κ = R[ κ₁ `→ κ₂ ]} {η₁} {η₂} e (l ▹ τ) with eval τ η₁ | eval τ η₂ | idext e τ | reify-≋ (idext e τ)
... | left x | left y | ide | refl = (idext e l) , refl
... | right F | right G | ide | d = (idext e l) , ide
idext {κ = R[ R[ κ₁ ] ]} {η₁} {η₂} e (l ▹ τ) = (idext e l) , (idext e τ)
idext {κ = κ} e ⌊ τ ⌋ = cong ⌊_⌋ (idext e τ)
idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
  (λ { ρ₁ ρ₂ V₁ V₂ q → ↻-ren-π ρ₂ V₁ V₂ q }) , 
  ((λ { ρ₁ ρ₂ V₁ V₂ q → ↻-ren-π ρ₂ V₁ V₂ q })) , 
  λ ρ x → cong-π x 
idext {κ = κ} e Σ = {!   !}        
idext {κ = κ} e (τ <$> τ₁) = {!   !}        
