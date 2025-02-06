{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Commutativity where

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
open import Rome.Operational.Types.Theorems.Completeness.Congruence

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
↻-ren-reflectNE {κ = R[ κ ]} ρ τ = refl

↻-ren-reflectNE-▹  : 
  ∀ (ρ : Renaming Δ₁ Δ₂) (l : NormalType Δ₁ L) (τ : NeutralType Δ₁ κ) → 
    _≋_ {κ = R[ κ ]} (renSem {κ = R[ κ ]} ρ (l ▹V (reflectNE τ)))  (N.ren ρ l ▹V (reflectNE (renNE ρ τ)))
↻-ren-reflectNE-▹ ρ l τ = refl , (↻-ren-reflectNE ρ τ)

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
↻-ren-reify {κ = R[ κ ]} ρ {left x} {left _} refl = refl
↻-ren-reify {κ = R[ κ ]} ρ {right (l , _)} {right (_ , _)} (refl , q) = cong (row ∘ (N.ren ρ l ▹_)) (↻-ren-reify ρ q)

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with application.

↻-ren-app : ∀ (ρ : Renaming Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≋_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≋ V₂ →  
                renSem ρ (F ·V V₁) ≋ (renSem {κ = κ₁ `→ κ₂} ρ G ·V renSem ρ V₂)
↻-ren-app ρ {left f} {left g} refl {V₁} {V₂} r = 
  trans-≋ (↻-ren-reflectNE ρ (f · reify V₁)) (reflectNE-≋ (cong (renNE ρ f ·_) (↻-ren-reify ρ r)))
↻-ren-app ρ {right F} {right G} (Unif-F , Unif-G , Ext) {V₁} {V₂} r = 
  trans-≋ (Unif-F id ρ V₁ V₂ r) ((Ext ρ (ren-≋ ρ (refl-≋ₗ (sym-≋ r)))))

--------------------------------------------------------------------------------
-- - Renaming commutes with labeled rows (↻-ren-▹)
-- - Renaming under labeled rows respects functor composition laws (renSem-comp-▹; implied by ↻-ren-▹)
-- - Renaming commutes with labeled rows housing applications of Kripke functions (ren-comp-Kripke-▹)

↻-ren-▹ : ∀ (ρ : Renaming Δ₁ Δ₂) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
                   V₁ ≋ V₂ → _≋_ {κ = R[ κ ]} (renSem {κ = R[ κ ]} ρ (l ▹V V₁)) (N.ren ρ l ▹V renSem ρ V₂)
↻-ren-▹ {κ = κ} ρ l V₁ V₂ q = refl , (ren-≋ ρ q)

-- renSem-comp-▹ : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
--                    V₁ ≋ V₂ → _≋_ {κ = R[ κ ]} (renSem {κ = R[ κ ]} ρ₂ ((N.ren ρ₁ l) ▹V renSem ρ₁ V₁))  (N.ren (ρ₂ ∘ ρ₁) l ▹V renSem (ρ₂ ∘ ρ₁) V₂)
-- renSem-comp-▹ ρ₁ ρ₂ l V₁ V₂ q = (sym (ren-comp ρ₁ ρ₂ l)) , {!   !} 
--   -- trans-≋ 
--   -- (↻-ren-▹ ρ₂ (N.ren ρ₁ l) (renSem ρ₁ V₁) (renSem ρ₁ V₂) (ren-≋ ρ₁ q)) 
--   -- (cong-▹ (sym (ren-comp ρ₁ ρ₂ l)) (sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (sym-≋ q)))))

-- ren-comp-Kripke-▹ : ∀ {ρ₁ : Renaming Δ₁ Δ₂} {ρ₂ : Renaming Δ₂ Δ₃} (l : NormalType Δ₁ L) (F G : KripkeFunction Δ₁ κ₁ κ₂) → 
--                     (V₁ V₂ : SemType Δ₂ κ₁) → V₁ ≋ V₂ → _≋_ {κ = κ₁ `→ κ₂} (right F)  (right G) → 
--                     renSem ρ₂ (N.ren ρ₁ l ▹V F ρ₁ V₁) ≋ (N.ren (ρ₂ ∘ ρ₁) l ▹V G (ρ₂ ∘ ρ₁) (renSem ρ₂ V₂))
-- ren-comp-Kripke-▹ {κ₁ = κ₁} {κ₂} {ρ₁} {ρ₂} l F G V₁ V₂ q (Unif-F , Unif-G , Ext) rewrite sym (ren-id (N.ren ρ₁ l)) | sym (renSem-id (F ρ₁ V₁)) = 
--      trans-≋ 
--       (renSem-comp-▹ id ρ₂ (N.ren ρ₁ l) (F ρ₁ V₁) (G ρ₁ V₂) (Ext ρ₁ q)) 
--       (cong-▹ (sym (ren-comp ρ₁ ρ₂ l)) (Unif-G ρ₁ (ρ₂ ∘ id) V₂ V₂ (refl-≋ₗ (sym-≋ q))))

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with <$>

↻-ren-<$> : ∀ (ρ : Renaming Δ₁ Δ₂) 
            {V₁ V₂ : SemType Δ₁ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ₁ R[ κ₁ ]} → 
            _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (renSem {κ = R[ κ₂ ]} ρ (V₁ <$>V W₁)) (renSem {κ = κ₁ `→ κ₂} ρ V₂ <$>V renSem {κ = R[ κ₁ ]} ρ W₂)
↻-ren-<$> ρ {V₁} {V₂} v {left x} {left x₁} refl = cong (_<$> renNE ρ x) (↻-ren-reify ρ v)
↻-ren-<$> ρ {V₁} {V₂} v {right (l , τ₁)} {right (.l , τ₂)} (refl , q) = refl , (↻-ren-app ρ v q)

--------------------------------------------------------------------------------
-- - Renaming commutes with ξ
-- - ξ is congruent w.r.t. semantic equivalence 

open Xi
Unif-ξ : ∀ {Δ} {κ} (Ξ : Xi) → Uniform {Δ = Δ} {κ₁ = R[ κ ]} {κ₂ = κ} (ξ-Kripke Ξ)
cong-ξ : ∀ (Ξ : Xi) {κ} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → ξ Ξ τ₁ ≋ ξ Ξ τ₂

-- Unif-ξ Ξ ρ₁ ρ₂ (left x) (left x₁) refl  = 
--   trans-≋ 
--     (↻-ren-reflectNE ρ₂ (Ξ .ΞNE x)) 
--     (reflectNE-≋ (Ξ .ren-NE ρ₂ x))
-- Unif-ξ {κ = ★} Ξ ρ₁ ρ₂ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-★ ρ₂ (l ▹ τ)
-- Unif-ξ {κ = L} Ξ ρ₁ ρ₂ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-L ρ₂ (l ▹ τ)
-- Unif-ξ {κ = κ `→ κ₁} Ξ ρ₁ ρ₂ (right (l , F)) (right (.l , G)) (refl , v) = 
--   (λ ρ₃ ρ₄ V₁ V₂ x → 
--     trans-≋ 
--     (Unif-ξ Ξ ρ₃ ρ₄ (right (N.ren (ρ₃ ∘ ρ₂) l , renSem (ρ₃ ∘ ρ₂) F ·V V₁)) (right (N.ren (ρ₃ ∘ ρ₂) l , renSem (ρ₃ ∘ ρ₂) F ·V V₁)) (refl , {! (cong-App ? ?) !})) 
--     (cong-ξ Ξ {_} {τ₁ = (right
--        (N.ren ρ₄ (N.ren (λ x₁ → ρ₃ (ρ₂ x₁)) l) ,
--         renSem ρ₄ (renSem (λ x₁ → ρ₃ (ρ₂ x₁)) F ·V V₁)))} {τ₂ = (right
--        (N.ren (λ x₁ → ρ₄ (ρ₃ (ρ₂ x₁))) l ,
--         (renSem (λ x₁ → ρ₄ (ρ₃ (ρ₂ x₁))) F ·V renSem ρ₄ V₂)))}  ((sym (ren-comp (ρ₃ ∘ ρ₂) ρ₄ l)) , {!   !}))) , 
--   {!   !} , 
--   {!   !}
-- Unif-ξ {κ = R[ κ ]} Ξ ρ₁ ρ₂ (right (l , F)) (right (.l , G)) (refl , v) = refl , (Unif-ξ Ξ id ρ₂ F G v)

↻-ren-ξ : ∀ {Δ₁} {Δ₂} (Ξ : Xi) {κ : Kind} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          _≋_ {κ = R[ κ ]} V₁ V₂ → renSem ρ (ξ Ξ V₁) ≋ ξ Ξ (renSem {κ = R[ κ ]} ρ V₂) 


Unif-NE-ξ▹· : ∀ (Ξ : Xi) (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) →
            Uniform (λ ρ' v → ξ Ξ (N.ren ρ' l ▹V reflectNE (renNE ρ' f · reify v)))
Unif-ξ▹· : ∀ (Ξ : Xi) (l : NormalType Δ L) (F : KripkeFunction Δ κ₁ κ₂) → _≋_ {κ = κ₁ `→ κ₂} (right F)  (right F) →             
              Uniform (λ ρ' v → ξ Ξ (N.ren ρ' l ▹V F ρ' v))

open Xi
↻-ren-ξ Ξ {κ} ρ (left x) (left x₁) refl rewrite (sym (Ξ .ren-NE ρ x)) = ↻-ren-reflectNE ρ (Ξ .ΞNE x)
↻-ren-ξ Ξ {★} ρ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-★ ρ (l ▹ τ)
↻-ren-ξ Ξ {L} ρ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-L ρ (l ▹ τ)
↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (right (l , F)) (right (.l , G)) (refl , q) = 
  ren-Uniform {F = λ ρ₁ v → ξ Ξ (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V v))} ρ
    (λ ρ₁ ρ₂ V₁ V₂ q' → trans-≋ 
      (↻-ren-ξ Ξ ρ₂ 
        (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V V₁)) (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V V₁)) 
        (refl , cong-App {V₁ = renSem {κ = κ₁ `→ κ₂} ρ₁ F} {renSem {κ = κ₁ `→ κ₂} ρ₁ F} (ren-≋ ρ₁ (refl-≋ₗ q)) {V₁} {V₁} (refl-≋ₗ q'))) 
      (cong-ξ Ξ
         {τ₁ =
          right (N.ren ρ₂ (N.ren ρ₁ l) , renSem ρ₂ (renSem {κ = κ₁ `→ κ₂}  ρ₁ F ·V V₁))}
         {τ₂ =
          N.ren (λ x → ρ₂ (ρ₁ x)) l ▹V
          (renSem {κ = κ₁ `→ κ₂} (λ x → ρ₂ (ρ₁ x)) F ·V renSem ρ₂ V₂)}
         ((sym (ren-comp ρ₁ ρ₂ l)) , 
            trans-≋ 
              (↻-ren-app ρ₂ {renSem {κ = κ₁ `→ κ₂} ρ₁ F} {renSem {κ = κ₁ `→ κ₂} ρ₁ F} (ren-≋ ρ₁ (refl-≋ₗ q)) {V₁} {V₂} q') 
              (cong-App (sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ q))) (ren-≋ ρ₂ (refl-≋ᵣ q')))))) , 
  {!    !} , 
    {!   !}
↻-ren-ξ Ξ {R[ κ ]} ρ (right (l , τ₁)) (right (.l , τ₂)) (refl , q) = refl , (↻-ren-ξ Ξ ρ τ₁ τ₂ q)



-- ↻-ren-ξ Ξ {★} ρ (row ρ₁) V₂ refl rewrite ren-★ Ξ ρ ρ₁ = refl
-- ↻-ren-ξ Ξ {L} ρ (ne x) V₂ refl rewrite (Ξ .ren-NE ρ x) = refl
-- ↻-ren-ξ Ξ {L} ρ (row ρ₁) V₂ refl rewrite ren-L Ξ ρ ρ₁ = refl
-- ↻-ren-ξ Ξ {κ `→ κ₁} ρ (left f) (left .f) refl rewrite Ξ .ren-NE ρ f = refl
-- ↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (right (l , left F)) (right (.l , left G)) (refl , refl) = 
--   ren-Uniform ρ (Unif-NE-ξ▹· Ξ l F) , Unif-NE-ξ▹· Ξ (N.ren ρ l) (renNE ρ F) , 
--   λ _ x → cong-ξ Ξ (cong-▹ (ren-comp _ _ _) (reflectNE-≋ (cong₂ _·_ (ren-comp-ne _ _ _) (reify-≋ x))))
-- ↻-ren-ξ Ξ {κ `→ κ₁} ρ (right (l , right F)) (right (.l , right G)) (refl , Unif-F , Unif-G , Ext) = 
--   ren-Uniform ρ (Unif-ξ▹· Ξ l F (Unif-F , Unif-F , refl-Extₗ Ext)) , 
--   Unif-ξ▹· Ξ (N.ren ρ l) (renKripke ρ G) ((ren-Uniform ρ Unif-G) , ((ren-Uniform ρ Unif-G) , (λ ρ₁ x → refl-Extᵣ Ext (ρ₁ ∘ ρ) x ))) , 
--  λ ρ₁ x → cong-ξ Ξ (cong-▹ (ren-comp _ _ _) (Ext (ρ₁ ∘ ρ) x))
-- ↻-ren-ξ Ξ {R[ ★ ]} ρ (left x) (left _) refl rewrite (Ξ .ren-NE ρ x) = refl
-- ↻-ren-ξ Ξ {R[ ★ ]} ρ (right (l , ne x)) (right (.l , .(ne _))) (refl , refl) rewrite (Ξ .ren-NE ρ x) = refl
-- ↻-ren-ξ Ξ {R[ ★ ]} ρ (right (l , row r)) (right (.l , .(row r))) (refl , refl) rewrite (Ξ .ren-★ ρ r) = refl
-- ↻-ren-ξ Ξ {R[ L ]} ρ (left x) (left _) refl rewrite (Ξ .ren-NE ρ x)  = refl
-- ↻-ren-ξ Ξ {R[ L ]} ρ (right (l , ne x)) (right (.l , .(ne _))) (refl , refl) rewrite (Ξ .ren-NE ρ x) = refl
-- ↻-ren-ξ Ξ {R[ L ]} ρ (right (l , row r)) (right (.l , .(row _))) (refl , refl) rewrite (Ξ .ren-L ρ r) = refl
-- ↻-ren-ξ Ξ {R[ κ₁ `→ κ₂ ]} ρ (left x) (left _) refl rewrite (Ξ .ren-NE ρ x) = refl
-- ↻-ren-ξ Ξ {R[ κ₁ `→ κ₂ ]} ρ (right (l , left F)) (right (.l , left G)) (refl , refl) rewrite (Ξ .ren-NE ρ F) = refl , refl
-- ↻-ren-ξ Ξ {R[ κ₁ `→ κ₂ ]} ρ (right (l , right (l' , left F))) (right (.l , right (.l' , left .F))) (refl , refl , refl) = 
--   refl , ↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (right (l' , left F)) (right (l' , left F)) (refl , refl)
-- ↻-ren-ξ Ξ {R[ κ₁ `→ κ₂ ]} ρ (right (l , right (l' , right F))) (right (.l , right (.l' , right G))) (refl , refl , q) = 
--   refl , ↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (right (l' , right F)) (right (l' , right G)) (refl , q)
-- ↻-ren-ξ Ξ {R[ R[ κ ] ]} ρ (left f) (left _) refl rewrite (Ξ .ren-NE ρ f) = refl
-- ↻-ren-ξ Ξ {R[ R[ ★ ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) rewrite (Ξ .ren-NE ρ x) = refl , refl
-- ↻-ren-ξ Ξ {R[ R[ L ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) rewrite (Ξ .ren-NE ρ x) = refl , refl
-- ↻-ren-ξ Ξ {R[ R[ κ `→ κ₁ ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl) rewrite (Ξ .ren-NE ρ x) = refl , refl
-- ↻-ren-ξ Ξ {R[ R[ R[ κ ] ] ]} ρ (right (l , left x)) (right (l , left .x)) (refl , refl)  rewrite (Ξ .ren-NE ρ x) = refl , refl
-- ↻-ren-ξ Ξ {R[ R[ κ ] ]} ρ (right (l , right (l' , τ₁))) (right (.l , right (.l' , τ₂))) (refl , refl , q) = 
--   refl , ↻-ren-ξ Ξ ρ (right (l' , τ₁)) (right (l' , τ₂)) (refl , q)

-- Unif-NE-ξ▹· Ξ l f ρ₁ ρ₂ V₁ V₂ q = 
--   (renSem ρ₂ (ξ Ξ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))))
--   ≋⟨ 
--       ↻-ren-ξ Ξ ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁)) (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))  
--       (cong-▹ refl (reflectNE-≋ refl)) 
--     ⟩ 
--   (ξ Ξ (renSem ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁))))
--   ≋⟨ cong-ξ Ξ
--       (renSem ρ₂ (N.ren ρ₁ l ▹V reflectNE (renNE ρ₁ f · reify V₁)) 
--       ≋⟨ 
--         ↻-ren-reflectNE-▹ ρ₂ (N.ren ρ₁ l) (renNE ρ₁ f · reify V₁) 
--         ⟩ 
--       cong-▹ (sym (ren-comp _ _ _)) (reflectNE-≋ (cong₂ _·_ (sym (ren-comp-ne _ _ _)) (↻-ren-reify ρ₂ q)))) 
--     ⟩ 
--   cong-ξ Ξ (cong-▹ refl (reflectNE-≋ refl))

-- Unif-ξ▹· Ξ l F e@(Unif-F , _ , Ext) ρ₁ ρ₂ V₁ V₂ q = 
--   trans-≋
--     (↻-ren-ξ Ξ ρ₂ (N.ren ρ₁ l ▹V F ρ₁ V₁) (N.ren ρ₁ l ▹V F ρ₁ V₁) (cong-▹ refl (Ext ρ₁ (refl-≋ₗ q))))
--     (cong-ξ Ξ (ren-comp-Kripke-▹ l F F V₁ V₂ q (Unif-F , Unif-F , Ext)))

-- cong-ξ Ξ {κ = ★} e = cong (ξ {★} Ξ) e
-- cong-ξ Ξ {κ = L} e = cong (ξ {L} Ξ) e
-- cong-ξ Ξ {κ = κ₁ `→ κ₂} {left x} {left x₁} refl = refl
-- cong-ξ Ξ {κ = κ₁ `→ κ₂} {right (l , left f)} {right (.l , left .f)} (refl , refl) = 
--   Unif-NE-ξ▹· Ξ l f , 
--   Unif-NE-ξ▹· Ξ l f , 
--   λ ρ q → (cong-ξ Ξ (cong-▹ refl (reflectNE-≋ ((cong₂ _·_ refl (reify-≋ q))))))
-- cong-ξ Ξ {κ = κ₁ `→ κ₂} {right (l , right F)} {right (l , right G)} (refl , e@(Unif-F , Unif-G , Ext)) = 
--   Unif-ξ▹· Ξ l F (Unif-F , (Unif-F , refl-Extₗ Ext)) ,
--   Unif-ξ▹· Ξ l G (Unif-G , (Unif-G , refl-Extᵣ Ext)),
--   λ ρ x → cong-ξ Ξ (cong-▹ refl (Ext ρ x))
-- cong-ξ Ξ {κ = R[ ★ ]} {left x} {left x₁} refl = refl
-- cong-ξ Ξ {κ = R[ L ]} {left x} {left x₁} refl = refl
-- cong-ξ Ξ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
-- cong-ξ Ξ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
-- cong-ξ Ξ {κ = R[ ★ ]} {right (l , τ)} {right (.l , τ')} (refl , refl) = refl
-- cong-ξ Ξ {κ = R[ L ]} {right (l , τ)} {right (.l , τ')} (refl , refl) = refl
-- cong-ξ Ξ {κ = R[ κ₁ `→ κ₂ ]} {right (l , left x)} {right (.l , left x₁)} (refl , refl) = refl , refl
-- cong-ξ Ξ {κ = R[ κ₁ `→ κ₂ ]} {right (l , right (l' , left f))} {right (.l , right (l' , left .f))} (refl , refl , refl) = 
--   refl , cong-ξ Ξ {κ = κ₁ `→ κ₂} {right (l' , left f)} {right (l' , left f)} (refl , refl)
-- cong-ξ Ξ {κ = R[ κ₁ `→ κ₂ ]} {right (l , right (l' , right F))} {right (.l , right (l' , right G))} (refl , refl , q) = 
--   refl , cong-ξ Ξ {κ = κ₁ `→ κ₂} {right (l' , right F)} {right (l' , right G)} (refl , q)
-- cong-ξ Ξ {κ = R[ R[ κ ] ]} {right (l , left x)} {right (.l , left .x)} (refl , refl) = refl , reflectNE-≋ refl
-- cong-ξ Ξ {κ = R[ R[ κ ] ]} {right (l , right (l' , F))} {right (.l , right (.l' , G))} (refl , refl , q) = refl , cong-ξ Ξ (refl , q)

-- ---------------------------------------
-- -- instantiations for π

-- ↻-ren-π : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → V₁ ≋ V₂ → renSem ρ (π V₁) ≋ π (renSem ρ V₂) 
-- ↻-ren-π = ↻-ren-ξ Π-rec

-- cong-π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → τ₁ ≋ τ₂ → π τ₁ ≋ π τ₂
-- cong-π = cong-ξ Π-rec

-- Unif-NE-π▹· : ∀ (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) →
--             Uniform (λ ρ' v → π (N.ren ρ' l ▹V reflectNE (renNE ρ' f · reify v)))
-- Unif-NE-π▹· = Unif-NE-ξ▹· Π-rec

-- Unif-π▹· : ∀ (l : NormalType Δ L) (F : KripkeFunction Δ κ₁ κ₂) → _≋_ {κ = κ₁ `→ κ₂} (right F) (right F) →             
--               Uniform (λ ρ' v → π (N.ren ρ' l ▹V F ρ' v))
-- Unif-π▹· = Unif-ξ▹· Π-rec

-- Unif-π : ∀ {Δ} {κ} → Uniform (π-Kripke {Δ = Δ} {κ = κ})
-- Unif-π ρ₁ = ↻-ren-π

-- ---------------------------------------
-- -- instantiations for σ

-- ↻-ren-σ : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → V₁ ≋ V₂ → renSem ρ (σ V₁) ≋ σ (renSem ρ V₂) 
-- ↻-ren-σ = ↻-ren-ξ Σ-rec

-- cong-σ : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → τ₁ ≋ τ₂ → σ τ₁ ≋ σ τ₂
-- cong-σ = cong-ξ Σ-rec

-- Unif-NE-σ▹· : ∀ (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) →
--             Uniform (λ ρ' v → σ (N.ren ρ' l ▹V reflectNE (renNE ρ' f · reify v)))
-- Unif-NE-σ▹· = Unif-NE-ξ▹· Σ-rec

-- Unif-σ▹· : ∀ (l : NormalType Δ L) (F : KripkeFunction Δ κ₁ κ₂) → _≋_ {κ = κ₁ `→ κ₂} (right F) (right F) →             
--               Uniform (λ ρ' v → σ (N.ren ρ' l ▹V F ρ' v))
-- Unif-σ▹· = Unif-ξ▹· Σ-rec

-- Unif-σ : ∀ {Δ} {κ} → Uniform (σ-Kripke {Δ = Δ} {κ = κ})
-- Unif-σ ρ₁ = ↻-ren-σ

-- --------------------------------------------------------------------------------
-- -- id extension
-- --
-- -- States that if we evaluate a single term in related environments, we get related results.
-- -- 
-- -- Mutually recursive with commutativity of semantic renaming and evaluation (↻-ren-eval):

-- --            eval in (renSem (ρ ∘ η₂))
-- --  Type Δ₁ κ  ------
-- --  |                \            
-- --  | eval in η₁       \          
-- --  |                    \          
-- --  V                      V        
-- -- NormalType Δ₂ κ ----------> SemType Δ₂ κ
-- --                  renSem ρ 


-- ↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
--                   (Ρ : Env-≋ η₁ η₂) → (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)
-- ↻-ren-eval-pred : ∀ (ρ : Renaming Δ₂ Δ₃) (π : Pred Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₁ Δ₂} → 
--                   (Ρ : Env-≋ η₁ η₂) → (N.renPred ρ (evalPred π η₁)) ≡ evalPred π (renSem ρ ∘ η₂)
-- idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
--           eval τ η₁ ≋ eval τ η₂
-- idext-pred : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (π : Pred Δ₁ R[ κ ]) →
--                evalPred π η₁ ≡ evalPred π η₂

-- ↻-ren-eval-pred ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} P rewrite 
--     ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-ren-eval ρ ρ₁ P)
--   | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-ren-eval ρ ρ₂ P)  
--   | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₃) | reify-≋ (↻-ren-eval ρ ρ₃ P)  = refl
-- ↻-ren-eval-pred ρ (ρ₁ ≲ ρ₂) P rewrite
--     ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-ren-eval ρ ρ₁ P)
--   | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-ren-eval ρ ρ₂ P)  = refl

-- ↻-ren-eval ρ Unit e = refl
-- ↻-ren-eval {κ = κ} ρ (` α) e = ren-≋ ρ (e α)
-- ↻-ren-eval ρ₁ (`λ τ) {η₁} {η₂} e = 
--   (λ ρ₂ ρ₃ V₁ V₂ v → 
--     trans-≋ 
--       (↻-ren-eval ρ₃ τ (extend-≋ {η₂ = renSem (ρ₂ ∘ ρ₁) ∘ η₂}  (λ x → ren-≋ (ρ₂ ∘ ρ₁) (e x)) v)) 
--       (idext (λ { Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) ; (S x) → sym-≋ (ren-comp-≋ (ρ₂ ∘ ρ₁) ρ₃ (e x)) }) τ)) ,
--   (λ ρ₂ ρ₃ V₁ V₂ v → 
--     trans-≋ 
--       (↻-ren-eval ρ₃ τ (extend-≋ {η₂ = renSem ρ₂ ∘ (renSem ρ₁ ∘ η₂)}  (λ x → ren-≋ ρ₂ (sym-≋ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x)))))) v)) 
--       (idext 
--         (λ {     Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) 
--            ; (S x) → sym-≋ (ren-comp-≋ ρ₂ ρ₃ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x))))) }) τ)) ,
--   λ ρ₂ q → idext (λ { Z → q ; (S x) → ren-comp-≋ ρ₁ ρ₂ (e x) }) τ
-- ↻-ren-eval {κ = .κ₂} ρ (_·_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {η₁} {η₂} e = 
--   trans-≋
--     (↻-ren-app ρ (idext (refl-≋ₗ ∘ e) τ₁) (idext (refl-≋ₗ ∘ e) τ₂))     
--     (cong-App (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e))
-- ↻-ren-eval ρ (τ₁ `→ τ₂) e = cong₂ _`→_ (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)
-- ↻-ren-eval ρ (`∀ κ τ) {η₁} {η₂} e = cong (`∀ κ) 
--   (trans 
--     (↻-ren-eval (lift ρ) τ {↑e η₁} {↑e η₂} 
--       (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl))) 
--     (idext E τ))
--   where
--     E : Env-≋ (renSem (lift ρ) ∘ ↑e {κ = κ} η₂) (↑e (renSem ρ ∘ η₂))
--     E Z = ↻-ren-reflectNE (lift ρ) (` Z)
--     E (S x) = 
--       trans-≋ 
--         (sym-≋ (ren-comp-≋ S (lift ρ) (refl-≋ₗ (sym-≋ (e x))))) 
--         (ren-comp-≋ ρ S (refl-≋ᵣ (e x)))
-- ↻-ren-eval ρ (μ τ) {η₁} {η₂} e = cong μ 
--   (trans 
--     (↻-ren-reify ρ {eval τ η₁} {eval τ η₂} (idext e τ)) 
--     (reify-≋ (↻-ren-eval ρ τ (refl-≋ᵣ ∘ e))))
-- ↻-ren-eval ρ (π ⇒ τ) e = cong₂ _⇒_ (↻-ren-eval-pred ρ π e) (↻-ren-eval ρ τ e)
-- ↻-ren-eval ρ (lab l) e = refl
-- ↻-ren-eval ρ (l ▹ τ) {η₁} {η₂} e =
--   (trans-≋ 
--       (↻-ren-▹ ρ (eval l η₁) (eval τ η₁) (eval τ η₂) (idext e τ)) 
--       ((cong-▹ (↻-ren-eval ρ l e) (↻-ren-eval ρ τ (refl-≋ᵣ ∘ e)))))
-- ↻-ren-eval ρ ⌊ τ ⌋ e = cong ⌊_⌋ (↻-ren-eval ρ τ e)
-- ↻-ren-eval ρ Π e = Unif-π , Unif-π , (λ ρ₁ x → cong-π x) 
-- ↻-ren-eval ρ Σ e = Unif-σ , Unif-σ , (λ ρ₁ x → cong-σ x) 
-- ↻-ren-eval ρ (τ₁ <$> τ₂) {η₁} {η₂} e = 
--   trans-≋ 
--     (↻-ren-<$> ρ (idext e τ₁) (idext e τ₂)) 
--     (cong-<$> (↻-ren-eval ρ τ₁ (refl-≋ᵣ ∘ e)) (↻-ren-eval ρ τ₂ (refl-≋ᵣ ∘ e)))
-- idext-pred e (ρ₁ · ρ₂ ~ ρ₃) rewrite 
--     sym (reify-≋ (idext e ρ₁))
--   | sym (reify-≋ (idext e ρ₂)) 
--   | sym (reify-≋ (idext e ρ₃))  = refl
-- idext-pred e (ρ₁ ≲ ρ₂) rewrite 
--     sym (reify-≋ (idext e ρ₁))
--   | sym (reify-≋ (idext e ρ₂))  = refl

-- idext {κ = κ} e Unit = refl
-- idext {κ = ★} e (` x) = e x
-- idext {κ = L} e (` x) = e x
-- idext {κ = κ `→ κ₁} e (` x) = e x
-- idext {κ = R[ κ ]} e (` x) = e x
-- idext {κ = κ} e (`λ τ) = 
--   (λ ρ₁ ρ₂ V₁ V₂ q → 
--     trans-≋ 
--       (↻-ren-eval ρ₂ τ 
--         (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q))
--       (idext 
--         (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
--            ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) τ)) ,
--   (λ ρ₁ ρ₂ V₁ V₂ q → 
--     trans-≋ 
--       (↻-ren-eval ρ₂ τ 
--         (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ sym-≋ ∘ e) q))
--       (idext 
--         (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
--            ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) τ)) , 
--   λ ρ q → idext (extend-≋ (ren-≋ ρ ∘ e) q) τ
-- idext {κ = ★} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
-- idext {κ = L} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
-- idext {κ = κ `→ κ₁} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
-- idext {κ = R[ κ ]} e (τ₁ · τ₂) = cong-App (idext e τ₁) (idext e τ₂)
-- idext {κ = κ} e (τ₁ `→ τ₂) = cong₂ _`→_ (idext e τ₁) (idext e τ₂)
-- idext {κ = κ} e (π ⇒ τ) = cong₂ _⇒_ (idext-pred e π) (idext e τ)
-- idext {κ = κ} e (`∀ κ₁ τ) = cong (`∀ κ₁) (idext (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) τ)
-- idext {κ = ★} {η₁} {η₂} e (μ τ) with eval τ η₁ | eval τ η₂ | reify-≋ (idext e τ)
-- ... | left x | left x₁ | refl = refl
-- ... | right F | right G | r = cong μ r
-- idext {κ = κ} e (lab x) = refl
-- idext {κ = R[ ★ ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
-- idext {κ = R[ L ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
-- idext {κ = R[ κ₁ `→ κ₂ ]} {η₁} {η₂} e (l ▹ τ) with eval τ η₁ | eval τ η₂ | idext e τ | reify-≋ (idext e τ)
-- ... | left x | left y | ide | refl = (idext e l) , refl
-- ... | right F | right G | ide | d = (idext e l) , ide
-- idext {κ = R[ R[ κ₁ ] ]} {η₁} {η₂} e (l ▹ τ) = (idext e l) , (idext e τ)
-- idext {κ = κ} e ⌊ τ ⌋ = cong ⌊_⌋ (idext e τ)
-- idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
--   Unif-π , 
--   Unif-π , 
--   λ ρ x → cong-π x 
-- idext {κ = κ} e Σ =
--   Unif-σ , 
--   Unif-σ , 
--   λ ρ x → cong-σ x 
-- idext {κ = .(R[ κ₂ ])} e (_<$>_ {κ₁} {κ₂} τ₁ τ₂) = cong-<$> (idext e τ₁) (idext e τ₂) 
 