{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.CompletenessRelation where

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

--------------------------------------------------------------------------------
-- Completeness of type normalization


-- Completeness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
Extensionality-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = κ₁ `→ κ₂} (left x) (left y) = x ≡ y
_≋_ {κ = κ₁ `→ κ₂} (left x) (right y) = ⊥
_≋_ {κ = κ₁ `→ κ₂} (right y) (left x) = ⊥
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} (right F) (right G) = 
  Uniform F × Uniform G × Extensionality-≋ {Δ₁} F G
 
_≋_ {κ = R[ ★ ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ L ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (right y) = ⊥
_≋_ {κ = R[ κ `→ κ₁ ]} (right x) (left y) = ⊥
_≋_ {Δ₁} {κ = R[ κ₁ `→ κ₂ ]} (right ( l₁ ,  F )) (right ( l₂ , G )) =
  l₁ ≡ l₂ × (_≋_ {κ = κ₁ `→ κ₂} F G)
_≋_ {κ = R[ R[ κ ] ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ R[ κ ] ]} (left x) (right y) = ⊥
_≋_ {κ = R[ R[ κ ] ]} (right y) (left x) = ⊥
_≋_ {Δ₁} {κ = R[ R[ κ ] ]} (right ( l₁ , τ₁ )) (right ( l₂ , τ₂ )) = 
  l₁ ≡ l₂ × τ₁ ≋ τ₂

Extensionality-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

Uniform {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (F (ρ₂ ∘ ρ₁) (renSem ρ₂ V₂))

--------------------------------------------------------------------------------
-- Semantic equality forms a PER
-- - Kind of reflexive
-- - symmetric
-- - transitive

reflNE-≋ : ∀ (τ : NeutralType Δ κ) → reflectNE τ ≋ reflectNE τ
reflNE-≋ {κ = ★} τ = refl
reflNE-≋ {κ = L} τ = refl
reflNE-≋ {κ = κ `→ κ₁} τ = refl
reflNE-≋ {κ = R[ ★ ]} τ = refl
reflNE-≋ {κ = R[ L ]} τ = refl
reflNE-≋ {κ = R[ κ `→ κ₁ ]} τ = refl
reflNE-≋ {κ = R[ R[ κ ] ]} τ = refl

--------------------------------------------------------------------------------
-- Congruence

sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
sym-≋ {κ = ★}  refl = refl
sym-≋ {κ = L}  refl = refl
sym-≋ {κ = κ `→ κ₁} {left x} {left x₁} refl = refl
sym-≋ {κ = κ `→ κ₁} 
  {right F} {right G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (Ext ρ (sym-≋ z)))
sym-≋ {κ = R[ ★ ]}   refl = refl
sym-≋ {κ = R[ L ]}   refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , F)} {right (.l₁ , G)} (refl , F≋G) = refl , (sym-≋ F≋G)
sym-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
sym-≋ {κ = R[ R[ κ ] ]} {right (l , τ₁)} {right (.l , τ₂)} (refl , eq) = refl , sym-≋ eq 

refl-≋ : ∀ {V₁ V₂ : SemType Δ κ} → V₁ ≋ V₂ → V₁ ≋ V₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃

refl-≋ q = trans-≋ q (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = κ₁ `→ κ₂} {right F} {right G} {right H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ (sym-≋ q)))
trans-≋ {κ = R[ ★ ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ L ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {right (l , F)} {right (.l , G)} {right (l' , H)} 
  (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H
trans-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} {τ₃ = τ₃} refl q₂ = q₂
trans-≋ {κ = R[ R[ κ ] ]} {right (l , F)} {right (.l , G)} {τ₃ = right (.l , H)} (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H

--------------------------------------------------------------------------------
-- Reasoning

infixr 2 _≋⟨_⟩∎ _≋⟨_⟩_

_≋⟨_⟩∎ : ∀ (V₁ : SemType Δ κ) {V₂ : SemType Δ κ}
  → V₁ ≋ V₂
    -----
  → V₁ ≋ V₂
x ≋⟨ q ⟩∎  =  q
  
_≋⟨_⟩_ : ∀ {V₂ V₃ : SemType Δ κ} → 
          (V₁ : SemType Δ κ) → 
          (V₁ ≋ V₂) →
          (V₂ ≋ V₃) →
          V₁ ≋ V₃
V₁ ≋⟨ q ⟩ r = trans-≋ q r

--------------------------------------------------------------------------------
-- Reflecting propositional equality of neutral types into semantic equality.


reflectNE-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflectNE τ₁ ≋ reflectNE τ₂
reflectNE-≋ {κ = ★} refl = refl
reflectNE-≋ {κ = L} refl = refl
reflectNE-≋ {κ = κ `→ κ₁} eq = eq
reflectNE-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = reflNE-≋ τ₁

--------------------------------------------------------------------------------
-- reflect propositional equality to semantic equality

-- reflect-≋ : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η : Env Δ₁ Δ₂} → eval τ₁ η ≡ eval τ₂ → τ₁ ≋ τ₂ 
-- reflect-≋ {κ = ★} refl = refl
-- reflect-≋ {κ = L} refl = refl
-- reflect-≋ {κ = κ `→ κ₁} e@refl = {!refl-≋ (reflect-≋!}
-- reflect-≋ {κ = R[ κ ]} refl = {!!}

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
-- Pointwise PER for environments

Env-≋ : (η₁ η₂ : Env Δ₁ Δ₂) → Set
Env-≋ η₁ η₂ = ∀ {κ} (x : KVar _ κ) → (η₁ x) ≋ (η₂ x)

-- extension
extend-≋ : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → 
            {V₁ V₂ : SemType Δ₂ κ} → 
            V₁ ≋ V₂ → 
            Env-≋ (extende η₁ V₁) (extende η₂ V₂)
extend-≋ p q Z = q
extend-≋ p q (S v) = p v

--------------------------------------------------------------------------------
-- related applicands yield related applications

App-≋ : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
App-≋ {V₁ = left x} {left .x} refl q = reflectNE-≋ (cong (x ·_) (reify-≋ q))
App-≋ {V₁ = left x} {right y} () q
App-≋ {V₁ = right y} {left x} () q
App-≋ {V₁ = right F} {right G} (unif-F , unif-G , Ext) q = Ext id q           

▹-≋ : ∀ {L₁ L₂ : NormalType Δ L} → 
           _≋_ {κ = L} L₁ L₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (L₁ ▹V W₁) ≋ (L₂ ▹V W₂)
▹-≋ {κ₁ = ★} refl refl = refl
▹-≋ {κ₁ = L} refl refl = refl
▹-≋ {κ₁ = κ₁ `→ κ₂} refl {left x} {left x₁} w = refl , w
▹-≋ {κ₁ = κ₁ `→ κ₂} refl {right F} {right G} ≋W = 
  refl , ≋W
▹-≋ {κ₁ = R[ κ₁ ]} refl w = refl , w

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

lem : ∀ (ρ : Renaming Δ₁ Δ₂) (F G : KripkeFunction Δ₁ κ₁ κ₂) → 
        _≋_ {Δ = Δ₁} {κ = κ₁ `→ κ₂} (right F) (right G) → 
        N.ren (lift ρ) (reify (F S (reflectNE (` Z)))) ≡ reify (renKripke ρ G S (reflectNE (` Z)))
↻-ren-reify : ∀ {Δ₁} {Δ₂} {κ} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≋ V₂ →  N.ren ρ (reify V₁) ≡ reify (renSem ρ V₂)

lem {κ₁ = κ₁} {κ₂} ρ F G q@(Unif-F , Unif-G , Ext) = (trans 
    (↻-ren-reify (lift ρ) (Ext S (reflectNE-≋ (refl {x = ` Z})))) 
    (reify-≋ 
      ((renSem (lift ρ) (G S (reflectNE (` Z)))) 
      ≋⟨ (Unif-G S (lift ρ) _ _ (reflectNE-≋ refl)) ⟩ 
      ((G (λ x → lift ρ (S x)) (renSem (lift ρ) (reflectNE (` Z)))) 
      ≋⟨ (App-≋ 
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
    G≋G = refl-≋ {κ = κ₁ `→ κ₂} {V₁ = right G} {V₂ = right F} (sym-≋ {κ = κ₁ `→ κ₂} {τ₁ = right F} {τ₂ = right G} q)

↻-ren-reify {κ = ★} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = L} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = κ₁ `→ κ₂} ρ {left _} {left _} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{right F} g@{right G} q@(Unif-F , Unif-G , Ext) = 
  cong `λ 
  (lem ρ F G q)
↻-ren-reify {κ = R[ ★ ]} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = R[ L ]} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = R[ κ `→ κ₁ ]} ρ {left x} {left x₁} refl = refl
↻-ren-reify {κ = R[ κ `→ κ₁ ]} ρ {right (l , left f)} {right (.l , left g)} (refl , refl) = refl
↻-ren-reify {κ = R[ κ₁ `→ κ₂ ]} ρ {right (l , f@(right F))} {right (.l , g@(right G))} (refl , q@(Unif-F , Unif-G , Ext)) = 
  cong row (cong₂ _▹_ refl (cong `λ (lem ρ F G q)))
↻-ren-reify {κ = R[ R[ κ ] ]} ρ {left _} {left _} refl = refl
↻-ren-reify {κ = R[ R[ κ ] ]} ρ {right (l , τ₁)} {right (.l , τ₂)} (refl , q) = cong row (cong₂ _▹_ refl (↻-ren-reify ρ q))

--------------------------------------------------------------------------------
-- Renaming commutes with application.

cong-ren-·V : ∀ (ρ : Renaming Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≋_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≋ V₂ →  
                renSem ρ (F ·V V₁) ≋ (renSem {κ = κ₁ `→ κ₂} ρ G ·V renSem ρ V₂)
cong-ren-·V {κ₂ = ★} ρ {left x} {right y} () r
cong-ren-·V {κ₂ = ★} ρ {right y} {left x} () r
cong-ren-·V {κ₂ = L} ρ {left x} {right y} () r
cong-ren-·V {κ₂ = L} ρ {right y} {left x} () r
cong-ren-·V {κ₂ = ★} ρ {left x} {left .x} refl r = 
  cong (ne ∘ (renNE ρ x ·_)) (trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))
cong-ren-·V {κ₂ = L} ρ {left x} {left .x} refl r = 
  cong (ne ∘ (renNE ρ x ·_)) (trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))
cong-ren-·V {κ₂ = κ₂ `→ κ₃} ρ {left τ} {left .τ} refl r = 
  cong (renNE ρ τ ·_) ((trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r))))
cong-ren-·V {κ₂ = R[ ★ ]} ρ {left f} {left .f} refl r = 
  cong ne (cong (renNE ρ f ·_) ((trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))))
cong-ren-·V {κ₂ = R[ L ]} ρ {left f} {left .f} refl r = 
  cong ne (cong (renNE ρ f ·_) ((trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))))
cong-ren-·V {κ₂ = R[ κ₂ `→ κ₃ ]} ρ {left f} {left .f} refl r = 
  cong (renNE ρ f ·_) (trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))
cong-ren-·V {κ₂ = R[ R[ κ₂ ] ]} ρ {left f} {left .f} refl r = 
  cong (renNE ρ f ·_) (trans (↻-ren-reify ρ (refl-≋ r)) (reify-≋ (ren-≋ ρ r)))
cong-ren-·V {κ₂ = κ₂} ρ {right F} {right G} (Unif-F , Unif-G , Ext) {V₁} {V₂} r = 
  trans-≋ (Unif-F id ρ V₁ V₂ r) ((Ext ρ (ren-≋ ρ (refl-≋ (sym-≋ r)))))

--------------------------------------------------------------------------------
-- Renaming commutes with π

rensem-comp-▹ : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
                   V₁ ≋ V₂ → renSem-R ρ₂ ((N.ren ρ₁ l) ▹V renSem ρ₁ V₁) ≋ (N.ren (ρ₂ ∘ ρ₁) l ▹V renSem (ρ₂ ∘ ρ₁) V₂)
rensem-comp-▹ {κ = ★} ρ₁ ρ₂ l V .V refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp ρ₁ ρ₂ V = refl
rensem-comp-▹ {κ = L} ρ₁ ρ₂ l V .V refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp ρ₁ ρ₂ V = refl
rensem-comp-▹ {κ = κ₁ `→ κ₂} ρ₁ ρ₂ l (left f) (left .f) refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp-ne ρ₁ ρ₂ f = refl , refl
rensem-comp-▹ {κ = κ₁ `→ κ₂} ρ₁ ρ₂ l (right F) (right G) (Unif-F , Unif-G , Ext) = sym (ren-comp ρ₁ ρ₂ l) , 
  (λ ρ₃ ρ₄ → Unif-F (λ x → ρ₃ (ρ₂ (ρ₁ x))) ρ₄) , 
  (λ {Δ₂ = Δ₄} {Δ₃ = Δ₅} ρ₃ → Unif-G (λ x → ρ₃ ((ρ₂ ∘ ρ₁) x))) , 
  λ {Δ₂ = Δ₄} ρ → Ext (λ x → ρ (ρ₂ (ρ₁ x)))
rensem-comp-▹ {κ = R[ κ ]} ρ₁ ρ₂ l V₁ V₂ v 
  rewrite sym (renSem-comp ρ₁ ρ₂ V₁) | sym (renSem-comp ρ₁ ρ₂ V₂) = (sym (ren-comp ρ₁ ρ₂ l)) , sym-≋ (ren-≋ (ρ₂ ∘ ρ₁) (sym-≋ v))


cong-π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → τ₁ ≋ τ₂ → π τ₁ ≋ π τ₂
↻-ren-π : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → V₁ ≋ V₂ → renSem ρ (π V₁) ≋ π (renSem ρ V₂) 
↻-ren-π {★} ρ (ne x) V₂ refl = refl
↻-ren-π {★} ρ (row ρ₁) V₂ refl = refl
↻-ren-π {L} ρ (ne x) V₂ refl = refl
↻-ren-π {L} ρ (row ρ₁) V₂ refl = refl
↻-ren-π {κ `→ κ₁} ρ (left f) (left .f) refl = refl
↻-ren-π {κ₁ `→ κ₂} ρ (right (l , left F)) (right (.l , left G)) (refl , refl) = 
  (λ { ρ₁ ρ₂ V₁ V₂ v → 
  trans-≋ 
    (↻-ren-π ρ₂ (N.ren (λ x → ρ₁ (ρ x)) l ▹V
      reflectNE (renNE (λ x → ρ₁ (ρ x)) F · reify V₁)) (N.ren (λ x → ρ₁ (ρ x)) l ▹V
      reflectNE (renNE (λ x → ρ₁ (ρ x)) F · reify V₁)) 
      (▹-≋ refl (reflNE-≋ (renNE (λ x → ρ₁ (ρ x)) F · reify V₁)))) 
      -- Need to rewrite by renaming composition (ren-comp) but for renSem-R
      -- and in a convoluted painful way under reflectNE
    (cong-π {!  !}) }) ,
  {! !} ,
  {! !}
↻-ren-π {κ `→ κ₁} ρ (right (l , right F)) (right (.l , right G)) (refl , eq) = {! !}
↻-ren-π {R[ κ ]} ρ V₁ V₂ q = {! !}

--------------------------------------------------------------------------------
-- pfft

Unif-NE : ∀ (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) → 
            Uniform (λ ρ' v → π (N.ren ρ' l ▹V reflectNE (renNE ρ' f · reify v)))


Unif-NE {κ₁ = ★} {★} l f ρ₁ ρ₂ V₁ V₂ refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp-ne ρ₁ ρ₂ f = cong Π refl
Unif-NE {κ₁ = ★} {L} l f ρ₁ ρ₂ V₁ V₂ refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp-ne ρ₁ ρ₂ f = cong ΠL refl
Unif-NE {κ₁ = ★} {κ₂ `→ κ₃} l f ρ₁ ρ₂ V₁ V₂ refl = 
  (λ ρ₃ ρ₄ V₃ V₄ q → {!  !}) , 
  {!   !} , 
  ext
  where
    unif : Uniform
            (renKripke ρ₂
           (λ ρ' v → 
              π (N.ren ρ' (N.ren ρ₁ l) ▹V
              reflectNE ((renNE ρ' (renNE ρ₁ f) · N.ren ρ' V₁) · reify v))))
    unif ρ₃ ρ₄ V₃ V₄ q rewrite 
        sym (NTypeProps.ren-comp ρ₂ ρ₃ (N.ren ρ₁ l))
      | sym (NTypeProps.ren-comp-ne ρ₂ ρ₃ (renNE ρ₁ f))
      | sym (NTypeProps.ren-comp ρ₂ ρ₃ V₂)   = {! Unif-NE l f ρ₁ ρ₂ V₁ V₂ refl   !}  
             
    ext : Extensionality-≋
      (renKripke ρ₂
       (λ ρ' v →
          π
          (N.ren ρ' (N.ren ρ₁ l) ▹V
           reflectNE ((renNE ρ' (renNE ρ₁ f) · N.ren ρ' V₁) · reify v))))
      (λ ρ' v →
         π
         (N.ren ρ' (N.ren (λ x → ρ₂ (ρ₁ x)) l) ▹V
          reflectNE
          ((renNE ρ' (renNE (λ x → ρ₂ (ρ₁ x)) f) · N.ren ρ' (N.ren ρ₂ V₁)) ·
           reify v))) 
    ext ρ v rewrite 
        NTypeProps.ren-comp ρ₂ ρ (N.ren ρ₁ l) 
      | NTypeProps.ren-comp ρ₁ ρ₂ l 
      | NTypeProps.ren-comp-ne ρ₂ ρ (renNE ρ₁ f) 
      | NTypeProps.ren-comp-ne ρ₁ ρ₂ f 
      | NTypeProps.ren-comp ρ₂ ρ V₁ 
      | reify-≋ v = cong-π (▹-≋ refl (reflectNE-≋ refl))

Unif-NE {κ₁ = ★} {R[ κ₂ ]} l f ρ₁ ρ₂ V₁ V₂ refl = {!   !}
Unif-NE {κ₁ = L} l f ρ₁ ρ₂ V₁ V₂ q = {!   !}
Unif-NE {κ₁ = κ₁ `→ κ₂} l f ρ₁ ρ₂ V₁ V₂ q = {!   !}
Unif-NE {κ₁ = R[ κ₁ ]} l f ρ₁ ρ₂ V₁ V₂ q = {!   !} 


cong-π {κ = ★} e = cong (π {κ = ★}) e
cong-π {κ = L} e = cong (π {κ = L}) e
cong-π {κ = κ₁ `→ κ₂} {left x} {left x₁} refl = refl
cong-π {κ = κ₁ `→ κ₂} {right (l , left f)} {right (.l , left .f)} (refl , refl) = 
  Unif-NE l f , 
  Unif-NE l f , 
  λ ρ q → (cong-π (▹-≋ refl (reflectNE-≋ ((cong₂ _·_ refl (reify-≋ q))))))

cong-π {κ = κ₁ `→ κ₂} {right (l , right F)} {right (l , right G)} (refl , eq) = {!  !}
cong-π {κ = R[ κ ]} e = {!  !}

-- --------------------------------------------------------------------------------
-- -- id extension
-- --
-- -- Lemma needed for semantic renaming commutation theorem.
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


idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
idext-pred : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (π : Pred Δ₁ R[ κ ]) →
               evalPred π η₁ ≡ evalPred π η₂
↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)
↻-ren-eval ρ τ P = {!  !}

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
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ (sym-≋ q))
           ; (S x) → sym-≋ {!  !} }) τ)) ,  -- renSem-comp (refl-≋ (e x)) ρ₁ ρ₂
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-ren-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ ∘ sym-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ (sym-≋ q))
           ; (S x) → sym-≋ {!  !} }) τ)) , -- (renSem-comp ρ₁ ρ₂ (refl-≋ (sym-≋ (e x))))
  λ ρ q → idext (extend-≋ (ren-≋ ρ ∘ e) q) τ
idext {κ = ★} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = L} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = κ `→ κ₁} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = R[ κ ]} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
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
  λ ρ x → cong-π x -- cong (π {κ = κ₁}) x)
idext {κ = κ} e Σ = {!   !}
idext {κ = κ} e (τ <$> τ₁) = {!   !} 
 
-- ↻-ren-eval ρ τ {η₁} {η₂} P = {!   !}
   
 
  
