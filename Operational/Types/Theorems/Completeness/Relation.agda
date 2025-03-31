{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Relation where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming as NTypeProps
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Completeness of type normalization


-- Completeness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
PointEqual-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
  Uniform F × Uniform G × PointEqual-≋ {Δ₁} F G 
_≋_ {Δ₁} {R[ κ ]} (left x) (left y) = x ≡ y
_≋_ {Δ₁} {R[ κ ]} (left x) (right y) = ⊥
_≋_ {Δ₁} {R[ κ ]} (right y) (left x) = ⊥
_≋_ {Δ₁} {R[ κ ]} (right (n , P)) (right (m , Q)) = 
  Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) → (subst-Row pf P) i ≋ Q i)

PointEqual-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

Uniform {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (renKripke ρ₁ F ρ₂ (renSem ρ₂ V₂))

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



-- Semantic equality forms a PER
-- - Kind of reflexive (as not all SemTypes satisfy Uniformity.)
-- - symmetric
-- - transitive

refl-≋ₗ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₁ ≋ V₁
refl-≋ᵣ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₂ ≋ V₂
sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ}      → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃

sym-≋ {κ = ★}  refl = refl
sym-≋ {κ = L}  refl = refl
sym-≋ {κ = κ `→ κ₁} 
  {F} {G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (Ext ρ (sym-≋ z)))
sym-≋ {κ = R[ κ ]} {left x} {left x₁} q = sym q
sym-≋ {κ = R[ κ ]} {right (n , P)} {right (m , Q)} (refl , eq-ρ) = refl , λ { i → sym-≋ (eq-ρ i)  }

refl-≋ₗ q = trans-≋ q (sym-≋ q)
refl-≋ᵣ q = refl-≋ₗ (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {F} {G} {H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ₗ (sym-≋ q)))
trans-≋ {κ = R[ κ ]} {left x} {left x₁} refl q = q
trans-≋ {κ = R[ κ ]} {right (n , P)} {right (m , Q)} {right (o , R)} (refl , rel₁) (refl , rel₂) = refl , λ { i → trans-≋ (rel₁ i) (rel₂ i) }

-- --------------------------------------------------------------------------------
-- -- Pointwise extensionality (accordingly) forms a PER

refl-Extₗ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ F F
refl-Extₗ Ext ρ q = trans-≋ (Ext ρ q) (sym-≋ (Ext ρ (refl-≋ₗ (sym-≋ q))))

sym-Ext : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G F
sym-Ext Ext ρ q = trans-≋ (refl-≋ₗ (sym-≋ (Ext ρ (sym-≋ q)))) (sym-≋ (Ext ρ (sym-≋ q)))

refl-Extᵣ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G G
refl-Extᵣ Ext ρ q = refl-Extₗ (sym-Ext Ext) ρ q

trans-Ext : ∀ {F G H : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G H → PointEqual-≋ F H
trans-Ext Ext-FG Ext-GH ρ q = trans-≋ (Ext-FG ρ q) (trans-≋ (Ext-GH ρ (sym-≋ q)) (refl-Extᵣ Ext-GH ρ q))

-- --------------------------------------------------------------------------------
-- -- Reasoning

-- infixr 2 _≋⟨_⟩∎ _≋⟨_⟩_

-- _≋⟨_⟩∎ : ∀ (V₁ : SemType Δ κ) {V₂ : SemType Δ κ}
--   → V₁ ≋ V₂
--     -----
--   → V₁ ≋ V₂
-- x ≋⟨ q ⟩∎  =  q
  
-- _≋⟨_⟩_ : ∀ {V₂ V₃ : SemType Δ κ} → 
--           (V₁ : SemType Δ κ) → 
--           (V₁ ≋ V₂) →
--           (V₂ ≋ V₃) →
--           V₁ ≋ V₃
-- V₁ ≋⟨ q ⟩ r = trans-≋ q r

-- --------------------------------------------------------------------------------
-- -- The first step in a proof by logical relation is to assert that well-typed 
-- -- entities inhabit the relation. 

-- -- The following definitions are necessarily mutually recursive;
-- -- ideally some of these would be put in Theorems.Completeness.Commutativity.

reflect-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflect τ₁ ≋ reflect τ₂
reify-≋    : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → reify V₁   ≡ reify V₂ 
reifyRow-≋ : ∀ {n} (P Q : Fin n → SemType Δ κ) →  
               (∀ (i : Fin n) → P i ≋ Q i) → 
               reifyRow (n , P) ≡ reifyRow (n , Q)
↻-ren-reflect  : 
  ∀ (ρ : Renamingₖ Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
    (renSem ρ (reflect τ)) ≋ (reflect (renₖNE ρ τ))
↻-ren-reify : ∀ {Δ₁} {Δ₂} {κ} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≋ V₂ →  renₖNF ρ (reify V₁) ≡ reify (renSem ρ V₂)
↻-ren-reifyRow : ∀ {n} (P Q : Fin n → SemType Δ₁ κ) →  
                        (ρ : Renamingₖ Δ₁ Δ₂) → 
                        (∀ (i : Fin n) → P i ≋ Q i) → 
                        renRowₖNF ρ (reifyRow (n , P)) ≡ reifyRow (n , (renSem ρ ∘ Q))

-- --------------------------------------------------------------------------------
-- -- reflect-≋ asserts that well kinded types are in the relation

reflect-≋ {κ = ★} refl = refl
reflect-≋ {κ = L} refl = refl
reflect-≋ {κ = κ `→ κ₁} {f} refl = Unif-f , Unif-f , PE-f
  where
    Unif-f : Uniform (λ ρ v → reflect (renₖNE ρ f · reify v))
    Unif-f ρ₁ ρ₂ V₁ V₂ q = 
      trans-≋ 
        (↻-ren-reflect ρ₂ (renₖNE ρ₁ f · reify V₁)) 
        (reflect-≋ (cong₂ _·_ (sym (renₖNE-comp ρ₁ ρ₂ f)) 
          (↻-ren-reify ρ₂ q)))

    PE-f : PointEqual-≋ (λ ρ v → reflect (renₖNE ρ f · reify v)) (λ ρ v → reflect (renₖNE ρ f · reify v))
    PE-f ρ v = reflect-≋ (cong₂ _·_ refl (reify-≋ v))
reflect-≋ {κ = R[ κ ]} {τ₁ = τ₁} q = q

-- --------------------------------------------------------------------------------
-- -- reify-≋ asserts that related semantic types reify to the same normal form.

reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ₁ `→ κ₂} {F} {G}
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflect-≋ refl)))
reify-≋ {κ = R[ κ ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ κ ]} {right (zero , P)} {right (_ , Q)} (refl , eq) = refl
reify-≋ {κ = R[ κ ]} {right (suc n , P)} {right (_ , Q)} (refl , eq) = 
  cong ⦅_⦆ (reifyRow-≋ {n = suc n} P Q λ i → eq i) 

reifyRow-≋ {n = zero} P Q eq = refl
reifyRow-≋ {n = suc n} P Q eq = 
  cong₂ _∷_ 
    (reify-≋ (eq fzero)) 
    (reifyRow-≋ {n = n} (P ∘ fsuc) (Q ∘ fsuc) (eq ∘ fsuc))

--------------------------------------------------------------------------------
-- Renamingₖ commutes with reification.

--             
--                renSem ρ 
-- SemType Δ₁ κ -------------> SemType Δ₂ Κ
--  |                          |
--  | reify                    | reify
--  |                          |
--  V                          V 
-- NormalType Δ₁ κ ----------> NormalType Δ₂ κ
--                   ren ρ 


↻-ren-reify {κ = ★} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = L} ρ {V₁} {V₂} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{F} g@{G} q@(Unif-F , Unif-G , Ext) = 
  cong `λ 
    (trans 
      (↻-ren-reify (liftₖ ρ) (Ext S (reflect-≋ (refl {x = ` Z})))) 
      (reify-≋ (trans-≋ 
        (Unif-G S (liftₖ ρ) _ _ (reflect-≋ refl)) 
        (refl-Extᵣ Ext (S ∘ ρ) (↻-ren-reflect (liftₖ ρ) (` Z))))))
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {left x} {left y} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {right (n , P)} {right (_ , Q)} (refl , eq) = 
  cong ⦅_⦆ (↻-ren-reifyRow P Q ρ λ i → eq i)

↻-ren-reifyRow {n = zero} P Q ρ eq = refl
↻-ren-reifyRow {n = suc n} P Q ρ eq = 
  cong₂ _∷_ 
    (↻-ren-reify ρ (eq fzero)) 
    (↻-ren-reifyRow {n = n} (P ∘ fsuc) (Q ∘ fsuc) ρ (eq ∘ fsuc))

--------------------------------------------------------------------------------
-- Renamingₖ commutes with reflection of neutral types

--             
--            ren ρ 
-- Type Δ₁ κ -------------> Type Δ₂ κ 
--  |                        |
--  | reflect              | reflect
--  |                        |
--  V                        V 
-- SemType Δ₁ κ ----------> SemType Δ₂ κ
--               renSem ρ 

↻-ren-reflect {κ = ★} ρ τ = refl
↻-ren-reflect {κ = L} ρ τ = refl
↻-ren-reflect {κ = κ `→ κ₁} ρ τ = 
  (λ ρ₁ ρ₂ V₁ V₂ x → 
    trans-≋ 
    (↻-ren-reflect ρ₂ (renₖNE (λ x₁ → ρ₁ (ρ x₁)) τ · reify V₁)) 
    (reflect-≋ (cong₂ _·_ (sym (renₖNE-comp (ρ₁ ∘ ρ) ρ₂ τ)) (↻-ren-reify ρ₂ x)))) , 
  (λ ρ₁ ρ₂ V₁ V₂ x → 
    trans-≋ 
      (↻-ren-reflect ρ₂ (renₖNE ρ₁ (renₖNE ρ τ) · reify V₁)) 
      (reflect-≋ (cong₂ _·_ (sym (renₖNE-comp ρ₁ ρ₂ (renₖNE ρ τ))) (↻-ren-reify ρ₂ x)))) , 
  λ ρ' v → reflect-≋ (cong₂ _·_ (renₖNE-comp ρ ρ' τ) (reify-≋ v))
↻-ren-reflect {κ = R[ κ ]} ρ τ = refl

--------------------------------------------------------------------------------
-- Functorial actions

renSem-id-≋    : ∀ {V₁ V₂ : SemType Δ₁ κ} → V₁ ≋ V₂  → (renSem id V₁) ≋ V₂
renSem-id-≋ {κ = ★} refl = renₖNF-id _
renSem-id-≋ {κ = L} refl = renₖNF-id _
renSem-id-≋ {κ = κ `→ κ₁} {F} {G} e = e
renSem-id-≋ {κ = R[ κ ]} {left x} {left y} refl = renₖNE-id x
renSem-id-≋ {κ = R[ κ ]} {right (n , P)} {right (n , Q)} (refl , eq) = refl , renSem-id-≋ ∘ eq

renSem-comp-≋  : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂)(ρ₂ : Renamingₖ Δ₂ Δ₃){V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≋ (renSem ρ₂ (renSem ρ₁ V₂))
renSem-comp-≋ {κ = ★} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = L} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = κ `→ κ₁} ρ₁ ρ₂ {F} {G} (Unif-F , Unif-G , Ext) = 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {left x} {left y} refl = renₖNE-comp _ _ _
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {right (n , P)} {right (_ , Q)} (refl , eq) = refl , renSem-comp-≋ ρ₁ ρ₂ ∘ eq

↻-lift-weaken-≋ₖ : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → 
                renSem (liftₖ {κ = κ'} ρ) (renSem S V₁) ≋ renSem S (renSem ρ V₂)
↻-lift-weaken-≋ₖ {κ' = κ'} ρ {V₁} {V₂} v = 
  trans-≋ 
    (sym-≋ (renSem-comp-≋ (S {κ₂ = κ'}) (liftₖ ρ) (sym-≋ v))) 
    (renSem-comp-≋ ρ S (refl-≋ᵣ v))
