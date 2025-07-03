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
_≋₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
(l₁ , τ₁) ≋₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋R_ : (ρ₁ ρ₂ : Row (SemType Δ κ)) → Set 
(n , P) ≋R (m , Q) = Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) →  (subst-Row pf P) i ≋₂ Q i)

PointEqual-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
PointEqualNE-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunctionNE Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set
UniformNE :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunctionNE Δ κ₁ κ₂ → Set

convNE : κ₁ ≡ κ₂ → NeutralType Δ R[ κ₁ ] → NeutralType Δ R[ κ₂ ]
convNE refl n = n 

convKripkeNE₁ : ∀ {κ₁'} → κ₁ ≡ κ₁' → KripkeFunctionNE Δ κ₁ κ₂ → KripkeFunctionNE Δ κ₁' κ₂
convKripkeNE₁ refl f = f

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
  Uniform F × Uniform G × PointEqual-≋ {Δ₁} F G 
_≋_ {Δ₁} {R[ κ ]} (ne τ₁) (ne τ₂) = τ₁ ≡ τ₂
_≋_ {Δ₁} {R[ κ₂ ]} (_<$>_ {κ₁} φ₁ n₁) (_<$>_ {κ₁'} φ₂ n₂) = 
  Σ[ pf ∈ (κ₁ ≡ κ₁') ]
  (PointEqualNE-≋ (convKripkeNE₁ pf φ₁) φ₂ ×
  UniformNE φ₁ × UniformNE φ₂ ×
  convNE pf n₁ ≡ n₂)
_≋_ {Δ₁} {R[ κ₂ ]} (φ₁ <$> n₁) _ = ⊥
_≋_ {Δ₁} {R[ κ₂ ]} _ (φ₁ <$> n₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ne x₁) (x₂ ▹ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ne x₁) (row ρ x₂) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ne x₁) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (ne x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (row ρ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (ne x₂) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (x₂ ▹ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row (n , P) x₁) (row (m , Q) x₂) = (n , P) ≋R (m , Q)
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (ne x₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (x₁ ▹ x₂) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (row ρ x₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (ρ₃ ─ ρ₄) = ρ₁ ≋ ρ₃ × ρ₂ ≋ ρ₄

PointEqual-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

PointEqualNE-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) (V : NeutralType Δ₂ κ₁) → 
  F ρ V ≋ G ρ V

Uniform {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (renKripke ρ₁ F ρ₂ (renSem ρ₂ V₂))

UniformNE {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V : NeutralType Δ₂ κ₁) →
  (renSem ρ₂ (F ρ₁ V)) ≋ F (ρ₂ ∘ ρ₁) (renₖNE ρ₂ V)

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
-- Semantic equality forms a PER
-- - Kind of reflexive (as not all SemTypes satisfy Uniformity.)
-- - symmetric
-- - transitive

refl-≋ₗ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₁ ≋ V₁
refl-≋ᵣ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₂ ≋ V₂
sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ}      → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃
trans-≋ᵣ : ∀ {τ₁ τ₂ τ₃ : Row (SemType Δ κ)} → τ₁ ≋R τ₂ → τ₂ ≋R τ₃ → τ₁ ≋R τ₃

sym-≋ {κ = ★}  refl = refl
sym-≋ {κ = L}  refl = refl
sym-≋ {κ = κ `→ κ₁} 
  {F} {G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (Ext ρ (sym-≋ z)))
sym-≋ {κ = R[ κ ]} {ne _} {ne x₂} q = sym q
sym-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} (eq , rel) = sym eq  , sym-≋ rel
sym-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} (refl , eq-ρ) =
  refl , 
  (λ i → (sym (eq-ρ i .fst)) , (sym-≋ (eq-ρ i .snd)))
sym-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (sym-≋ rel₁) , (sym-≋ rel₂)
sym-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Ext , Unif-φ₁ , Unif-φ₂ , refl) = refl , (λ r v → sym-≋ (Ext r v) ) , Unif-φ₂ , Unif-φ₁ , refl
refl-≋ₗ q = trans-≋ q (sym-≋ q)
refl-≋ᵣ q = refl-≋ₗ (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {F} {G} {H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ₗ (sym-≋ q)))
trans-≋ {κ = R[ κ ]} {ne x} {ne x₁} refl q = q
trans-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} (eq-l₁ , rel-τ₁) (eq-l₂ , rel-τ₂) = trans eq-l₁ eq-l₂  , trans-≋ rel-τ₁ rel-τ₂
trans-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} {row (o , R) _} (refl , rel₁) (refl , rel₂) = 
  refl , λ { i → trans (rel₁ i .fst) (rel₂ i .fst) , trans-≋ (rel₁ i .snd) (rel₂ i .snd) }
trans-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} {ρ₆ ─ ρ₅} (rel₁ , rel₂) (rel₃ , rel₄) = (trans-≋ rel₁ rel₃) , (trans-≋ rel₂ rel₄)
trans-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} {φ₃ <$> n₃} (refl , Ext₁ , Unif-φ₁ , _ , refl) (refl , Ext₂ , _ , Unif-φ₃ , refl) = refl , (λ r v → trans-≋ (Ext₁ r v) (Ext₂ r v) ) , Unif-φ₁ , Unif-φ₃ , refl

trans-≋ᵣ {τ₁ = (n , P)} {τ₂ = (m , Q)} {τ₃ = (j , K)} (refl , rel₁) (refl , rel₂) = refl , (λ { i → trans (rel₁ i .fst) (rel₂ i .fst)  , trans-≋ (rel₁ i .snd) (rel₂ i .snd) })
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
reifyRow-≋ : ∀ {n} (P Q : Fin n → Label × SemType Δ κ) →  
               (∀ (i : Fin n) → P i ≋₂ Q i) → 
               reifyRow (n , P) ≡ reifyRow (n , Q)
↻-ren-reflect  : 
  ∀ (ρ : Renamingₖ Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
    (renSem ρ (reflect τ)) ≋ (reflect (renₖNE ρ τ))
↻-ren-reify-─ : ∀ {Δ₁} {Δ₂} {κ} (r : Renamingₖ Δ₁ Δ₂) {V₂ V₁ V₄ V₃ : SemType Δ₁ R[ κ ]} → 
                V₂ ≋ V₄ → V₁ ≋ V₃ → 
                {nr₁ : NotRow V₂ or NotRow V₁} → 
                {nr₂ : NotRow V₄ or NotRow V₃} → 
                renₖNF r (reify ((V₂ ─ V₁) {nr₁})) ≡ reify (renSem r ((V₄ ─ V₃) {nr₂}))

↻-ren-reify : ∀ {Δ₁} {Δ₂} {κ} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≋ V₂ →  renₖNF ρ (reify V₁) ≡ reify (renSem ρ V₂)

↻-ren-reifyRow : ∀ {n} (P Q : Fin n → Label × SemType Δ₁ κ) →  
                        (ρ : Renamingₖ Δ₁ Δ₂) → 
                        (∀ (i : Fin n) → P i ≋₂ Q i) → 
                        renRowₖNF ρ (reifyRow (n , P)) ≡ reifyRow (n , λ i → overᵣ (renSem ρ) (Q i)) 

-- -- --------------------------------------------------------------------------------
-- -- -- reflect-≋ asserts that well kinded types are in the relation

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
    PE-f ρ v = reflect-≋ (cong₂ _·_ refl (reify-≋ {κ = κ} v))
reflect-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = refl

-- -- --------------------------------------------------------------------------------
-- -- -- reify-≋ asserts that related semantic types reify to the same normal form.

reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ₁ `→ κ₂} {F} {G}
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflect-≋ {κ = κ₁} refl)))
reify-≋ {κ = R[ κ ]} {ne x} {ne x₁} refl = refl
reify-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , rel) = (cong₂ _▹ₙ_ refl (reify-≋ rel))
reify-≋ {κ = R[ κ ]} {row (zero , P) _} {row (_ , Q) _} (refl , eq) = refl
reify-≋ {κ = R[ κ ]} {row (suc n , P) _} {row (_ , Q) _} (refl , eq) = 
  cong-⦅⦆ (reifyRow-≋ {n = suc n} P Q λ i → eq i)
reify-≋ {κ = R[ κ ]} {ne x₁ ─ ρ₁} {ne x₂ ─ ρ₃} (rel₁ , rel₂) = cong-─ (cong-ne rel₁) (reify-≋ rel₂)
reify-≋ {κ = R[ κ ]} {(φ₁ <$> n₁) ─ V₂} {(φ₂ <$> n₂) ─ V₃} ((refl , Ext , _ , _ , refl) , rel₂) = {!!}

reify-≋ {κ = R[ κ ]} {(x₁ ▹ x₂) ─ ρ₁} {(x₃ ▹ x₄) ─ ρ₃} ((refl , rel₁) , rel₂) = cong-─ (cong (x₁ ▹ₙ_) (reify-≋ rel₁)) (reify-≋ rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ ne x₃} {row (m , Q) x₂ ─ ne x₄} ((refl , rel) , rel₂) = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel)) (cong-ne rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (x₃ ▹ x₄)} {row (m , Q) x₂ ─ (x₅ ▹ x₆)} ((refl , rel₁) , refl , rel₂) = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel₁ )) (cong (x₃ ▹ₙ_) (reify-≋ rel₂))
reify-≋ {κ = R[ κ ]} {row ρ x₁ ─ row ρ₁ x₃} {(row ρ₂ x₂ ─ row ρ₃ x₄) {left ()}} (rel₁ , rel₂)
reify-≋ {κ = R[ κ ]} {row ρ x₁ ─ row ρ₁ x₃} {(row ρ₂ x₂ ─ row ρ₃ x₄) {right ()}} (rel₁ , rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (ρ₁ ─ ρ₃)} {row (n , Q) x₂ ─ (ρ₄ ─ ρ₅)} ((refl , rel₁) , rel₂) = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel₁)) (reify-≋ {V₁ = ρ₁ ─ ρ₃} {V₂ = ρ₄ ─ ρ₅} rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (φ₁ <$> n₁)} {row (n' , Q) x₂ ─ (φ₂ <$> n₂)} ((refl , rel) , rel') = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel)) (reify-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} rel')
reify-≋ {κ = R[ κ ]} {(ρ₂ ─ ρ₄) ─ ρ₁} {(ρ₅ ─ ρ₆) ─ ρ₃} (rel₁ , rel₂) = cong-─ (reify-≋ {V₁ = ρ₂ ─ ρ₄} {ρ₅ ─ ρ₆} rel₁) (reify-≋ rel₂)
reify-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Ext , _ , _ , refl) with notId? (reifyKripkeNE φ₁) | notId? (reifyKripkeNE φ₂) | Ext S (` Z) 
... | yes p | yes q | c = cong-<$>ne (cong `λ (reify-≋ c)) refl
... | no  p | yes q | c  = ⊥-elim (p (subst (λ X → X) (cong (NotId ∘ `λ) (reify-≋ (sym-≋ c))) q ))
... | yes p | no  q | c = ⊥-elim (q (subst (λ X → X) (cong (NotId ∘ `λ) (reify-≋ c)) p)) 
... | no  p | no  q | c with (¬notId?⇒equalKinds (`λ (reify (φ₁ S (` Z)))) p) | (¬notId?⇒equalKinds (`λ (reify (φ₂ S (` Z)))) q)
... | refl | refl = cong-ne refl

reifyRow-≋ {n = zero} P Q eq = refl
reifyRow-≋ {n = suc n} P Q eq = 
  cong₂ _∷_ 
  (cong₂ _,_ (eq fzero .fst) (reify-≋ (eq fzero .snd))) 
  (reifyRow-≋ {n = n} (P ∘ fsuc) (Q ∘ fsuc) (eq ∘ fsuc))

reifyRow-≋' : ∀ {n m} (P : Fin n → Label × SemType Δ κ) (Q : Fin m → Label × SemType Δ κ) →  
                (pf : m ≡ n) → 
               (∀ (i : Fin n) → P i ≋₂ subst-Row pf Q i) → 
               reifyRow (n , P) ≡ reifyRow (m , Q)
reifyRow-≋' P Q refl i = reifyRow-≋ P Q i


--------------------------------------------------------------------------------
-- 
-- Renamingₖ commutes with reification.

            
--                renSem ρ 
-- SemType Δ₁ κ -------------> SemType Δ₂ Κ
--  |                          |
--  | reify                    | reify
--  |                          |
--  V                          V 
-- NormalType Δ₁ κ ----------> NormalType Δ₂ κ
--                   ren ρ 


↻-ren-reify-─ r {φ₁ <$> ρ₁} {x} {φ₂ <$> ρ₂} {y} (refl , Ext₁ , Unif-φ₁ , Unif-φ₂ , refl) rel {x₁} {x₂} = cong-─ {!!} (f x y rel)
  where
    -- Being forced to repeat this logic is stupid
    f : ∀ x y → x ≋ y → renₖNF r (reify x) ≡ reify (renSem r y)
    f (φ₁ <$> τ₁) (φ₂ <$> τ₂) rel@(refl , Ext , Unif-φ₁ , Unif-φ₂ , refl) with notId? (`λ (reify (φ₁ S (` Z)))) | notId? (`λ (reify (φ₂ (λ x₃ → S (r x₃)) (` Z))))
    ... | yes p | yes q = {!!}
    ... | yes p | no  q = {!!}
    ... | no  p | yes q = {!!}
    ... | no  p | no  q with  (¬notId?⇒equalKinds (reifyKripkeNE φ₁) p) | (¬notId?⇒equalKinds (reifyKripkeNE (λ r' → φ₂ (λ x₃ → r' (r x₃)))) q) 
    ... | refl | refl = cong-ne refl
    f (ne x₁) (ne x₂) refl = refl
    f (x₁ ▹ x₂) (x₃ ▹ x₄) (refl , rel) = (cong₂ (_▹ₙ_) refl (↻-ren-reify r rel))
    f (row (n , P) x₁) (row (m , Q) x₂) (refl , i) = (cong-⦅⦆ (↻-ren-reifyRow P Q r i))
    f (x₁ ─ x₂) (y₁ ─ y₂) (rel₁ , rel₂) = ↻-ren-reify-─ r rel₁ rel₂ 

↻-ren-reify-─ r {ne x₃} {ne x₄} {ne x₅} {ne x₆} refl refl {x₁} {x₂} = refl
↻-ren-reify-─ r {ne x₃} {x₄ ▹ x₅} {ne x₆} {x₇ ▹ x₈} refl (refl , snd₁) {x₁} {x₂} = cong-─ refl (cong (renₖNE r x₄ ▹ₙ_) (↻-ren-reify r snd₁))
↻-ren-reify-─ r {ne x₃} {row (n , P) x₄} {ne x₅} {row (m , Q) x₆} refl (refl , rel) = cong-─ refl (cong-⦅⦆ (↻-ren-reifyRow P Q r rel ))
↻-ren-reify-─ r {ne x₃} {(V₁ ─ V₂) {nr}} {ne x₄} {(V₃ ─ V₄) {nr'}} refl rel₂ {x₁} {x₂} = cong-─ refl (↻-ren-reify-─ r (rel₂ .fst) (rel₂ .snd) {nr} {nr'} )
↻-ren-reify-─ r {ne x₃} {φ₁ <$> n₁} {ne x₄} {ρ₂ <$> n₂} refl rel₂ {x₁} {x₂} = cong-─ refl {!!}
↻-ren-reify-─ r {x₃ ▹ x₄} {ne x₅} {x₆ ▹ x₇} {ne x₈} (refl , rel) refl {x₁} {x₂} = cong-─ (cong₂ (_▹ₙ_) refl (↻-ren-reify r rel)) refl
↻-ren-reify-─ r {x₃ ▹ x₄} {x₅ ▹ x₆} {x₇ ▹ x₈} {x₉ ▹ x₁₀} (refl , rel₁) (refl , rel₂) {x₁} {x₂} = cong-─ (cong (renₖNE r x₃ ▹ₙ_) (↻-ren-reify r rel₁)) (cong (renₖNE r x₅ ▹ₙ_) (↻-ren-reify r rel₂))
↻-ren-reify-─ r {x₃ ▹ x₄} {row (n , P) x₅} {x₆ ▹ x₇} {row (m , Q) x₈} (refl , rel) (refl , relR) {x₁} {x₂} = cong-─ (cong (renₖNE r x₃ ▹ₙ_) (↻-ren-reify r rel)) (cong-⦅⦆ (↻-ren-reifyRow P Q r relR))
↻-ren-reify-─ r {x₃ ▹ x₄} {V₁ ─ V₂} {x₅ ▹ x₆} {V₃ ─ V₄} (refl , rel₁) (rel₂ , rel₃) {x₁} {x₂} = cong-─ (cong (renₖNE r x₃ ▹ₙ_) (↻-ren-reify r rel₁)) (↻-ren-reify-─ r {V₁} {V₂} {V₃} {V₄} rel₂ rel₃)
↻-ren-reify-─ r {x₃ ▹ x₄} {φ₁ <$> n₁} {x₅ ▹ x₆} {φ₂ <$> n₂} (refl , rel₁) rel = cong-─ (cong (renₖNE r x₃ ▹ₙ_) (↻-ren-reify r rel₁)) {!!}
↻-ren-reify-─ r {V₂ ─ V₅} {ne x₃} {V₄ ─ V₆} {ne x₄} rel₁ refl {x₁} {x₂} = cong-─ (↻-ren-reify-─ r (rel₁ .fst) (rel₁ .snd)) refl
↻-ren-reify-─ r {V₂ ─ V₅} {x₃ ▹ x₄} {V₄ ─ V₆} {x₅ ▹ x₆} (rel₁ , rel₂) (refl , rel₃) {x₁} {x₂} = cong-─ (↻-ren-reify-─ r rel₁ rel₂) (cong (renₖNE r x₃ ▹ₙ_) (↻-ren-reify r rel₃))
↻-ren-reify-─ r {V₂ ─ V₅} {row (n , P) x₃} {V₄ ─ V₆} {row (m , Q) x₄} rel₁ (refl , i) {x₁} {x₂} = cong-─ (↻-ren-reify-─ r (rel₁ .fst) (rel₁ .snd)) (cong-⦅⦆ (↻-ren-reifyRow P Q r i))
↻-ren-reify-─ r {V₂ ─ V₅} {V₁ ─ V₆} {V₄ ─ V₇} {V₃ ─ V₈} rel₁ rel₂ {x₁} {x₂} = cong-─ (↻-ren-reify-─ r (rel₁ .fst) (rel₁ .snd)) (↻-ren-reify-─ r (rel₂ .fst) (rel₂ .snd))
↻-ren-reify-─ r {V₂ ─ V₅} {φ₁ <$> n₁} {V₄ ─ V₇} {φ₂ <$> n₂} rel₁ rel₂ {x₁} {x₂} = cong-─ (↻-ren-reify-─ r (rel₁ .fst) (rel₁ .snd)) {!!}
↻-ren-reify-─ r {row (n , P) oρ} {ne x₁} {row (m , Q) oρ'} {ne x₃} (refl , i) refl {ev₁} {ev₂} = cong-─ (cong-⦅⦆ (↻-ren-reifyRow P Q r i)) (cong-ne refl)
↻-ren-reify-─ r {row (n , P) oρ} {x₁ ▹ x₂} {row (m , Q) oρ'} {x₄ ▹ x₅} (refl , i) (refl , rel) {ev₁} {ev₂} = cong-─ (cong-⦅⦆ (↻-ren-reifyRow P Q r i)) (cong₂ _▹ₙ_ refl (↻-ren-reify r rel))
↻-ren-reify-─ r {row (n , P) oρ} {row _ _} {row ρ₂ x₂} {row ρ₃ x₃} rel₁ rel₂ {left ()}
↻-ren-reify-─ r {row (n , P) oρ} {row _ _} {row ρ₂ x₂} {row ρ₃ x₃} rel₁ rel₂ {right ()}
↻-ren-reify-─ r {row (n , P) oρ} {V₁ ─ V₂} {row (m , Q) oρ'} {V₃ ─ V₄} (refl , i) rel₂ {ev₁} {ev₂} = cong-─ (cong-⦅⦆ (↻-ren-reifyRow P Q r i)) (↻-ren-reify-─ r (rel₂ .fst) (rel₂ .snd))
↻-ren-reify-─ r {row (n , P) oρ} {φ₁ <$> n₁} {row (m , Q) oρ'} {φ₂ <$> n₂} (refl , i) rel₂ {ev₁} {ev₂} = cong-─ (cong-⦅⦆ (↻-ren-reifyRow P Q r i)) {!!}

↻-ren-reifyRow {n = zero} P Q ρ eq = refl
↻-ren-reifyRow {n = suc n} P Q ρ eq = 
  cong₂ _∷_ 
    (cong₂ _,_ (eq fzero .fst) (↻-ren-reify ρ (eq fzero .snd))) -- (↻-ren-reify ρ (eq fzero)) 
    (↻-ren-reifyRow {n = n} (P ∘ fsuc) (Q ∘ fsuc) ρ (eq ∘ fsuc))

↻-ren-reify {κ = ★} ρ {V₁} {V₂} refl = refl
↻-ren-reify {κ = L} ρ {V₁} {V₂} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{F} g@{G} q@(Unif-F , Unif-G , Ext) = 
  cong `λ 
    (trans 
      (↻-ren-reify (liftₖ ρ) (Ext S (reflect-≋ (refl {x = ` Z})))) 
      (reify-≋ (trans-≋ 
        (Unif-G S (liftₖ ρ) _ _ (reflect-≋ refl)) 
        (refl-Extᵣ Ext (S ∘ ρ) (↻-ren-reflect (liftₖ ρ) (` Z))))))

↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {ne x₁} {ne y} refl = cong-ne refl
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Ext , Unif-φ₁ , Unif-φ₂ , refl) with 
      notId? (`λ (reify (φ₁ S (` Z)))) 
    | notId? (`λ (reify (φ₂ (S ∘ ρ) (` Z)))) 
... | yes p | yes q = cong-<$>ne (cong `λ (trans (↻-ren-reify (liftₖ ρ) (Ext S (` Z))) (reify-≋ (Unif-φ₂ S (liftₖ ρ) (` Z))))) refl
... | yes p | no  q = ⊥-elim (q 
                             (subst NotId 
                                    (cong `λ (reify-≋ (Ext (S ∘ ρ) (` Z)))) 
                                          (subst NotId 
                                                 (cong `λ (trans
                                                             (trans (↻-ren-reify (liftₖ ρ) (Ext S (` Z)))
                                                              (reify-≋ (Unif-φ₂ S (liftₖ ρ) (` Z))))
                                                             (sym (reify-≋ (Ext (S ∘ ρ) (` Z)))))) 
                                                 (¬idRenₖNF ρ (reifyKripkeNE φ₁) p))))
... | no  p | yes q =
  ⊥-elim (p (¬idRenₖNF⁻¹ ρ (reifyKripkeNE φ₁) 
            (subst NotId (cong `λ (trans (sym (reify-≋ (Ext (S ∘ ρ) (` Z)))) 
                                  (trans (sym (reify-≋ (Unif-φ₁ S (liftₖ ρ) (` Z)))) (sym (↻-ren-reify (liftₖ ρ) (refl-≋ₗ (Ext S (` Z)))))))) q)))
... | no  p | no  q with (¬notId?⇒equalKinds (reifyKripkeNE φ₁) p) | (¬notId?⇒equalKinds (reifyKripkeNE (λ r' → φ₂ (λ x₁ → r' (ρ x₁))))
        q) 
... | refl | refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , q) = cong (renₖNE ρ l₁ ▹ₙ_) (↻-ren-reify ρ q)
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {row (n , P) _} {row (_ , Q) _} (refl , eq) = 
  cong-⦅⦆ (↻-ren-reifyRow P Q ρ λ i → eq i)
↻-ren-reify {Δ₁} {Δ₂} {κ = R[ κ ]} ρ {(ρ₂ ─ ρ₁) {nr}} {(ρ₄ ─ ρ₃) {nr'}} (rel₁ , rel₂) = ↻-ren-reify-─ ρ rel₁ rel₂ {nr₂ = nr'}

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

-- -- --------------------------------------------------------------------------------
-- -- -- Functorial actions

renSem-id-≋    : ∀ {V₁ V₂ : SemType Δ₁ κ} → V₁ ≋ V₂  → (renSem id V₁) ≋ V₂
renSem-id-≋ {κ = ★} refl = renₖNF-id _
renSem-id-≋ {κ = L} refl = renₖNF-id _
renSem-id-≋ {κ = κ `→ κ₁} {F} {G} e = e
renSem-id-≋ {κ = R[ κ ]} {ne x} {ne y} refl = renₖNE-id x
renSem-id-≋ {κ = R[ κ ]} {(l₁ ▹ τ₁)} {(l₂ ▹ τ₂)} (refl , rel) = renₖNE-id l₁ , renSem-id-≋ rel
renSem-id-≋ {κ = R[ κ ]} {row (n , P) _} {row (n , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-id-≋ (eq i .snd) } -- renSem-id-≋ ∘ eq
renSem-id-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (renSem-id-≋ rel₁) , (renSem-id-≋ rel₂)

renSem-comp-≋  : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂)(ρ₂ : Renamingₖ Δ₂ Δ₃){V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≋ (renSem ρ₂ (renSem ρ₁ V₂))
renSem-comp-≋ {κ = ★} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = L} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = κ `→ κ₁} ρ₁ ρ₂ {F} {G} (Unif-F , Unif-G , Ext) = 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {ne x} {ne y} refl = renₖNE-comp _ _ _
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , rel) = (renₖNE-comp ρ₁ ρ₂ l₁) , (renSem-comp-≋ ρ₁ ρ₂ rel)
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {row (n , P) _} {row (_ , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-comp-≋  ρ₁ ρ₂ (eq i .snd) }
renSem-comp-≋ {κ = R[ κ ]} r₁ r₂ {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (renSem-comp-≋ r₁ r₂ rel₁) , (renSem-comp-≋ r₁ r₂ rel₂)

↻-lift-weaken-≋ₖ : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → 
                renSem (liftₖ {κ = κ'} ρ) (renSem S V₁) ≋ renSem S (renSem ρ V₂)
↻-lift-weaken-≋ₖ {κ' = κ'} ρ {V₁} {V₂} v = 
  trans-≋ 
    (sym-≋ (renSem-comp-≋ (S {κ₂ = κ'}) (liftₖ ρ) (sym-≋ v))) 
    (renSem-comp-≋ ρ S (refl-≋ᵣ v))
