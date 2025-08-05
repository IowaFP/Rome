-- {-# OPTIONS --safe #-}
module Rome.Both.Types.Theorems.Soundness.Relation where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Properties.Renaming
open import Rome.Both.Types.Properties.Substitution
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Renaming as NTypeProps
open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming
open import Rome.Both.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Soundness of type normalization


-- Soundness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
_≋₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
(l₁ , τ₁) ≋₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋R_ : (ρ₁ ρ₂ : Row (SemType Δ κ)) → Set 
(n , P) ≋R (m , Q) = Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) →  (subst-Row pf P) i ≋₂ Q i)

PointEqual-≋ : ∀ {Δ₁ : KEnv ι₁} {κ₁ : Kind ι₂} {κ₂ : Kind ι₃} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
PointEqualNE-≋ : ∀ {Δ₁ : KEnv ι₁} {κ₁ : Kind ι₂} {κ₂ : Kind ι₃}  (F G : KripkeFunctionNE Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ : KEnv ι₁} {κ₁ : Kind ι₂} {κ₂ : Kind ι₃} → KripkeFunction Δ κ₁ κ₂ → Set
UniformNE :  ∀ {Δ : KEnv ι₁} {κ₁ : Kind ι₂} {κ₂ : Kind ι₃} → KripkeFunctionNE Δ κ₁ κ₂ → Set

convNE : κ₁ ≡ κ₂ → NeutralType Δ R[ κ₁ ] → NeutralType Δ R[ κ₂ ]
convNE refl n = n 

convKripkeNE₁ : ∀ {κ₁'} → κ₁ ≡ κ₁' → KripkeFunctionNE Δ κ₁ κ₂ → KripkeFunctionNE Δ κ₁' κ₂
convKripkeNE₁ refl f = f

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
  Uniform F × Uniform G × PointEqual-≋ {Δ₁} F G 
_≋_ {Δ₁} {κ = R[ κ₂ ]} (_<$>_ {κ₁} φ₁ n₁) (_<$>_ {κ₁'} φ₂ n₂) = 
  Σ[ pf ∈ (κ₁ ≡ κ₁') ]  
    UniformNE φ₁
  × UniformNE φ₂
  × (PointEqualNE-≋ (convKripkeNE₁ pf φ₁) φ₂
  × convNE pf n₁ ≡ n₂)
_≋_ {Δ₁} {κ = R[ κ₂ ]} (φ₁ <$> n₁) _ = ⊥
_≋_ {Δ₁} {R[ κ₂ ]} _ (φ₁ <$> n₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (row ρ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (x₂ ▹ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row (n , P) x₁) (row (m , Q) x₂) = (n , P) ≋R (m , Q)
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (ρ₂ ─ ρ₃) = ⊥
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
Env-≋ η₁ η₂ = ∀ {κ} (x : TVar _ κ) → (η₁ x) ≋ (η₂ x)

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
sym-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} (eq , rel) = sym eq  , sym-≋ rel
sym-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} (refl , eq-ρ) =
  refl , 
  (λ i → (sym (eq-ρ i .fst)) , (sym-≋ (eq-ρ i .snd)))
sym-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (sym-≋ rel₁) , (sym-≋ rel₂)
sym-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Unif-φ₁ , Unif-φ₂ , Ext , refl) = refl  , Unif-φ₂ , Unif-φ₁ , (λ r v → sym-≋ (Ext r v) ) , refl
refl-≋ₗ q = trans-≋ q (sym-≋ q)
refl-≋ᵣ q = refl-≋ₗ (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {F} {G} {H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ₗ (sym-≋ q)))
trans-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} (eq-l₁ , rel-τ₁) (eq-l₂ , rel-τ₂) = trans eq-l₁ eq-l₂  , trans-≋ rel-τ₁ rel-τ₂
trans-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} {row (o , R) _} (refl , rel₁) (refl , rel₂) = 
  refl , λ { i → trans (rel₁ i .fst) (rel₂ i .fst) , trans-≋ (rel₁ i .snd) (rel₂ i .snd) }
trans-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} {ρ₆ ─ ρ₅} (rel₁ , rel₂) (rel₃ , rel₄) = (trans-≋ rel₁ rel₃) , (trans-≋ rel₂ rel₄)
trans-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} {φ₃ <$> n₃} (refl , Unif-φ₁ , Unif-φ₂ , Ext₁ , refl) (refl , _ , Unif-φ₃ , Ext₂ , refl) = refl , Unif-φ₁ , Unif-φ₃ , (λ r v → trans-≋ (Ext₁ r v) (Ext₂ r v) ) , refl

trans-≋ᵣ {τ₁ = (n , P)} {τ₂ = (m , Q)} {τ₃ = (j , K)} (refl , rel₁) (refl , rel₂) = refl , (λ { i → trans (rel₁ i .fst) (rel₂ i .fst)  , trans-≋ (rel₁ i .snd) (rel₂ i .snd) })
--------------------------------------------------------------------------------
-- Pointwise extensionality (accordingly) forms a PER

refl-Extₗ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ F F
refl-Extₗ Ext ρ q = trans-≋ (Ext ρ q) (sym-≋ (Ext ρ (refl-≋ₗ (sym-≋ q))))

sym-Ext : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G F
sym-Ext Ext ρ q = trans-≋ (refl-≋ₗ (sym-≋ (Ext ρ (sym-≋ q)))) (sym-≋ (Ext ρ (sym-≋ q)))

refl-Extᵣ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G G
refl-Extᵣ Ext ρ q = refl-Extₗ (sym-Ext Ext) ρ q

trans-Ext : ∀ {F G H : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G H → PointEqual-≋ F H
trans-Ext Ext-FG Ext-GH ρ q = trans-≋ (Ext-FG ρ q) (trans-≋ (Ext-GH ρ (sym-≋ q)) (refl-Extᵣ Ext-GH ρ q))

-- --------------------------------------------------------------------------------
-- Reification of semantic equality and reflection of propositional equality
-- N.b. other definitions necessarily mutually recursive.

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
                        renRowₖNF ρ (reifyRow (n , P)) ≡ reifyRow (n , λ i → map₂ (renSem ρ) (Q i)) 

--------------------------------------------------------------------------------
-- reflect-≋ asserts that well kinded neutral types are in the relation

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
reflect-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = refl , (λ _ → ↻-ren-reflect) , ((λ _ → ↻-ren-reflect)) , (λ r V → reflect-≋ refl) , refl

--------------------------------------------------------------------------------
-- reify-≋ asserts that related semantic types reify to the same normal form.

reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ₁ `→ κ₂} {F} {G}
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflect-≋ {κ = κ₁} refl)))
reify-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , rel) = (cong₂ _▹ₙ_ refl (reify-≋ rel))
reify-≋ {κ = R[ κ ]} {row (zero , P) _} {row (_ , Q) _} (refl , eq) = refl
reify-≋ {κ = R[ κ ]} {row (suc n , P) _} {row (_ , Q) _} (refl , eq) = 
  cong-⦅⦆ (reifyRow-≋ {n = suc n} P Q λ i → eq i)
reify-≋ {κ = R[ κ ]} {a@(φ₁ <$> n₁) ─ V₂} {b@(φ₂ <$> n₂) ─ V₃} (rel₁@(refl , Ext , _ , _ , refl) , rel₂) = cong-─ (reify-≋ {V₁ = a} {V₂ = b} rel₁) (reify-≋ rel₂)

reify-≋ {κ = R[ κ ]} {(x₁ ▹ x₂) ─ ρ₁} {(x₃ ▹ x₄) ─ ρ₃} ((refl , rel₁) , rel₂) = cong-─ (cong (x₁ ▹ₙ_) (reify-≋ rel₁)) (reify-≋ rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (x₃ ▹ x₄)} {row (m , Q) x₂ ─ (x₅ ▹ x₆)} ((refl , rel₁) , refl , rel₂) = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel₁ )) (cong (x₃ ▹ₙ_) (reify-≋ rel₂))
reify-≋ {κ = R[ κ ]} {row ρ x₁ ─ row ρ₁ x₃} {(row ρ₂ x₂ ─ row ρ₃ x₄) {left ()}} (rel₁ , rel₂)
reify-≋ {κ = R[ κ ]} {row ρ x₁ ─ row ρ₁ x₃} {(row ρ₂ x₂ ─ row ρ₃ x₄) {right ()}} (rel₁ , rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (ρ₁ ─ ρ₃)} {row (n , Q) x₂ ─ (ρ₄ ─ ρ₅)} ((refl , rel₁) , rel₂) = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel₁)) (reify-≋ {V₁ = ρ₁ ─ ρ₃} {V₂ = ρ₄ ─ ρ₅} rel₂)
reify-≋ {κ = R[ κ ]} {row (n , P) x₁ ─ (φ₁ <$> n₁)} {row (n' , Q) x₂ ─ (φ₂ <$> n₂)} ((refl , rel) , rel') = cong-─ (cong-⦅⦆ (reifyRow-≋ P Q rel)) (reify-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} rel')
reify-≋ {κ = R[ κ ]} {(ρ₂ ─ ρ₄) ─ ρ₁} {(ρ₅ ─ ρ₆) ─ ρ₃} (rel₁ , rel₂) = cong-─ (reify-≋ {V₁ = ρ₂ ─ ρ₄} {ρ₅ ─ ρ₆} rel₁) (reify-≋ rel₂)
reify-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , _ , _ , Ext , refl) = cong₂ _<$>_ (cong `λ (reify-≋ (Ext S (` Z)))) refl

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

↻-ren-reify-R[κ] : ∀ (r : Renamingₖ Δ₁ Δ₂) (x y : SemType Δ₁ R[ κ ])  → x ≋ y → renₖNF r (reify x) ≡ reify (renSem r y)
↻-ren-reify-R[κ] r (φ₁ <$> τ₁) (φ₂ <$> τ₂) rel@(refl , Unif-φ₁ , Unif-φ₂ , Ext , refl) = cong₂ _<$>_ (cong `λ (trans (↻-ren-reify (liftₖ r) (Ext S (` Z))) (reify-≋ (Unif-φ₂ S (liftₖ r) (` Z))))) refl
↻-ren-reify-R[κ] r (x₁ ▹ x₂) (x₃ ▹ x₄) (refl , rel) = (cong₂ (_▹ₙ_) refl (↻-ren-reify r rel))
↻-ren-reify-R[κ] r (row (n , P) x₁) (row (m , Q) x₂) (refl , i) = (cong-⦅⦆ (↻-ren-reifyRow P Q r i))
↻-ren-reify-R[κ] r (x₁ ─ x₂) (y₁ ─ y₂) (rel₁ , rel₂) = ↻-ren-reify-─ r rel₁ rel₂ 

↻-ren-reify-─ r {φ <$> x₁} {x} {φ₁ <$> x₂} {y} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r (φ <$> x₁) (φ₁ <$> x₂) rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-─ r a@{x₁ ▹ x₂} {x} b@{x₃ ▹ x₄} {y} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-─ r {a@(row (n , P) oP)} x@{φ <$> x₁} {b@(row (m , Q) oQ)} y@{φ₁ <$> x₂} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-─ r {a@(row (n , P) oP)} x@{x₁ ▹ x₂} {b@(row (m , Q) oQ)} y@{x₃ ▹ x₄} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-─ r {a@(row (n , P) oP)} {row ρ x₁} {b@(row (m , Q) oQ)} {row ρ₁ x₂} rel₁ rel₂ {left ()}
↻-ren-reify-─ r {a@(row (n , P) oP)} {row ρ x₁} {b@(row (m , Q) oQ)} {row ρ₁ x₂} rel₁ rel₂ {right ()}
↻-ren-reify-─ r {a@(row (n , P) oP)} x@{x₁ ─ x₂} {b@(row (m , Q) oQ)} y@{y₁ ─ y₂} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-─ r a@{ρ₂ ─ ρ₁} {x} b@{ρ₄ ─ ρ₃} {y} rel₁ rel₂ = cong-─ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)

↻-ren-reifyRow {n = zero} P Q ρ eq = refl
↻-ren-reifyRow {n = suc n} P Q ρ eq = 
  cong₂ _∷_ 
    (cong₂ _,_ (eq fzero .fst) (↻-ren-reify ρ (eq fzero .snd))) -- (↻-ren-reify ρ (eq fzero)) 
    (↻-ren-reifyRow {n = n} (P ∘ fsuc) (Q ∘ fsuc) ρ (eq ∘ fsuc)) 

↻-ren-reify {κ = ★} r {V₁} {V₂} refl = refl 
↻-ren-reify {κ = L} r {V₁} {V₂} refl = refl
↻-ren-reify {Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{F} g@{G} q@(Unif-F , Unif-G , Ext) = 
  cong `λ 
    (trans 
      (↻-ren-reify (liftₖ ρ) (Ext S (reflect-≋ (refl {x = ` Z})))) 
      (reify-≋ (trans-≋ 
        (Unif-G S (liftₖ ρ) _ _ (reflect-≋ refl)) 
        (refl-Extᵣ Ext (S ∘ ρ) (↻-ren-reflect (liftₖ ρ) (` Z))))))
↻-ren-reify {κ = R[ κ ]} r {V₁} {V₂} rel = ↻-ren-reify-R[κ] r V₁ V₂ rel 

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
↻-ren-reflect {κ = R[ κ ]} ρ τ = reflect-≋ {κ = R[ κ ]} refl

-- -- --------------------------------------------------------------------------------
-- -- -- Functorial actions

renSem-id-≋    : ∀ {V₁ V₂ : SemType Δ₁ κ} → V₁ ≋ V₂  → (renSem id V₁) ≋ V₂
renSem-id-≋ {κ = ★} refl = renₖNF-id _
renSem-id-≋ {κ = L} refl = renₖNF-id _
renSem-id-≋ {κ = κ `→ κ₁} {F} {G} e = e
renSem-id-≋ {κ = R[ κ ]} {(l₁ ▹ τ₁)} {(l₂ ▹ τ₂)} (refl , rel) = renₖNE-id l₁ , renSem-id-≋ rel
renSem-id-≋ {κ = R[ κ ]} {row (n , P) _} {row (n , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-id-≋ (eq i .snd) } -- renSem-id-≋ ∘ eq
renSem-id-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (renSem-id-≋ rel₁) , (renSem-id-≋ rel₂)
renSem-id-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Ext , Unif-φ₁ , Unif-φ₂ , refl) = refl , Ext , Unif-φ₁ , Unif-φ₂ , renₖNE-id n₁

renSem-comp-≋  : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂)(ρ₂ : Renamingₖ Δ₂ Δ₃){V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≋ (renSem ρ₂ (renSem ρ₁ V₂))
renSem-comp-≋ {κ = ★} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = L} ρ₁ ρ₂ refl = renₖNF-comp _ _ _
renSem-comp-≋ {κ = κ `→ κ₁} ρ₁ ρ₂ {F} {G} (Unif-F , Unif-G , Ext) = 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {l₁ ▹ τ₁} {l₂ ▹ τ₂} (refl , rel) = (renₖNE-comp ρ₁ ρ₂ l₁) , (renSem-comp-≋ ρ₁ ρ₂ rel)
renSem-comp-≋ {κ = R[ κ ]} ρ₁ ρ₂ {row (n , P) _} {row (_ , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-comp-≋  ρ₁ ρ₂ (eq i .snd) }
renSem-comp-≋ {κ = R[ κ ]} r₁ r₂ {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Unif-φ₁ , Unif-φ₂ , Ext , refl) = 
  refl , (λ ρ₁ ρ₂ V → Unif-φ₁ (ρ₁ ∘ r₂ ∘ r₁) ρ₂ V) , (λ ρ₁ ρ₂ V → Unif-φ₂ (ρ₁ ∘ r₂ ∘ r₁) ρ₂ V) , (λ r₃ V → Ext (r₃ ∘ r₂ ∘ r₁) V) , renₖNE-comp r₁ r₂ n₁ 
renSem-comp-≋ {κ = R[ κ ]} r₁ r₂ {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (renSem-comp-≋ r₁ r₂ rel₁) , (renSem-comp-≋ r₁ r₂ rel₂)

↻-lift-weaken-≋ₖ : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → 
                renSem (liftₖ {κ = κ'} ρ) (renSem S V₁) ≋ renSem S (renSem ρ V₂)
↻-lift-weaken-≋ₖ {κ' = κ'} ρ {V₁} {V₂} v = 
  trans-≋ 
    (sym-≋ (renSem-comp-≋ (S {κ₂ = κ'}) (liftₖ ρ) (sym-≋ v))) 
    (renSem-comp-≋ ρ S (refl-≋ᵣ v))
