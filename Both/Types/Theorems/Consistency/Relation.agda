{-# OPTIONS --safe #-}
module Rome.Both.Types.Theorems.Consistency.Relation where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Properties.Renaming
open import Rome.Both.Types.Properties.Substitution
open import Rome.Both.Types.Equivalence.Properties

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming 
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming
open import Rome.Both.Types.Semantic.NBE


open import Rome.Both.Types.Equivalence.Relation
open import Rome.Both.Types.Equivalence.Properties
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Consistency of type normalization: 
--   All types are equivalent (under ≡t) to their normal forms.

infix 0 ⟦_⟧≋_
⟦_⟧≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
⟦_⟧≋ne_ : ∀ {κ} → Type Δ κ → NeutralType Δ κ → Set

⟦_⟧r≋_ : ∀ {κ} → SimpleRow Type Δ R[ κ ] → Row (SemType Δ κ) → Set
⟦_⟧≋₂_ : ∀ {κ} → Label × Type Δ κ → Label × SemType Δ κ → Set
⟦ (l₁ , τ) ⟧≋₂ (l₂ , V) = (l₁ ≡ l₂) × (⟦ τ ⟧≋ V)

SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set
SoundKripkeNE : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunctionNE Δ₁ κ₁ κ₂ → Set

-- τ is equivalent to neutral `n` if it's equivalent 
-- to the η and map-id expansion of n
⟦_⟧≋ne_ τ n = τ ≡t ⇑ (η-norm n)

⟦_⟧≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {κ = L} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (row (n , P)  oρ) =
    let xs = ⇑Row (reifyRow (n , P)) in 
    (τ ≡t ⦅ xs ⦆ (fromWitness (Ordered⇑ (reifyRow (n , P)) (reifyRowOrdered' n P oρ)))) × 
    (⟦ xs ⟧r≋ (n , P))
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = (τ ≡t (⇑NE l ▹ ⇑ (reify V))) × (⟦ ⇑ (reify V) ⟧≋ V)
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ─ ρ₁) {nr}) = (τ ≡t (⇑ (reify ((ρ₂ ─ ρ₁) {nr})))) × (⟦ ⇑ (reify ρ₂) ⟧≋ ρ₂) × (⟦ ⇑ (reify ρ₁) ⟧≋ ρ₁)
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (φ <$> n) = 
  ∃[ f ] ((τ ≡t (f <$> ⇑NE n)) × (SoundKripkeNE f φ))
⟦ [] ⟧r≋ (zero , P) = ⊤
⟦ [] ⟧r≋ (suc n , P) = ⊥
⟦ x ∷ ρ ⟧r≋ (zero , P) = ⊥
⟦ x ∷ ρ ⟧r≋ (suc n , P) =  (⟦ x ⟧≋₂ (P fzero)) × ⟦ ρ ⟧r≋ (n , P ∘ fsuc)

SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≋ V → 
      ⟦ (renₖ ρ f · v) ⟧≋ (renKripke ρ F ·V V)

SoundKripkeNE {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂} (r : Renamingₖ Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≋ne  V → 
      ⟦ (renₖ r f · v) ⟧≋ (F r V)

--------------------------------------------------------------------------------
-- Neutral types are equivalent to their η-normalizations

η-norm-≡t'ren : ∀ (τ : NeutralType Δ₁ κ) {r : Renamingₖ Δ₁ Δ₂} → 
                  ⇑ (renₖNF r (η-norm τ)) ≡t ⇑NE (renₖNE r τ)
η-norm-≡t'ren {κ = ★} τ = eq-refl
η-norm-≡t'ren {κ = L} τ = eq-refl
η-norm-≡t'ren {κ = κ `→ κ₁} τ {r} = 
  eq-trans 
    (eq-λ (η-norm-≡t'ren (renₖNE S τ · reify (reflect (` Z))) {liftₖ r})) 
  (eq-trans 
    (eq-λ (eq-· 
      (inst (trans (↻-ren-⇑NE (liftₖ r) (renₖNE S τ)) (cong (renₖ (liftₖ r)) (↻-ren-⇑NE S  τ)))) 
      (η-norm-≡t'ren (` Z) {liftₖ r}))) 
  (eq-trans (eq-λ (eq-· (eq-trans (inst (↻-liftₖ-weaken r (⇑NE τ))) (inst (cong (renₖ S) (sym (↻-ren-⇑NE  r τ))))) eq-refl)) 
    (eq-sym eq-η)))
η-norm-≡t'ren {κ = R[ κ ]} τ {r} = eq-trans (eq-<$> (eq-λ (η-norm-≡t'ren (` Z) {liftₖ r})) eq-refl) eq-map-id

η-norm-≡t : ∀ (τ : NeutralType Δ κ) → ⇑ (η-norm τ) ≡t ⇑NE τ 
η-norm-≡t  τ = 
  eq-trans 
    (subst 
      (λ X → ⇑ X ≡t ⇑NE (renₖNE id τ)) {x = renₖNF id (η-norm τ)} 
      (renₖNF-id  (η-norm τ)) 
      ((η-norm-≡t'ren τ {id}))) 
  (inst (cong ⇑NE (renₖNE-id τ)))

--------------------------------------------------------------------------------
-- - Types equivalent to neutral types under ≡t reflect to equivalence under _≋_, and 
-- - Types related under _≋_ have reifications equivalent under _≡t_

reflect-⟦⟧≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡t ⇑NE υ → ⟦ τ ⟧≋ (reflect υ)
reify-⟦⟧≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
               ⟦ τ ⟧≋ V → τ ≡t ⇑ (reify V)

reflect-⟦⟧≋ {κ = ★} e = e  
reflect-⟦⟧≋ {κ = L} e = e 
reflect-⟦⟧≋ {κ = κ₁ `→ κ₂} {τ} {υ} e = 
    λ ρ q → reflect-⟦⟧≋ 
    (eq-· 
        (eq-sym (eq-trans (inst (↻-ren-⇑NE ρ υ)) 
            (renₖ-≡t ρ (eq-sym e)))) 
        (reify-⟦⟧≋ q)) 
reflect-⟦⟧≋ {κ = R[ κ ]} e = 
  `λ (⇑ (η-norm (` Z))) , eq-trans (eq-sym eq-map-id) (eq-<$> (eq-λ (eq-sym (η-norm-≡t (` Z)))) e) , 
  λ r {v = v} {V} eq → reflect-⟦⟧≋ (eq-trans 
    (eq-· eq-refl eq) 
    (eq-trans 
      eq-β 
      (eq-trans 
        (inst (sym (↻-subₖ-renₖ (⇑ (reify (reflect _)))))) 
        (eq-trans 
          (subₖ-≡t (η-norm-≡t (` Z))) (η-norm-≡t V)))))

reify-⟦⟧≋ {κ = ★} {τ} {V} e = e 
reify-⟦⟧≋ {κ = L} {τ} {V} e = e
reify-⟦⟧≋ {κ = κ₁ `→ κ₂} {τ} {F} e = 
    eq-trans 
        eq-η 
        (eq-λ (eq-trans 
            (reify-⟦⟧≋ (e S (reflect-⟦⟧≋ eq-refl))) 
            eq-refl))

reify-⟦⟧≋ {κ = R[ κ ]} {τ} {row (zero , P) _} (eq , I) = eq
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {row (suc n , P) _} (eq , I) = eq-trans eq (eq-row (eq-cons refl eq-refl (instᵣ refl)))
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {l ▹ V} eq = fst eq
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {V₂ ─ V₁} eq = eq .fst
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {φ <$> ρ} (f , eq , rel) = 
  eq-trans 
    eq 
    (eq-<$> 
      (eq-trans 
        eq-η
        (eq-λ (reify-⟦⟧≋ (rel S (eq-sym (η-norm-≡t (` Z))))))) 
      eq-refl)

reify-⟦⟧r≋ : ∀ {xs : SimpleRow Type Δ R[ κ ]} {V :  Row (SemType Δ κ)} → 
               ⟦ xs ⟧r≋ V → xs ≡r ⇑Row (reifyRow V)
reify-⟦⟧r≋ {xs = []} {zero , P} rel = eq-[]
reify-⟦⟧r≋ {xs = x ∷ xs} {suc n , P} (eq , I) = eq-cons (eq .fst) (reify-⟦⟧≋ (eq .snd)) (reify-⟦⟧r≋ I)

--------------------------------------------------------------------------------
-- Equivalent types relate to the same semantic types

subst-⟦⟧≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
  τ₁ ≡t τ₂ → 
  {V : SemType Δ κ} → 
  ⟦ τ₁ ⟧≋ V → 
  ---------
  ⟦ τ₂ ⟧≋ V 

subst-⟦⟧≋ {κ = ★} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≋ {κ = L} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≋ {κ = κ `→ κ₁} {τ₁ = τ₁} {τ₂} q {F} rel = λ ρ {v} {V} rel-v → subst-⟦⟧≋ (eq-· (renₖ-≡t ρ q) eq-refl) (rel ρ rel-v)
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {φ <$> n} (f , eq , rel) = f , (eq-trans (eq-sym q) eq) , rel
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {row (n , P) _} (eq , I) = eq-trans (eq-sym q) eq , I
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {l ▹ τ} (eq , rel) = eq-trans (eq-sym q) eq , rel
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {V₂ ─ V₁} (eq , rel₁ , rel₂) = eq-trans (eq-sym q) eq , rel₁ , rel₂

--------------------------------------------------------------------------------
-- Equivalent rows relate to the same semantic rows

subst-⟦⟧r≋ : ∀ {xs ys : SimpleRow Type Δ R[ κ ]} → 
  xs ≡r ys → 
  {ρ : Row (SemType Δ κ)} → 
  ⟦ xs ⟧r≋ ρ → 
  ---------
  ⟦ ys ⟧r≋ ρ

subst-⟦⟧r≋ eq-[] rel = rel
subst-⟦⟧r≋ (eq-cons refl eq-x eq-xs) {suc n , P} ((eq , rel-x) , rel-xs) = (eq , subst-⟦⟧≋ eq-x rel-x) , (subst-⟦⟧r≋ eq-xs rel-xs) 

-- --------------------------------------------------------------------------------
-- -- Stability rule for reification

refl-⟦⟧≋ : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
                ⟦ v ⟧≋ V  →
               ⟦ ⇑ (reify V) ⟧≋ V 
refl-⟦⟧≋ {κ = κ} rel-v = subst-⟦⟧≋ (reify-⟦⟧≋ rel-v) rel-v

refl-⟦⟧r≋ : ∀ {xs : SimpleRow Type Δ R[ κ ]} {ρ : Row (SemType Δ κ)} → 
                ⟦ xs ⟧r≋ ρ  →
               ⟦ ⇑Row (reifyRow ρ) ⟧r≋ ρ
refl-⟦⟧r≋ {κ = κ} rel = subst-⟦⟧r≋ (reify-⟦⟧r≋ rel) rel
    

--------------------------------------------------------------------------------
-- renaming respects consistency relation

ren-⟦⟧≋ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) 
           {v : Type Δ₁ κ} 
           {V : SemType Δ₁ κ} → 
           ⟦ v ⟧≋ V → 
           ⟦ renₖ ρ v ⟧≋ renSem ρ V

-- We need to state the renaming lemma over both semantic and syntactic row renaming
ren-⟦⟧r≋ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → 
             (n : ℕ) (P : Fin n → Label × SemType Δ₁ κ) → 
           ⟦ ⇑Row (reifyRow (n , P)) ⟧r≋ (n , P) → 
           ⟦ ⇑Row (reifyRow (n , map₂ (renSem ρ) ∘ P)) ⟧r≋ (n , map₂ (renSem ρ) ∘ P)

ren-⟦⟧r≋' : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → 
             (n : ℕ) (P : Fin n → Label × SemType Δ₁ κ) → 
           ⟦ ⇑Row (reifyRow (n , P)) ⟧r≋ (n , P) → 
           ⟦ renRowₖ ρ (⇑Row (reifyRow (n , P))) ⟧r≋ renRow ρ (n , P)


-- and that renaming commutes over (⇑ ∘ reify)
↻-ren-⇑-reify-─ : ∀ (r : Renamingₖ Δ₁ Δ₂) (V₂ V₁ : RowType Δ₁ (λ Δ → SemType Δ κ) R[ κ ]) →
                ⟦ ⇑ (reify V₂) ⟧≋ V₂ →
                ⟦ ⇑ (reify V₁) ⟧≋ V₁ →  
                (ev : NotRow V₂ or NotRow V₁) → 
                renₖ r (⇑ (reify ((V₂ ─ V₁) {ev}))) ≡t ⇑ (reify ((renSem r V₂ ─ renSem r V₁) {nrRenSem' r V₂ V₁ ev}))
↻-ren-⇑-reify :  ∀ (r : Renamingₖ Δ₁ Δ₂) (V : RowType Δ₁ (λ Δ → SemType Δ κ) R[ κ ]) →
                ⟦ ⇑ (reify V) ⟧≋ V →
                renₖ r (⇑ (reify V)) ≡t ⇑ (reify (renSem r V))

--------------------------------------------------------------------------------
-- renaming respects consistency relation (definitions)

↻-ren-⇑-reify r (φ <$> N) (f , eq , rel₁) = 
  (eq-trans 
    (renₖ-≡t r eq) 
    (eq-<$> 
      (eq-trans 
        eq-η 
        (eq-λ (eq-trans 
          (eq-· (inst (sym (renₖ-comp r S f))) eq-refl)
          ((reify-⟦⟧≋ (rel₁ (S ∘ r) (eq-sym (η-norm-≡t (` Z))))))))) 
      (inst (sym (↻-ren-⇑NE r N)))))
↻-ren-⇑-reify r (x₁ ▹ x₂) rel = 
  eq-▹ 
    (inst (sym (↻-ren-⇑NE r x₁))) 
    (reify-⟦⟧≋ (ren-⟦⟧≋ r (rel .snd)))
↻-ren-⇑-reify r (row (n , P) x₁) rel = eq-row (reify-⟦⟧r≋ (ren-⟦⟧r≋' r n P (rel .snd)))
↻-ren-⇑-reify r ((V₂ ─ V₁) {nr}) (eq , rel₂ , rel₁) = ↻-ren-⇑-reify-─ r V₂ V₁ rel₂ rel₁ nr                 

↻-ren-⇑-reify-─ r (l ▹ τ) V₂ rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify r (l ▹ τ) rel₂) (↻-ren-⇑-reify r V₂ rel₁)
↻-ren-⇑-reify-─ r ρ₂@(row ρ x₁) ρ₁@(φ <$> x₂) rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-─ r ρ₂@(row ρ x₁) ρ₁@(x₂ ▹ x₃) rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-─ r (row ρ x₁) (row ρ₁ x₂) rel₂ rel₁ (left ())
↻-ren-⇑-reify-─ r (row ρ x₁) (row ρ₁ x₂) rel₂ rel₁ (right ())
↻-ren-⇑-reify-─ r ρ₂@(row ρ x₁) ρ₁@(V₂ ─ V₃) rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-─ r ((ρ₂ ─ ρ₁) {nr}) V₂ rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify-─ r ρ₂ ρ₁ (rel₂ .snd .fst) (rel₂ .snd .snd) nr) (↻-ren-⇑-reify r V₂ rel₁)
↻-ren-⇑-reify-─ r (φ <$> n) V₂ rel₂ rel₁ ev = eq-─ (↻-ren-⇑-reify r (φ <$> n) rel₂) (↻-ren-⇑-reify r V₂ rel₁)

ren-⟦⟧r≋' ρ zero P rel = tt
ren-⟦⟧r≋' ρ (suc n) P (rel-fzero , rel-fsuc) = (refl , (ren-⟦⟧≋ ρ (rel-fzero .snd))) , ren-⟦⟧r≋' ρ n  (P ∘ fsuc) rel-fsuc 
ren-⟦⟧r≋ ρ zero P rel = tt
ren-⟦⟧r≋ ρ (suc n) P (rel-fzero , rel-fsuc) = (refl , refl-⟦⟧≋ (ren-⟦⟧≋ ρ (rel-fzero .snd))) , ren-⟦⟧r≋ ρ n (λ x → P (fsuc x)) rel-fsuc

ren-⟦⟧≋ {κ = ★} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≋ {κ = L} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≋ {κ = κ `→ κ₁} ρ₁ {v₁} {V₁} rel-v₁ ρ₂ {v₂} {V₂} rel-v₂  = subst-⟦⟧≋ (eq-· (inst (renₖ-comp ρ₁ ρ₂ v₁)) eq-refl) (rel-v₁ (ρ₂ ∘ ρ₁) rel-v₂)
ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {φ <$> n} (f , eq , rel-v) = 
  renₖ ρ f , 
  eq-trans (renₖ-≡t ρ eq) (eq-<$> eq-refl (inst (sym (↻-ren-⇑NE ρ n)))) , 
  (λ r v-eq → subst-⟦⟧≋ (eq-· (inst (renₖ-comp ρ r f)) eq-refl) (rel-v (r ∘ ρ) v-eq)) 
ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {row (n , P) _} (eq , rel) = 
  eq-trans 
    (renₖ-≡t ρ eq) 
    (eq-row ( reify-⟦⟧r≋ (ren-⟦⟧r≋' ρ n P rel))) , 
  ren-⟦⟧r≋ ρ n P rel
ren-⟦⟧≋ {κ = R[ κ ]} r {v} {l ▹ V} (eq , rel) = 
  eq-trans 
    (renₖ-≡t r eq) 
    (eq-▹ 
      (inst (sym (↻-ren-⇑NE r l))) 
      (reify-⟦⟧≋ (ren-⟦⟧≋ r rel))) , refl-⟦⟧≋  (ren-⟦⟧≋ r rel)
ren-⟦⟧≋ {κ = R[ κ ]} r {v} {(V₂ ─ V₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans (renₖ-≡t r eq) (↻-ren-⇑-reify-─ r V₂ V₁ rel₂ rel₁ nr)) , 
  (refl-⟦⟧≋ (ren-⟦⟧≋ r rel₂)) , 
  (refl-⟦⟧≋ (ren-⟦⟧≋ r rel₁))

--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments
 
⟦_⟧≋e_ : ∀ {Δ₁ Δ₂} → Substitutionₖ Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
⟦_⟧≋e_ {Δ₁} σ η = ∀ {κ} (α : TVar Δ₁ κ) → ⟦ (σ α) ⟧≋ (η α)

-- Identity relation
idSR : ∀ {Δ₁} →  ⟦ ` ⟧≋e (idEnv {Δ₁})
idSR α = reflect-⟦⟧≋ eq-refl

--------------------------------------------------------------------------------
-- Extended substitutions relate to extended environments

extend-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
             ⟦ σ ⟧≋e η →
             ∀ {τ : Type Δ₂ κ} {V : SemType Δ₂ κ} → 
             ⟦ τ ⟧≋ V → 
             ⟦ (extendₖ σ τ) ⟧≋e (extende η V)
extend-⟦⟧≋ p q Z = q
extend-⟦⟧≋ p q (S x) = p x

--------------------------------------------------------------------------------
-- Weakened substitutions relate to weakened environments
 
weaken-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
           ⟦ σ ⟧≋e η → 
           ⟦ liftsₖ {κ = κ} σ ⟧≋e (extende (λ {κ'} v → renSem S (η v)) (reflect (` Z)))
weaken-⟦⟧≋ e Z = reflect-⟦⟧≋ eq-refl
weaken-⟦⟧≋ e (S α) = ren-⟦⟧≋ S (e α)           

--------------------------------------------------------------------------------
--  Substituting syntactic substitutions in related environments

substEnv-⟦⟧≋ : ∀ {σ₁ σ₂ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
             (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) →
             ⟦ σ₁ ⟧≋e η →
             ⟦ σ₂ ⟧≋e η
substEnv-⟦⟧≋ eq rel x rewrite sym (eq x) = rel x

--------------------------------------------------------------------------------
-- A necessary lemma difficult to describe

map₂-⟦⟧≋ : ∀ {n : ℕ} 
             {P : Fin n → Label × SemType Δ₂ κ₁} 
             {σ : Substitutionₖ Δ₁ Δ₂}
             {η : Env Δ₁ Δ₂}
             (f : Type Δ₁ (κ₁ `→ κ₂)) → 
             ⟦ subₖ σ f ⟧≋ (eval f η) → 
             ⟦ ⇑Row (reifyRow (n , P)) ⟧r≋ (n , P) → 
            ⟦ ⇑Row (reifyRow (n , map₂ (eval f η id) ∘ P)) ⟧r≋ (n , (map₂ (eval f η id)) ∘ P)
map₂-⟦⟧≋ {n = zero} F rel-f rel = tt
map₂-⟦⟧≋ {n = suc n} F rel-f ((refl , rel-fzero) , rel-fsuc) = 
  (refl , (refl-⟦⟧≋ (rel-f id rel-fzero))) , map₂-⟦⟧≋ {n = n} F rel-f rel-fsuc 

--------------------------------------------------------------------------------
-- To be clear, although we use an existential in defining ⟦ τ ⟧≋(φ <$> n), 
-- we know more precisely that τ ≡t `λ (⇑ (reify (φ₂ S (` Z)))) <$> ⇑NE n.

reifySoundKripkeNE-≡t : ∀ {τ : Type Δ R[ κ₂ ]} {f : Type Δ (κ₁ `→ κ₂)} {n : NeutralType Δ R[ κ₁ ]} 
        {φ : KripkeFunctionNE Δ κ₁ κ₂} → 
        τ ≡t f <$> ⇑NE n → 
        SoundKripkeNE f φ → 
        τ ≡t (`λ (⇑ (reify (φ S (` Z)))) <$> ⇑NE n)
reifySoundKripkeNE-≡t eq rel-f = 
  (eq-trans 
      eq
      (eq-<$> 
        (eq-trans eq-η (eq-λ (reify-⟦⟧≋ (rel-f S {` Z} (eq-sym (η-norm-≡t (` Z))))))) 
        eq-refl))
