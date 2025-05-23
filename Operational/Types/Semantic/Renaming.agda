{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
-- open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax

open import Data.List.Properties using (map-id ; map-cong; map-∘)
import Data.List.Relation.Unary.All as All
open All using (All)

-- --------------------------------------------------------------------------------
-- -- Renaming semantic types.

renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renRow : Renamingₖ Δ₁ Δ₂ → 
         Row (SemType Δ₁ κ) → 
         Row (SemType Δ₂ κ)

orderedRenRow : ∀ {n} {P : Fin n → Label × SemType Δ₁ κ} → (r : Renamingₖ Δ₁ Δ₂) → 
                OrderedRow' n P → OrderedRow' n (λ i → (P i .fst) , renSem r (P i .snd))

nrRenSem : ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             NotRow ρ → NotRow (renSem r ρ)

nrRenSem' : ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ₂ ρ₁ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             (nr : NotRow ρ₂ or NotRow ρ₁) → NotRow (renSem r ((ρ₂ ─ ρ₁) {nr}))


-- renₖNF-≪ : ∀ {l₁ l₂ : NormalType Δ₁ L} (r : Renamingₖ Δ₁ Δ₂) → l₁ ≪ l₂ → renₖNF r l₁ ≪ renₖNF r l₂
-- renₖNF-≪ {l₁ = lab l₁} {lab l} r l₁<l₂ = l₁<l₂

renSem {κ = ★} r τ = renₖNF r τ
renSem {κ = L} r τ = renₖNF r τ
renSem {κ = κ `→ κ₁} r F = renKripke r F
-- renSem {κ = R[ κ ]} r (ne x) = ne (renₖNE r x)
renSem {κ = R[ κ ]} r (l ▹ τ) = (renₖNE r l) ▹ renSem r τ
renSem {κ = R[ κ ]} r (row (n , P) q) = row (n , ( overᵣ (renSem r) ∘ P)) (orderedRenRow r q)
renSem {κ = R[ κ ]} r (ne x) = ne (renₖNE r x)
renSem {κ = R[ κ ]} r ((ρ₂ ─ ρ₁) {left nr}) = (renSem r ρ₂ ─ renSem r ρ₁) {nr = left (nrRenSem r ρ₂ nr)}
renSem {κ = R[ κ ]} r ((ρ₂ ─ ρ₁) {right nr}) = (renSem r ρ₂ ─ renSem r ρ₁) {nr = right (nrRenSem r ρ₁ nr)}
-- renSem {κ = R[ κ ]} r (ρ₂ ─₂ ρ₁) = {!!}

nrRenSem r (ne x) nr = tt
nrRenSem r (x ▹ x₁) nr = tt
nrRenSem r ((ρ ─ ρ₁) {nr'}) nr = nrRenSem' r ρ ρ₁ nr'  

nrRenSem' r ρ₂ ρ₁ (left x) = tt
nrRenSem' r ρ₂ ρ₁ (right y) = tt

orderedRenRow {n = zero} {P} r o = tt
orderedRenRow {n = suc zero} {P} r o = tt
orderedRenRow {n = suc (suc n)} {P} r (l₁<l₂ , o) =  l₁<l₂  , (orderedRenRow {n = suc n} {P ∘ fsuc} r o)

renRow φ (n , P) = n , overᵣ (renSem φ) ∘ P 

-- --------------------------------------------------------------------------------
-- -- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ

-- --------------------------------------------------------------------------------
-- -- Functor laws for renaming as a functorial action

-- renSem-id : ∀ (V : SemType Δ κ) → renSem id V ≡ V 
-- map-id' : ∀ {A : Set} (f : A → A) → (∀ (x : A) → f x ≡ x) → (xs : List A) → map f xs ≡ xs
-- map-id' f eq [] = refl
-- map-id' f eq (x ∷ xs) rewrite eq x | map-id' f eq xs = refl

-- renSem-id {κ = ★} V = renₖNF-id V
-- renSem-id {κ = L} V = renₖNF-id V
-- renSem-id {κ = κ `→ κ₁} F = refl
-- renSem-id {κ = R[ κ ]} (left x) = cong left (renₖNE-id x)
-- renSem-id {κ = R[ κ ]} (right (n , P))  = cong right (cong (n ,_) {!renSem-id !})

-- renSem-comp : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V : SemType Δ₁ κ) → 
--              (renSem (ρ₂ ∘ ρ₁) V) ≡ (renSem ρ₂ (renSem ρ₁ V))
-- renSem-comp {κ = ★} ρ₁ ρ₂ V = renₖNF-comp _ _ _
-- renSem-comp {κ = L} ρ₁ ρ₂ V = renₖNF-comp _ _ _
-- renSem-comp {κ = κ `→ κ₁} ρ₁ ρ₂ F = refl
-- renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ (neV x) = cong neV (renₖNE-comp _ _ _)
-- renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ (l ▹V τ) = (cong₂ _▹V_ (renₖNF-comp _ _ _) (renSem-comp _ _ _))
-- renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ εV = refl
-- renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ ⦅ ρ ⦆V = 
--   cong ⦅_⦆V 
--   (trans 
--     (map-cong (renSem-comp ρ₁ ρ₂) ρ) 
--     (map-∘ ρ))

