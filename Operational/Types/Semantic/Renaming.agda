{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax

open import Data.List.Properties using (map-id ; map-cong; map-∘)
import Data.List.Relation.Unary.All as All
open All using (All)

-- --------------------------------------------------------------------------------
-- -- Renaming semantic types.

renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renRow : Renamingₖ Δ₁ Δ₂ → Row Δ₁ R[ κ ] → Row Δ₂ R[ κ ]

renSem {κ = ★} r τ = renₖNF r τ
renSem {κ = L} r τ = renₖNF r τ
renSem {κ = κ `→ κ₁} r F = renKripke r F
renSem {κ = R[ κ ]} r (left x) = left (renₖNE r x)
renSem {κ = R[ κ ]} r (right (n , P)) = right (n , (λ i → (renSem {κ = L} r ((P i) .fst)) , (renSem r (P i .snd))))

renRow φ (n , P) = n , fmap× {Ty = SemType} (renSem φ) ∘ P 

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

