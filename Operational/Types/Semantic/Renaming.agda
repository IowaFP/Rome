{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)


open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming


open import Rome.Operational.Types.Semantic.Syntax

--------------------------------------------------------------------------------
-- Renaming semantic types.

renKripke : Renaming Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ

renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = L} ρ τ = ren ρ τ
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right F) = right (renKripke ρ F)

renSem {κ = R[ ★ ]} ρ τ = ren ρ τ
renSem {κ = R[ L ]} ρ τ = ren ρ τ
renSem {κ = R[ κ `→ κ₁ ]} ρ (left τ) = left (renNE ρ τ)
renSem {κ = R[ κ `→ κ₁ ]} ρ (right (l , left x)) = right (ren ρ l , left (renNE ρ x))
renSem {κ = R[ κ `→ κ₁ ]} ρ (right (l , right F)) = right (ren ρ l , right (renKripke ρ F))
renSem {κ = R[ R[ κ ] ]} ρ (left x) = left (renNE ρ x)
renSem {κ = R[ R[ κ ] ]} ρ (right (l , τ)) = right (ren ρ l , renSem ρ τ)

-- --------------------------------------------------------------------------------
-- -- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ

--------------------------------------------------------------------------------
-- Functor laws for renaming as a functorial action

renSem-id : ∀ (V : SemType Δ κ) → renSem id V ≡ V 
renSem-id {κ = ★} V = ren-id V
renSem-id {κ = L} V = ren-id V
renSem-id {κ = κ `→ κ₁} (left x) = cong left (ren-id-ne x)
renSem-id {κ = κ `→ κ₁} (right y) = cong right refl
renSem-id {κ = R[ ★ ]} V = ren-id V
renSem-id {κ = R[ L ]} V = ren-id V
renSem-id {κ = R[ κ `→ κ₁ ]} (left x) = cong left (ren-id-ne x)
renSem-id {κ = R[ κ `→ κ₁ ]} (right (l , left f)) = cong right (cong₂ _,_ (ren-id l) (cong left (ren-id-ne f)))
renSem-id {κ = R[ κ `→ κ₁ ]} (right (l , right F)) = cong right (cong₂ _,_ (ren-id l) (cong right refl))
renSem-id {κ = R[ R[ κ ] ]} (left x) = cong left (ren-id-ne x)
renSem-id {κ = R[ R[ κ ] ]} (right (l , F)) = cong right (cong₂ _,_ (ren-id l) (renSem-id F))


renSem-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (V : SemType Δ₁ κ) → 
             (renSem (ρ₂ ∘ ρ₁) V) ≡ (renSem ρ₂ (renSem ρ₁ V))
renSem-comp {κ = ★} ρ₁ ρ₂ V = ren-comp _ _ _
renSem-comp {κ = L} ρ₁ ρ₂ V = ren-comp _ _ _
renSem-comp {κ = κ `→ κ₁} ρ₁ ρ₂ (left x) = cong left (ren-comp-ne _ _ _)
renSem-comp {κ = κ `→ κ₁} ρ₁ ρ₂ (right y) = cong right refl
renSem-comp {κ = R[ ★ ]} ρ₁ ρ₂ V = ren-comp _ _ _
renSem-comp {κ = R[ L ]} ρ₁ ρ₂ V = ren-comp _ _ _
renSem-comp {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ (left x) = cong left (ren-comp-ne _ _ _)
renSem-comp {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ (right (fst₁ , left x)) = cong right (cong₂ _,_ (ren-comp _ _ _) (cong left (ren-comp-ne _ _ _)))
renSem-comp {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ (right (fst₁ , right y)) = cong right (cong₂ _,_ (ren-comp _ _ _) (cong right refl))
renSem-comp {κ = R[ R[ κ ] ]} ρ₁ ρ₂ (left x) = cong left (ren-comp-ne _ _ _)
renSem-comp {κ = R[ R[ κ ] ]} ρ₁ ρ₂ (right (fst₁ , snd₁)) = cong right (cong₂ _,_ (ren-comp _ _ _) (renSem-comp _ _ _))
 
