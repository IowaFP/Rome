module R2Mu.Types.Decidability where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)

open import R2Mu.Kinds.Syntax
open import R2Mu.Types.Syntax
import R2Mu.Types.Pre as Pre


open Pre.Type

-- Need to change output type to Σ[ ⊢τ ∈ Type Δ τ κ] (Value ⊢τ)
-- where Value defined on Syntax.Type...
⊢ₖ? : ∀ {Δ : KEnv} → (τ : Pre.Type) → (v : Pre.Value τ) → (κ : Kind) → Σ[ ⊢τ ∈ Type Δ τ κ ] (Value ⊢τ)
-- ⊢ₖ? .Pre.U Pre.U ★            = yes U
-- ⊢ₖ? .(tvar n) (Pre.tvar n) ★  = yes (tvar n {!!})
-- ⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) ★ = {!!}
-- ⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) ★  = {!!}
-- ⊢ₖ? .(`λ κ _) (Pre.`λ κ v) ★  = {!!}
-- ⊢ₖ? .(μ _) (Pre.μ v) ★        = {!!}
-- ⊢ₖ? .(ν _) (Pre.ν v) ★        = {!!}
-- ⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) ★    = {!!}
-- ⊢ₖ? .(lab l) (Pre.lab l) ★    = {!!}
-- ⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) ★   = {!!}
-- ⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) ★ = {!!}
-- ⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ ★  = {!!}
-- ⊢ₖ? .∅ Pre.∅ ★                = yes ∅
-- ⊢ₖ? .(Π τ) (Pre.Π {τ} v) ★ with ⊢ₖ? τ v R[ ★ ]
-- ... | yes p = yes (Π p)
-- -- N.b. I need a notion of *typed* values to prevent case distinction
-- -- on _·[_]...
-- ... | no p = no λ { (x ·[ x₁ ]) → {!!} ; (Π x) → p x ; (Σ x) → p x }

-- ⊢ₖ? .(Σ _) (Pre.Σ v) ★ = {!!}

-- ⊢ₖ? .U v@Pre.U L = {!!}
-- ⊢ₖ? .(tvar n) (Pre.tvar n) L = {!!}
-- ⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) L = {!!}
-- ⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) L = {!!}
-- ⊢ₖ? .(`λ κ _) (Pre.`λ κ v) L = {!!}
-- ⊢ₖ? .(μ _) (Pre.μ v) L = {!!}
-- ⊢ₖ? .(ν _) (Pre.ν v) L = {!!}
-- ⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) L = {!!}
-- ⊢ₖ? .(lab l) (Pre.lab l) L = {!!}
-- ⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) L = {!!}
-- ⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) L = {!!}
-- ⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ L = {!!}
-- ⊢ₖ? .∅ Pre.∅ L = {!!}
-- ⊢ₖ? .(Π _) (Pre.Π v) L = {!!}
-- ⊢ₖ? .(Σ _) (Pre.Σ v) L = {!!}
-- ⊢ₖ? .U Pre.U R[ κ ] = {!!}
-- ⊢ₖ? .(tvar n) (Pre.tvar n) R[ κ ] = {!!}
-- ⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) R[ κ ] = {!!}
-- ⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) R[ κ₁ ] = {!!}
-- ⊢ₖ? .(`λ κ _) (Pre.`λ κ v) R[ κ₁ ] = {!!}
-- ⊢ₖ? .(μ _) (Pre.μ v) R[ κ ] = {!!}
-- ⊢ₖ? .(ν _) (Pre.ν v) R[ κ ] = {!!}
-- ⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) R[ κ ] = {!!}
-- ⊢ₖ? .(lab l) (Pre.lab l) R[ κ ] = {!!}
-- ⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) R[ κ ] = {!!}
-- ⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) R[ κ ] = {!!}
-- ⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ R[ κ ] = {!!}
-- ⊢ₖ? .∅ Pre.∅ R[ κ ] = {!!}
-- ⊢ₖ? .(Π _) (Pre.Π v) R[ κ ] = {!!}
-- ⊢ₖ? .(Σ _) (Pre.Σ v) R[ κ ] = {!!}
-- ⊢ₖ? .U Pre.U (x `→ κ) = {!!}
-- ⊢ₖ? .(tvar n) (Pre.tvar n) (x `→ κ) = {!!}
-- ⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) (x `→ κ) = {!!}
-- ⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) (x `→ κ₁) = {!!}
-- ⊢ₖ? .(`λ κ _) (Pre.`λ κ v) (x `→ κ₁) = {!!}
-- ⊢ₖ? .(μ _) (Pre.μ v) (x `→ κ) = {!!}
-- ⊢ₖ? .(ν _) (Pre.ν v) (x `→ κ) = {!!}
-- ⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) (x₁ `→ κ) = {!!}
-- ⊢ₖ? .(lab l) (Pre.lab l) (x `→ κ) = {!!}
-- ⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) (x `→ κ) = {!!}
-- ⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) (x `→ κ) = {!!}
-- ⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ (x `→ κ) = {!!}
-- ⊢ₖ? .∅ Pre.∅ (x `→ κ) = {!!}
-- ⊢ₖ? .(Π _) (Pre.Π v) (x `→ κ) = {!!}
-- ⊢ₖ? .(Σ _) (Pre.Σ v) (x `→ κ) = {!!}
  
