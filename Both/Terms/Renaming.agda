-- {-# OPTIONS --safe #-}
-- {-# OPTIONS --safe #-}

module Rome.Both.Terms.Renaming where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.SynAna
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Properties.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Properties.Renaming
open import Rome.Both.Types.Normal.Properties.Substitution

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Types.Equivalence.Relation
open import Rome.Both.Types.Equivalence.Properties

open import Rome.Both.Types.Renaming

open import Rome.Both.Terms.Syntax

open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Containment

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : Env Δ ιΓ
    Φ Φ₁ Φ₂ Φ₃ : PEnv Δ ιΦ
    r : Renamingₖ Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- Renamings are functions from term variables to term variables
-- and from evidence variables to evidence variables

Renaming : ∀ {ιΓ₁} {ιΓ₂} {Δ₁ : KEnv ιΔ₁} {Δ₂ : KEnv ιΔ₂} 
             (Γ₁ : Env Δ₁ ιΓ₁) (Γ₂ : Env Δ₂ ιΓ₂) → 
             Renamingₖ Δ₁ Δ₂ → Set
Renaming Γ₁ Γ₂ r = 
  (∀ {ι}{τ : NormalType _ (★ {ι})} → Var Γ₁ τ → Var Γ₂ (renₖNF r τ))

PredRenaming : ∀ {Δ₁ : KEnv ιΔ₁} {Δ₂ : KEnv ιΔ₂}
                 (Φ₁ : PEnv Δ₁ ιΦ₁) (Φ₂ : PEnv Δ₂ ιΦ₂) → 
                 Renamingₖ Δ₁ Δ₂ → Set 
PredRenaming Φ₁ Φ₂ r = (∀ {ικ} {κ : Kind ικ} {π : NormalPred _ R[ κ ]} → PVar Φ₁ π → PVar Φ₂ (renPredₖNF r π))

-- renType : ∀ {r : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ r → NormalType Δ₁ κ → NormalType Δ₂ κ
-- renType {r = r} R = renₖNF r

-- renPred : ∀ {r : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ r → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
-- renPred {r = r} R = renPredₖNF r

-- --------------------------------------------------------------------------------
-- -- Lifting of renamings

stupid : ∀ {τ : NormalType Δ₁ (★ {ι})} → Renaming (Γ₁ , τ) ∅ r → Renaming Γ₂ ∅ r 
stupid R Z = {!!} 
stupid R (S {Γ = Γ , τ'} v) = {!!}

lift : Renaming Γ₁ Γ₂ r → {τ : NormalType Δ₁ (★ {ι})} → Renaming (Γ₁ , τ) (Γ₂ , renₖNF r τ) r
lift {r = r} ρ Z = Z
lift {r = r} ρ (S v) = S (ρ v)

liftP : PredRenaming Φ₁ Φ₂ r → {π : NormalPred Δ R[ κ ]} → PredRenaming (Φ₁ , π) (Φ₂ , renPredₖNF r π) r
liftP {r = r} ρ Z = Z
liftP {r = r} ρ (S v) = S (ρ v)

liftTVar : Renaming Γ₁ Γ₂ r → {κ : Kind ικ} → Renaming (weakΓ {κ = κ} Γ₁) (weakΓ Γ₂) (liftₖ r)
liftTVar {Γ₁ = Γ₁ , x} {Γ₂ = ∅} {r = r} R v = {!!}
liftTVar {Γ₁ = Γ₁ , x} {Γ₂ = Γ₂ , x₁} {r = r} R v = {!!}


-- --------------------------------------------------------------------------------
-- -- Renaming terms

ren : ∀ (ρ : Renaming Γ₁ Γ₂ r)
        (P : PredRenaming Φ₁ Φ₂ r) → 
      NormalTerm Δ₁ Φ₁ Γ₁ τ →
      NormalTerm Δ₂ Φ₂ Γ₂ (renₖNF r τ)

renEnt : ∀ {π : NormalPred Δ₁ R[ κ ]} (ρ : PredRenaming Φ₁ Φ₂ r) → 
      NormalEnt Δ₁ Φ₁ π →
      NormalEnt Δ₂ Φ₂ (renPredₖNF r π)
renRecord : ∀ {xs : SimpleRow (NormalType Δ (★ {ι}))}
            (ρ : Renaming Γ₁ Γ₂ r) → 
            Record Γ₁ xs →
            Record Γ₂ (renRowₖNF r xs)

-- --------------------------------------------------------------------------------
-- -- Useful lemma for commuting renaming over the lift entailment rules

-- ↻-ren-⇓-<$> : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → 
--           (F : NormalType Δ₁ (κ₁ `→ κ₂))
--           (ρ₁ : NormalType Δ₁ R[ κ₁ ]) → 
--           ⇓ (⇑ (renₖNF ρ F) <$> ⇑ (renₖNF ρ ρ₁)) ≡  renₖNF ρ (⇓ (⇑ F <$> ⇑ ρ₁))
-- ↻-ren-⇓-<$> {Δ₁ = Δ₁} ρ F ρ₁ rewrite 
--     (↻-ren-⇑ ρ ρ₁) 
--   | (↻-ren-⇑ ρ F) = 
--       (trans 
--         (reify-≋ 
--           (trans-≋ (↻-renₖ-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋) 
--           (trans-≋ 
--             (idext (sym-≋ ∘ ↻-ren-reflect ρ ∘ `) (⇑ F <$> ⇑ ρ₁)) 
--             (sym-≋ (↻-renSem-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋))))) 
--         (sym (↻-ren-reify {Δ₁ = Δ₁} ρ 
--           {V₁ = (↑ F <$>V ↑ ρ₁)} 
--           {V₂ = (↑ F <$>V ↑ ρ₁)} 
--           (fundC 
--             {τ₁ = ⇑ F <$> ⇑ ρ₁} 
--             {τ₂ = ⇑ F <$> ⇑ ρ₁} 
--             idEnv-≋ 
--             (eq-<$> 
--               eq-refl 
--               eq-refl)))))   

-- --------------------------------------------------------------------------------
-- -- Renaming definitions

ren R P (` x) = ` (R x)
ren R P (`λ M) = `λ (ren (lift R) P M)
ren R P (M · N) = ren R P M · ren R P N
ren R P (Λ M) = Λ (ren {!R!} {!!} M)
ren {r = r} R P (_·[_] {τ₂ = τ₂} M τ) =
  conv 
    (sym (↻-renₖNF-β r τ₂ τ)) 
    ((ren R P M) ·[ renₖNF r τ ])
ren R P (`ƛ M) = `ƛ (ren R (liftP P) M)
ren {r = r} R P (M ·⟨ e ⟩) = ren R P M ·⟨ renEnt P e ⟩
ren {r = r} R P (# ℓ) = # (renₖNF r ℓ)
ren R P (M Π▹ne N) = (ren R P M) Π▹ne (ren R P N)
ren R P (M Π▹ N) = (ren R P M) Π▹ (ren R P N)
ren R P (M Π/ne N) = (ren R P M) Π/ne (ren R P N)
ren R P (M Π/ N) = (ren R P M) Π/ (ren R P N)
ren R P (prj M e) = prj (ren R P M) (renEnt P e)
ren R P ((M ⊹ N) e) = ((ren R P M) ⊹ (ren R P N)) (renEnt P e)
ren R P (syn ρ₁ φ M) = {!!}
ren R P (ana ρ₁ φ τ eq₁ eq₂ M) = {!!}
ren R P (M Σ▹ne M₁) = {!!}
ren R P (M Σ▹ M₁) = {!!}
ren R P (M Σ/ne M₁) = {!!}
ren R P (M Σ/ M₁) = {!!}
ren R P (inj M x) = {!!}
ren R P ((M ▿ M₁) x) = {!!}
ren R P ⟨ x ⟩ = {!!}
ren R P (⟨ l ▹ M ⟩via x) = {!!}
-- ren R (`λ M) = `λ (ren (lift R) M)
-- ren R (M · N) = (ren R M) · (ren R N)
-- ren R (Λ M) = Λ (ren (liftTVar R) M)
-- ren {ρ = ρ} R (_·[_] {τ₂ = τ₂} M τ) = 
--   conv 
--     (sym (↻-renₖNF-β ρ τ₂ τ)) 
--     ((ren R M) ·[ renₖNF ρ τ ])
-- ren R (# l) = # (renType R l)
-- ren R (l Π▹ M) = (ren R l) Π▹ (ren R M)
-- ren R (l Π▹ne M) = (ren R l) Π▹ne (ren R M)
-- ren R (M Π/ l) = ren R M Π/ ren R l
-- ren R (M Π/ne l) = ren R M Π/ne ren R l
-- ren R (l Σ▹ne M) = (ren R l) Σ▹ne (ren R M)
-- ren R (l Σ▹ M) = (ren R l) Σ▹ (ren R M)
-- ren R (M Σ/ne l) = ren R M Σ/ne ren R l
-- ren R (M Σ/ l) = ren R M Σ/ ren R l
-- ren R (`ƛ τ) = `ƛ (ren (liftPVar R) τ)
-- ren R (τ ·⟨ e ⟩) = ren R τ ·⟨ renEnt R e ⟩
-- ren {ρ = ρ} R (prj m e) = prj (ren R m) (renEnt R e)
-- ren {ρ = ρ} R (inj m e) = inj (ren R m) (renEnt R e)
-- ren {ρ = ρ} R ((M ⊹ N) e) = ((ren R M) ⊹ (ren R N)) (renEnt R e)
-- ren {ρ = ρ} R ((M ▿ N) e) = ((ren R M) ▿ (ren R N)) (renEnt R e)
-- ren {ρ = r} R (syn ρ φ M) =
--   conv (cong Π (↻-ren-⇓-<$> r φ ρ)) 
--     (syn (renₖNF r ρ) (renₖNF r φ) 
--   (conv (cong ⇓ (sym (SynT-cong (↻-ren-⇑ r ρ) (↻-ren-⇑ r φ))))
--   (conv-≡t (inst (↻-ren-syn r (⇑ ρ) (⇑ φ)) ) (conv (↻-ren-⇓ r (SynT (⇑ ρ) (⇑ φ))) (ren R M)))))
-- ren {ρ = r} R (ana ρ φ τ refl refl M) = 
--   conv 
--     (cong₂ _`→_ (cong Σ (↻-ren-⇓-<$> r φ ρ)) refl) 
--   (ana (renₖNF r ρ) (renₖNF r φ) (renₖNF r τ) refl refl
--     (conv 
--       ((cong ⇓ (sym (AnaT-cong (↻-ren-⇑ r ρ) (↻-ren-⇑ r φ) (↻-ren-⇑ r τ)))))
--     (conv (cong ⇓ (↻-ren-ana r (⇑ ρ) (⇑ φ) (⇑ τ))) 
--     (conv (↻-ren-⇓ r (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) (ren R M)))))
-- ren R ⟨ xs ⟩ = ⟨ renRecord R xs ⟩
-- ren {ρ = r} R (⟨ l ▹ M ⟩via i) = ⟨ l ▹ (ren R M) ⟩via ∈-renₖNF r i 

-- renRecord {ρ = r} R ∅ = ∅
-- renRecord {ρ = r} R (_▹_⨾_ l M xs) = _▹_⨾_ l (ren R M) (renRecord R xs)

-- renEnt {ρ = ρ} {π} (r , p) (n-var x) = n-var (p x)
-- renEnt {ρ = φ} {π} R (n-incl {xs = xs} {ys} i) = n-incl (⊆-cong _ _ (renRowₖNF-isMap φ) i )
-- renEnt {ρ = φ} {π} R (n-plus {xs = xs} {ys} {zs} i₁ i₂ i₃) = 
--   n-plus 
--     (⊆-cong _ _ (renRowₖNF-isMap φ) i₁) 
--     (⊆-cong _ _ (renRowₖNF-isMap φ) i₂)
--     (⊆-cong-or _ _ (renRowₖNF-isMap φ) i₃)
-- renEnt R n-refl = n-refl
-- renEnt R (_n-⨾_ e₁ e₂) = _n-⨾_ (renEnt R e₁) (renEnt R e₂)
-- renEnt R (n-plusL≲ e) = n-plusL≲ (renEnt R e)
-- renEnt R (n-plusR≲ e) = n-plusR≲ (renEnt R e)
-- renEnt R n-emptyR = n-emptyR
-- renEnt R n-emptyL = n-emptyL
-- renEnt {Γ₂ = Γ₂} {ρ = ρ} R (n-map≲ {ρ₁ = ρ₁} {ρ₂} {F} e eq-ρ₁ eq-ρ₂) 
--   rewrite 
--     eq-ρ₁ 
--   | eq-ρ₂
--   = n-map≲ 
--     {F = renₖNF ρ F} 
--     (renEnt R e) 
--     (sym (↻-ren-⇓-<$> ρ F ρ₁))
--     (sym (↻-ren-⇓-<$> ρ F ρ₂))
-- renEnt {ρ = ρ} R (n-map· {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} e eq-ρ₁ eq-ρ₂ eq-ρ₃)
--   rewrite 
--     eq-ρ₁ 
--   | eq-ρ₂
--   | eq-ρ₃
--   = n-map· 
--     {F = renₖNF ρ F} 
--     (renEnt R e) 
--     (sym (↻-ren-⇓-<$> ρ F ρ₁))
--     (sym (↻-ren-⇓-<$> ρ F ρ₂)) 
--     (sym (↻-ren-⇓-<$> ρ F ρ₃)) 
-- renEnt {ρ = ρ} R (n-complR-inert {ρ₂ = ρ₂} {ρ₁} {nsr} e) = n-complR-inert (renEnt R e)
-- renEnt {ρ = r} R (n-complR {xs = xs} {ys} {ozs = ozs} e) = 
--   let pf = (trans 
--           (cong ⇓Row (cong₂ _─s_ (↻-ren-⇑Row r ys) (↻-ren-⇑Row r xs))) 
--         (trans 
--           (cong ⇓Row (sym (↻-renRowₖ-─s r {ρ₂ = ⇑Row ys} {⇑Row xs}))) 
--           (sym (↻-ren-⇓Row r (⇑Row ys ─s ⇑Row xs)) ))) in
--   convEnt 
--     (cong₃ _·_~_ 
--       refl 
--       (cong-⦅⦆ 
--         {wf₁ = 
--           subst (λ x → True (normalOrdered? x)) 
--             (sym pf) 
--             (fromWitness (orderedRenRowₖNF r _ (toWitness ozs)))}
--         pf) 
--       refl) 
--     (n-complR (renEnt R e))
-- renEnt {ρ = ρ} R (n-complL-inert {ρ₂ = ρ₂} {ρ₁} {nsr} e) = n-complL-inert (renEnt R e)
-- renEnt {ρ = r} R (n-complL {xs = xs} {ys} {ozs = ozs} e) = 
--   let pf = (trans 
--           (cong ⇓Row (cong₂ _─s_ (↻-ren-⇑Row r ys) (↻-ren-⇑Row r xs))) 
--         (trans 
--           (cong ⇓Row (sym (↻-renRowₖ-─s r {ρ₂ = ⇑Row ys} {⇑Row xs}))) 
--           (sym (↻-ren-⇓Row r (⇑Row ys ─s ⇑Row xs)) ))) in
--   convEnt 
--     (cong₃ _·_~_ 
--        (cong-⦅⦆ 
--         {wf₁ = 
--           subst (λ x → True (normalOrdered? x)) 
--             (sym pf) 
--             (fromWitness (orderedRenRowₖNF r _ (toWitness ozs)))}
--         pf) 
--       refl
--       refl) 
--     (n-complL (renEnt R e))  

-- --------------------------------------------------------------------------------
-- -- Weakening is a special case of renaming (but we must convert types)

-- weakenTermByType : NormalTerm Γ τ₁ → NormalTerm (Γ , τ₂) τ₁
-- weakenTermByType {τ₁ = τ₁} M = conv (renₖNF-id τ₁) (ren ((convVar (sym (renₖNF-id _))) ∘ S , convPVar (sym (renₖNF-id-pred _)) ∘ T) M)

-- weakenTermByKind : ∀ {τ : NormalType Δ (★ {ι})} → NormalTerm Γ τ → NormalTerm (Γ ,, κ) (weakenₖNF τ)
-- weakenTermByKind = ren (K , K)

-- weakenTermByPred : ∀ {τ : NormalType Δ (★ {ι})} {π : NormalPred Δ R[ κ ]} → NormalTerm Γ τ → NormalTerm (Γ ,,, π) τ
-- weakenTermByPred {Γ = Γ} {τ = τ} {π} M = conv (renₖNF-id τ) (ren ((convVar (sym (renₖNF-id _))) ∘ P , convPVar (sym (renₖNF-id-pred _)) ∘ S) M)

-- --------------------------------------------------------------------------------
-- -- Weakening of an entailment

-- weakenEntByType : ∀ {π : NormalPred Δ R[ κ ]} → NormalEnt Γ π → NormalEnt (Γ , τ) π 
-- weakenEntByType {π = π} M = convEnt (renₖNF-id-pred π) (renEnt (convVar (sym (renₖNF-id _)) ∘ S , convPVar (sym (renₖNF-id-pred _)) ∘ T) M)

-- weakenEntByKind : ∀ {π : NormalPred Δ R[ κ₁ ]} → NormalEnt Γ π → NormalEnt (Γ ,, κ₂) (weakenPredₖNF π)
-- weakenEntByKind = renEnt (K , K)

-- weakenEntByPred : ∀ {π₁ : NormalPred Δ R[ κ₁ ]} {π₂ : NormalPred Δ R[ κ₂ ]} → NormalEnt Γ π₁ → NormalEnt (Γ ,,, π₂) π₁
-- weakenEntByPred M = convEnt (renₖNF-id-pred _) (renEnt (convVar (sym (renₖNF-id _)) ∘ P , convPVar (sym (renₖNF-id-pred _)) ∘ S) M)
