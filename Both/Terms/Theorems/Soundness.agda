module Rome.Both.Terms.Theorems.Consistency where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.SynAna
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Substitution
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Terms.Normal.Syntax
open import Rome.Both.Terms.Syntax

open import Rome.Both.Containment

--------------------------------------------------------------------------------
-- We must recursively embed contexts

⇑Ctx : NormalContext Δ → Context Δ
⇑Ctx ∅ = ∅
⇑Ctx (Γ , τ) = ⇑Ctx Γ , ⇑ τ
⇑Ctx (Γ ,, κ) = ⇑Ctx Γ ,, κ
⇑Ctx (Γ ,,, π) = ⇑Ctx Γ ,,, ⇑Pred π

--------------------------------------------------------------------------------
-- Consistency of typing: Given a well-typed NormalTerm, we can produce a well-typed Term...
-- or: if Γ ⊢nf M : τ then Γ ⊢ M : ⇑ τ.


⇑Var : ∀ {Γ} {τ : NormalType Δ ★} → NormalVar Γ τ → Var (⇑Ctx Γ) (⇑ τ)
⇑Var Z = Z
⇑Var (S v) = S (⇑Var v)
⇑Var (K {τ = τ} v) = convVar' (sym (↻-ren-⇑ S τ) ) (K (⇑Var v))
⇑Var (P v) = P (⇑Var v)

⇑PVar : ∀ {Γ} {π : NormalPred Δ R[ κ ]} → NormalPVar Γ π → PVar (⇑Ctx Γ) (⇑Pred π)
⇑PVar Z = Z
⇑PVar (S v) = S (⇑PVar v)
⇑PVar (T v) = T (⇑PVar v)
⇑PVar (K v) = convPVar' (sym (↻-ren-⇑Pred S _)) (K (⇑PVar v))

-- ⇑Row-isBimapMap : ∀ (xs : SimpleRow NormalType Δ₁ R[ κ ]) → ⇑Row xs ≡ map (bimap ⇑  ⇑) xs
-- ⇑Row-isBimapMap [] = refl
-- ⇑Row-isBimapMap (x ∷ xs) rewrite ⇑Row-isBimapMap xs = refl

⇑Ent : ∀ {Γ} {π : NormalPred Δ R[ κ ]} → NormalEnt Γ π → Ent (⇑Ctx Γ) (⇑Pred π)
⇑Ent (n-var x) = n-var (⇑PVar x)
⇑Ent (n-incl i) = n-incl (⊆-cong (λ (x , τ) → (x , ⇑ τ)) _ ⇑Row-isMap i) 
⇑Ent (n-plus i₁ i₂ i₃) = n-plus (⊆-cong _ _ ⇑Row-isMap i₁)
                                (⊆-cong _ _ ⇑Row-isMap i₂)
                                (⊆-cong-or _ _ ⇑Row-isMap i₃)

⇑Ent n-refl = n-refl
⇑Ent (_n-⨾_ e e₁) = _n-⨾_ (⇑Ent e) (⇑Ent e₁)
⇑Ent (n-plusL≲ e) = n-plusL≲ (⇑Ent e)
⇑Ent (n-plusR≲ e) = n-plusR≲ (⇑Ent e)
⇑Ent n-emptyR = n-emptyR
⇑Ent n-emptyL = n-emptyL
⇑Ent (n-map≲ {ρ₁ = ρ₁} {ρ₂} {F = F} e refl refl) = {!!}
  -- convEnt'
  --    (cong₂ _≲_
  --      (cong ⇑ (sym (stability-<$> F ρ₁)))
  --      (cong ⇑ (sym (stability-<$> F ρ₂))))
  -- (convert ((consistency (⇑ F <$> ⇑ ρ₁)) eq-≲ (consistency (⇑ F <$> ⇑ ρ₂))) (n-map≲ (⇑Ent e)))
⇑Ent (n-map· {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} e refl refl refl) = {!!}
  -- convEnt'
  --   (cong₃ _·_~_
  --     (cong ⇑ (sym (stability-<$> F ρ₁)))
  --     (cong ⇑ (sym (stability-<$> F ρ₂)))
  --     (cong ⇑ (sym (stability-<$> F ρ₃))))
  -- (convert
  --   ((consistency (⇑ F <$> ⇑ ρ₁)) eq-· (consistency (⇑ F <$> ⇑ ρ₂)) ~ (consistency (⇑ F <$> ⇑ ρ₃)))
  --   (n-map· (⇑Ent e)))
⇑Ent (n-complR-inert n) = n-complR (⇑Ent n)
⇑Ent (n-complR {xs = xs} {ys} n) = convert (eq-refl eq-· {! !} ~ eq-refl) (n-complR (⇑Ent n))
⇑Ent (n-complL-inert n) = n-complL (⇑Ent n)
⇑Ent (n-complL n) = {!!}

⇑Term : ∀ {Γ} {τ : NormalType Δ ★} → NormalTerm Γ τ → Term (⇑Ctx Γ) (⇑ τ)
⇑Term (` x) = ` (⇑Var x)
⇑Term (`λ M) = `λ (⇑Term M)
⇑Term (M · N) = ⇑Term M · ⇑Term N
⇑Term (Λ M) = Λ (⇑Term M)
⇑Term (_·[_] {τ₂ = τ₂} M τ) = (convert (eq-sym (↻-β-⇑ τ₂ τ)) ((⇑Term M) ·[ (⇑ τ) ]))
⇑Term (In F M) = In (⇑ F) (convert (embed-≡t (stability-·' F (μ F))) (⇑Term M))
⇑Term (Out F M) = convert (eq-sym (embed-≡t (stability-·' F (μ F)))) (Out (⇑ F) (⇑Term M))
⇑Term (`ƛ M) = `ƛ (⇑Term M)
⇑Term (M ·⟨ e ⟩) = (⇑Term M) ·⟨ ⇑Ent e  ⟩
⇑Term (# l) = # (⇑ l)
⇑Term (l Π▹ M) = convert (eq-· eq-refl (eq-labTy eq-refl)) (⇑Term l Π▹ ⇑Term M) 
⇑Term (M Π/ l) = (convert (eq-· eq-refl (eq-sym (eq-labTy eq-refl))) (⇑Term M)) Π/ (⇑Term l)
⇑Term (prj M n) = prj (⇑Term M) (⇑Ent n)
⇑Term ((M ⊹ N) n) = ((⇑Term M) ⊹ (⇑Term N)) (⇑Ent n)
⇑Term (l Σ▹ M) = {!!} -- convert (eq-· eq-refl eq-refl) (⇑Term l Σ▹ ⇑Term M)
⇑Term (M Σ/ l) = {!!} -- (convert (eq-· eq-refl (eq-sym eq-refl)) (⇑Term M)) Σ/ (⇑Term l)
⇑Term (inj M n) = inj (⇑Term M) (⇑Ent n)
⇑Term ((M ▿ N) n) = ((⇑Term M) ▿ (⇑Term N)) (⇑Ent n)
⇑Term (fix M) = fix (⇑Term M)
⇑Term (syn ρ φ M) =
  convert
    (eq-·
      eq-refl
      (eq-trans
        (consistency  (⇑ φ <$> ⇑ ρ))
        eq-refl))
  (syn (⇑ ρ) (⇑ φ) (convert (eq-sym (consistency (SynT (⇑ ρ) (⇑ φ)))) (⇑Term M)))
⇑Term (τ Π▹ne τ₁) = {!!}
⇑Term (τ Π/ne τ₁) = {!!}
⇑Term (ana ρ φ τ eq₁ eq₂ τ₁) = {!!}
⇑Term (τ Σ▹ne τ₁) = {!!}
⇑Term (τ Σ/ne τ₁) = {!!}
⇑Term ⟨ x ⟩ = {!!}
⇑Term (⟨ l ▹ τ ⟩via x) = {!!}
-- ⇑Term (ana ρ φ τ M) =
--   convert
--     (eq-→
--       (eq-·
--         eq-refl
--         (eq-trans (consistency (⇑ φ <$> ⇑ ρ)) eq-refl))
--       eq-refl)
--   (ana (⇑ ρ) (⇑ φ) (⇑ τ)
--     (convert (eq-sym (consistency (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) (⇑Term M)))
