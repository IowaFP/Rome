{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming 
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Equivalence.Properties
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
  using (↻-ren-⇑NE ; ↻-ren-⇑)

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness.Relation public

--------------------------------------------------------------------------------
-- ⇑ ∘ reify commutes over _─_

↻-⇑-reify-─ : ∀ (ρ₂ ρ₁ : RowType Δ₂ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]) → 
                   {nr   : NotRow ρ₂ or NotRow ρ₁} → 
                  ⇑ (reify ((ρ₂ ─ ρ₁) {nr})) ≡t ⇑ (reify ρ₂) ─ ⇑ (reify ρ₁)
↻-⇑-reify-─ (ne x₁) (ne x₂) {nr} = eq-refl
↻-⇑-reify-─ (ne x₁) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-─ (ne x₁) (row ρ x₂) {nr} = eq-refl
↻-⇑-reify-─ (ne x₁) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (ne x₃) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (x₃ ▹ x₄) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (row ρ x₃) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (ne x₂) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (row ρ₁ x₂) {left ()}
↻-⇑-reify-─ (row ρ x₁) (row ρ₁ x₂) {right ()}
↻-⇑-reify-─ (row ρ x₁) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (ne x₁) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (x₁ ▹ x₂) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (row ρ x₁) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (ρ₁ ─ ρ₄) {nr} = eq-refl

--------------------------------------------------------------------------------
-- syntactic mapping relates to semantic precomposition

map-over-⇑Row : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (n : ℕ) (P : Fin n → Label × SemType Δ κ₁) → 
                ⟦ f ⟧≋ F → 
                ⟦ ⇑Row (reifyRow (n , P)) ⟧r≋ (n , P) → 
                ⟦ map (overᵣ (f ·_)) (⇑Row (reifyRow (n , P))) ⟧r≋ (n , overᵣ (F id) ∘ P)
map-over-⇑Row f F zero P rel-f rel-P = tt
map-over-⇑Row f F (suc n) P rel-f rel-P = 
  (refl , 
  (subst-⟦⟧≋ (eq-· (inst (renₖ-id f)) eq-refl) (rel-f id (rel-P .fst .snd)))) , 
  (map-over-⇑Row f F n (P ∘ fsuc) rel-f (rel-P .snd))              

--------------------------------------------------------------------------------
-- Congruence over syntactic/semantic mapping

cong-<$>⟦⟧≋ : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (v : Type Δ R[ κ₁ ]) (V : SemType Δ R[ κ₁ ]) → 
                ⟦ f ⟧≋ F → 
                ⟦ v ⟧≋ V → 
                ⟦ f <$> v ⟧≋ F <$>V V 
cong-<$>⟦⟧≋ f F v (ne x₁) rel-f rel-v = eq-<$> (reify-⟦⟧≋ rel-f) rel-v
cong-<$>⟦⟧≋ f F v (l ▹ τ) rel-f (eq , rel) = 
  eq-trans 
    (eq-<$> eq-refl eq) 
  (eq-trans 
    eq-▹$ 
  (eq-▹ 
    eq-refl 
    (reify-⟦⟧≋ 
      (subst-⟦⟧≋ 
        (eq-· (inst (renₖ-id f)) eq-refl) 
        (rel-f id rel))))) , 
  refl-⟦⟧≋ (rel-f id rel)
cong-<$>⟦⟧≋ f F v (row (n , P) x₁) rel-f (eq , rel) = 
  (eq-trans 
    (eq-<$> eq-refl eq) 
  (eq-trans eq-map 
  (eq-row (reify-⟦⟧r≋ (map-over-⇑Row f F n P rel-f rel))))) , 
  refl-⟦⟧r≋ (map-over-⇑Row f F n P rel-f rel)
cong-<$>⟦⟧≋ f F v ((V₂ ─ V₁) {nr}) rel-f (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-<$> eq-refl (eq-trans eq (↻-⇑-reify-─ V₂ V₁ {nr}))) 
  (eq-trans 
    eq-<$>-─ 
  (eq-trans 
    (eq-─ 
      (reify-⟦⟧≋ (cong-<$>⟦⟧≋ f F (⇑ (reify V₂)) V₂ rel-f rel₂)) 
      ((reify-⟦⟧≋ (cong-<$>⟦⟧≋ f F (⇑ (reify V₁)) V₁ rel-f rel₁)))) 
    (eq-sym (↻-⇑-reify-─ (F <$>V V₂) (F <$>V V₁) {NotRow<$> nr}))))) , 
  (refl-⟦⟧≋ (cong-<$>⟦⟧≋ f F (⇑ (reify V₂)) V₂ rel-f rel₂)) , 
  (refl-⟦⟧≋ (cong-<$>⟦⟧≋ f F (⇑ (reify V₁)) V₁ rel-f rel₁))

--------------------------------------------------------------------------------
-- Congruence over complement

∈Row→∈L≋ : ∀ {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈Row P → l ∈L (⇑Row (reifyRow' n P))
∈Row→∈L≋ {n = n} (fzero , refl) = Here
∈Row→∈L≋ {n = n} (fsuc i , eq) = There (∈Row→∈L≋ (i , eq))

∈L→∈Row≋ : ∀ {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈L (⇑Row (reifyRow' n P)) → l ∈Row P
∈L→∈Row≋ {n = suc n} Here = fzero , refl
∈L→∈Row≋ {n = suc n} (There ev) with ∈L→∈Row≋ ev 
... | i , eq = (fsuc i) , eq

cong-compl⟦⟧≋ : ∀ {n m : ℕ} 
                {P : Fin n → Label × SemType Δ κ}
                {Q : Fin m → Label × SemType Δ κ} →
                ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P) → 
                ⟦ ⇑Row (reifyRow' m Q) ⟧r≋ (m , Q) → 
                ⟦ ⇑Row (reifyRow' n P) ─s ⇑Row (reifyRow' m Q) ⟧r≋ compl P Q
cong-compl⟦⟧≋ {n = zero} {P = P} {Q} P≋ Q≋ = tt
cong-compl⟦⟧≋ {n = suc n} {m} {P = P} {Q} P≋ Q≋ with P fzero .fst ∈Row? Q | P fzero .fst ∈L? ⇑Row (reifyRow' m Q) 
... | yes p | yes q = cong-compl⟦⟧≋ (P≋ .snd) Q≋
... | yes p | no q = ⊥-elim (q (∈Row→∈L≋ p))
... | no p | yes q = ⊥-elim (p (∈L→∈Row≋ q))
... | no p | no q = (refl , P≋ .fst .snd) , (cong-compl⟦⟧≋ (P≋ .snd) Q≋)

--------------------------------------------------------------------------------
-- Apply is sound

sound-apply : ∀ {κ₂} (v : Type Δ κ₁) (V : SemType Δ κ₁) → 
               ⟦ v ⟧≋ V → 
               SoundKripke {κ₂ = κ₂} (`λ (` Z · renₖ S v)) (apply V)
sound-apply v V rel-v r {g} {G} rel-G = 
  subst-⟦⟧≋ 
    (eq-sym eq-β)
  (subst-⟦⟧≋ 
    (eq-sym 
      (eq-· eq-refl 
      (eq-trans 
        (inst (cong (subₖ (extendₖ ` g)) (↻-liftₖ-weaken r v)))
        (inst (subₖ-weaken (renₖ r v) g))))) 
  (subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id g)) eq-refl) 
    (rel-G id (ren-⟦⟧≋ r rel-v))))

--------------------------------------------------------------------------------
-- Π and Π-Kripke are soundly related

sound-Π : ∀ {nl : True (notLabel? κ₁)} → 
        SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Π {notLabel = nl}) Π-Kripke

-- Mapping _apply_ over a row is semantic application
-- REFACTOR:
--  - restate and reprove using map-over-⇑Row; observe that subRowₖ (extendₖ ` v) (renRowₖ S ...
--    can be reduced.
map-apply : ∀ (n : ℕ) (P : Fin n → Label × KripkeFunction Δ₁ κ₁ κ₂) → 
               (φ : Renamingₖ Δ₁ Δ₂) → 
               (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
               (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → 
               (rel-v : ⟦ v ⟧≋ V) → 
             ⟦ map (overᵣ (_·_ (`λ (` Z · weakenₖ v))))
               (subRowₖ (extendₖ ` v)
                 (renRowₖ S (renRowₖ φ (⇑Row (reifyRow (n , P))))))
             ⟧r≋ (n , λ x → (P x . fst) , apply V id (renKripke φ (P x .snd)))
map-apply zero P φ rel v V rel-v = tt
map-apply (suc n) P φ (rel-fzero , rel-fsuc) v V rel-v = 
  (refl , 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
  (subst-⟦⟧≋ 
    (eq-sym eq-β) 
  (subst-⟦⟧≋ 
    (inst (subₖ-comp (renₖ (liftₖ S)
            (renₖ (liftₖ φ) (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))))) 
  (subst-⟦⟧≋ 
    (inst (↻-subₖ-renₖ (renₖ (liftₖ φ) (⇑ (reify ((P fzero .snd) S (reflect (` Z)))))))) 
  (subst-⟦⟧≋ 
    (inst (↻-subₖ-renₖ (⇑ (reify ((P fzero .snd) S (reflect (` Z))))) )) 
  (subst-⟦⟧≋ 
    (inst (subₖ-cong {σ₁ = extendₖ (` ∘ φ) v} (λ { Z → sym (subₖ-weaken v _) ; (S x) → refl })  (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))) 
  (subst-⟦⟧≋ 
    (eq-trans 
      eq-β 
    (eq-trans 
      (inst (sym (↻-subₖ-renₖ {r = liftₖ φ} {σ = extendₖ ` (renₖ id v)} (⇑ (reify ((P fzero .snd) S (reflect (` Z)))))))) 
    (inst (subₖ-cong (λ { Z → renₖ-id v ; (S x) → refl }) (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))))) 
  ((rel-fzero .snd) φ (ren-⟦⟧≋ id rel-v))))))))) , 
  (map-apply n (P ∘ fsuc) φ rel-fsuc v V rel-v)

--------------------------------------------------------------------------------
--
-- Mapping Π over a row relates to pre-composition by semantic Π 
--
-- N.b. we can't use map-over-⇑Row to define map-Π without violating termination
-- checking in sound-Π later.

map-Π : ∀ {nl : True (notLabel? κ)} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (overᵣ (_·_ (Π {notLabel = nl}))) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΠV (P i .snd))

--------------------------------------------------------------------------------
-- Soundness of Π and ΠV definition

sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {ne g} q = λ ρ {v} {V} eq → 
  subst-⟦⟧≋ 
  (eq-sym (eq-Π-assoc {ρ = renₖ ρ f} {τ = v})) 
  (subst-⟦⟧≋ 
    (eq-sym 
      (eq-trans 
        (eq-· eq-refl 
          (eq-trans 
            (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
            eq-β)) 
          eq-refl)) 
        (sound-Π ρ
           {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
           (eq-<$> 
             (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
             (eq-trans 
               (eq-trans 
                 (inst (subₖ-weaken (renₖ ρ f) v)) 
                 (renₖ-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Π {κ₁ = R[ κ ]} ρ {v} {ne x} q =
 eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-⟦⟧≋ (sound-Π id eq-refl)))) 
                eq-refl))
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (eq , rel) ρ₂ {v} {V} rel-v = 
  subst-⟦⟧≋ (eq-sym (eq-Π-assoc)) (sound-Π ρ₂ {renₖ ρ₂ f ?? v} 
  ((eq-trans 
    (eq-· 
      (eq-· 
        eq-refl 
        (renₖ-≡t ρ₂ eq)) 
      eq-refl) 
  (eq-trans 
    (eq-· eq-β eq-refl) 
  (eq-trans 
    eq-β 
  (eq-trans 
    eq-map 
  (eq-row 
    (reify-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v))))))) , 
  refl-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v)))
sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {f} {l ▹ F} (eq , sound-F) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ (eq-sym (eq-Π-assoc)) 
    (sound-Π r₂ 
      ((eq-trans 
        (eq-· (eq-· eq-refl (renₖ-≡t r₂ eq)) eq-refl) 
        (eq-trans (eq-· eq-β eq-refl) 
        (eq-trans 
          eq-β 
        (eq-trans 
          eq-▹$ 
          (eq-▹ 
            (inst (trans (subₖ-weaken (renₖ r₂ (⇑NE l)) v) (sym (↻-ren-⇑NE r₂ l)))) 
            (eq-trans 
              eq-β 
            (eq-trans 
              eq-β 
            (eq-trans 
              (inst (sym (subₖ-comp (renₖ (liftₖ S)
              (renₖ (liftₖ r₂) (⇑ (reify (F S (reflect (` Z)))))))))) 
            (eq-trans 
              (inst (sym (↻-subₖ-renₖ (renₖ (liftₖ r₂) (⇑ (reify (F S (reflect (` Z))))))))) 
            (eq-trans 
              (inst 
                (subₖ-cong {σ₂ = extendₖ ` (renₖ id v)} 
                (λ { Z → trans (subₖ-weaken v _) (sym (renₖ-id v)) ; (S x₁) → refl }) 
                (renₖ (liftₖ r₂) (⇑ (reify (F S (reflect (` Z)))))))) 
              (eq-trans 
                (eq-sym 
                  (eq-β {τ₁ = renₖ (liftₖ r₂) (⇑ (reify (F S (reflect (` Z)))))} {renₖ id v})) 
              (reify-⟦⟧≋ (sound-F r₂ (ren-⟦⟧≋ id rel-V)))))))))))))) , 
    refl-⟦⟧≋ (sound-F r₂ {_} {renSem id V} (ren-⟦⟧≋ id rel-V))))
  
sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ─ V₁) {nr}} rel r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ (eq-trans (rel .fst) (↻-⇑-reify-─ V₂ V₁ {nr}))))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc) 
  (sound-Π r₂ 
    (eq-trans 
      (eq-trans 
        (eq-· eq-β eq-refl) 
      (eq-trans 
          eq-β 
      (eq-trans 
        eq-<$>-─ 
      (eq-─ 
        (eq-trans 
          (eq-<$> eq-refl (inst (subₖ-weaken (renₖ r₂ (⇑ (reify V₂))) v))) 
          (reify-⟦⟧≋ 
            {V = apply V <$>V renSem r₂ V₂} 
            (cong-<$>⟦⟧≋ 
              (`λ (` Z · renₖ S v)) 
              (apply V) 
              (renₖ r₂ (⇑ (reify V₂))) 
              (renSem r₂ V₂) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≋ r₂ (rel .snd .fst))))) 
        ((eq-trans 
          (eq-<$> eq-refl (inst (subₖ-weaken (renₖ r₂ (⇑ (reify V₁))) v))) 
          (reify-⟦⟧≋ 
            {V = apply V <$>V renSem r₂ V₁} 
            (cong-<$>⟦⟧≋ 
              (`λ (` Z · renₖ S v)) 
              (apply V) 
              (renₖ r₂ (⇑ (reify V₁))) 
              (renSem r₂ V₁) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≋ r₂ (rel .snd .snd)))))))))) 
    (eq-sym 
      (↻-⇑-reify-─ 
        (apply V <$>V renSem r₂ V₂) (apply V <$>V renSem r₂ V₁) {NotRow<$> (nrRenSem' r₂ V₂ V₁ nr)})) , 
    (refl-⟦⟧≋ (cong-<$>⟦⟧≋ (`λ (` Z · renₖ S v)) (apply V)
                 (renₖ r₂ (⇑ (reify V₂))) (renSem r₂ V₂) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ (rel .snd .fst))) , 
    refl-⟦⟧≋ (cong-<$>⟦⟧≋ (`λ (` Z · renₖ S v)) (apply V)
                 (renₖ r₂ (⇑ (reify V₁))) (renSem r₂ V₁) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ (rel .snd .snd)))))))
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (eq , rel) =
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  (eq-trans 
    eq-map 
    (eq-row (reify-⟦⟧r≋ (map-Π n P rel))))) , 
  refl-⟦⟧r≋ (map-Π {nl = nl} n P rel)
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (eq , rel) = 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Π (eq-trans eq-▹$ (eq-▹ eq-refl (reify-⟦⟧≋ (sound-Π id rel)))))) , 
  (refl-⟦⟧≋ (sound-Π {nl = nl} id rel))
sound-Π {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ─ ρ₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  (eq-trans 
    (eq-<$> eq-refl (↻-⇑-reify-─ ρ₂ ρ₁ {nr})) 
  (eq-trans 
    eq-<$>-─ 
  (eq-trans 
    (eq-─ (eq-sym eq-Π) (eq-sym eq-Π)) 
  (eq-trans 
    (eq-─ (reify-⟦⟧≋ (sound-Π id rel₂)) (reify-⟦⟧≋ (sound-Π id rel₁))) 
  (eq-trans (eq-sym (↻-⇑-reify-─ ((λ ρ → ΠV) <$>V ρ₂) ((λ ρ → ΠV) <$>V ρ₁) {nr = NotRow<$> nr})) eq-refl))))))) , (refl-⟦⟧≋ (sound-Π {nl = nl} id rel₂)) , ((refl-⟦⟧≋ (sound-Π {nl = nl} id rel₁)))

map-Π zero P rel = tt
map-Π {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Π {nl = nl} id rel-fzero) , (map-Π n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- Soundness for Σ (identical to Π above)

-- sound-Σ : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Σ Σ-Kripke
-- map-Σ : ∀ (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
--         (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
--         ⟦ map (overᵣ (_·_ Σ)) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΣV (P i .snd))

-- sound-Σ {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
-- sound-Σ {κ₁ = L} ρ {v} {V} q = {!!} -- eq-· eq-refl (reify-⟦⟧≋ q)
-- sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {f} {ne g} q = λ ρ {v} {V} eq → 
--   subst-⟦⟧≋ 
--   (eq-sym (eq-Σ-assoc {ρ = renₖ ρ f} {τ = v})) 
--   (subst-⟦⟧≋ 
--     (eq-sym 
--       (eq-trans 
--         (eq-· eq-refl 
--           (eq-trans 
--             (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
--             eq-β)) 
--           eq-refl)) 
--         (sound-Σ ρ
--            {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
--            (eq-<$> 
--              (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
--              (eq-trans 
--                (eq-trans 
--                  (inst (subₖ-weaken (renₖ ρ f) v)) 
--                  (renₖ-≡t ρ q)) 
--                (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
-- sound-Σ {κ₁ = R[ κ ]} ρ {v} {ne x} q =
--  eq-trans 
--         (eq-· eq-refl q) 
--         (eq-trans 
--             eq-Σ 
--             (eq-<$> 
--                 (eq-trans 
--                     eq-η 
--                     (eq-λ (reify-⟦⟧≋ (sound-Σ id eq-refl)))) 
--                 eq-refl))
-- sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (eq , rel) ρ₂ {v} {V} rel-v = 
--   subst-⟦⟧≋ (eq-sym (eq-Σ-assoc)) (sound-Σ ρ₂ {renₖ ρ₂ f ?? v} 
--   ((eq-trans 
--     (eq-· 
--       (eq-· 
--         eq-refl 
--         (renₖ-≡t ρ₂ eq)) 
--       eq-refl) 
--   (eq-trans 
--     (eq-· eq-β eq-refl) 
--   (eq-trans 
--     eq-β 
--   (eq-trans 
--     eq-map 
--   (eq-row 
--     (reify-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v))))))) , refl-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v)))
-- sound-Σ {κ₁ = R[ κ ]} ρ {v} {row (n , P) _} = {!!} -- (eq , rel) = 
--   -- eq-trans 
--   --   (eq-· eq-refl eq) 
--   -- (eq-trans 
--   --   eq-Σ 
--   -- (eq-trans 
--   --   eq-map 
--   --   (eq-row (reify-⟦⟧r≋ (map-Σ n P rel))))) , 
--   -- refl-⟦⟧r≋ (map-Σ n P rel)

-- map-Σ zero P rel = tt
-- map-Σ (suc n) P = {!!} -- (rel-fzero , rel-fsuc) = (sound-Σ id rel-fzero) , (map-Σ n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- commutativity lemmas


--------------------------------------------------------------------------------
-- Fundamental lemma  

fundS : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)

--------------------------------------------------------------------------------
-- Fundamental lemma for rows

fundSRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)
fundSRow [] e = tt
fundSRow ((l , τ) ∷ xs) e = (refl , fundS τ e ) , fundSRow xs e

--------------------------------------------------------------------------------
-- mapping an application over a row is application of the semantic row.

fundS-map-app : ∀ (n : ℕ) (P : Fin n → Label × SemType Δ₂ κ₁) →  
                (τ₁ : Type Δ₁ (κ₁ `→ κ₂)) → 
                (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
                {σ : Substitutionₖ Δ₁ Δ₂} → {η : Env Δ₁ Δ₂} → 
                ⟦ σ ⟧≋e η → 
                ⟦ map (overᵣ (_·_ (subₖ σ τ₁))) (⇑Row (reifyRow' n P)) ⟧r≋ (n , (λ x → P x .fst , eval τ₁ η id (P x .snd)))


fundS-map-app zero P _ _ _ = tt
fundS-map-app (suc n) P τ₁ (rel-fzero , rel-fsuc) {σ} e =
  (refl , (subst-⟦⟧≋ (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) (fundS τ₁ e id (rel-fzero .snd)))) ,
  fundS-map-app n (P ∘ fsuc) τ₁ rel-fsuc e

--------------------------------------------------------------------------------
-- Fundamental lemma for predicates
          
fundSPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η)           
fundSPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-· (reify-⟦⟧≋ (fundS ρ₂ e)) ~ (reify-⟦⟧≋ (fundS ρ₃ e))
fundSPred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-≲ (reify-⟦⟧≋ (fundS ρ₂ e))

--------------------------------------------------------------------------------
-- Fundamental lemma definition 

fundS (` α) {σ} {η} e = e α
fundS (`λ τ) {σ} {η} e ρ {v} {V} q = 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
    (subst-⟦⟧≋ 
      (eq-trans 
        (eq-trans 
          (inst (subₖ-cong (λ { Z → refl ; (S x) → trans (renₖ-subₖ-id σ ρ (σ x)) (↻-subₖ-renₖ (σ x)) }) τ)) 
          (inst (subₖ-comp τ))) 
        (inst (↻-subₖ-renₖ (subₖ (liftsₖ σ) τ)))) 
      (fundS τ (extend-⟦⟧≋ (ren-⟦⟧≋ ρ ∘ e) q)))
fundS (τ₁ · τ₂) {σ} {η} e  = 
  subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) 
    (fundS τ₁ e id (fundS τ₂ e))
fundS (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fundS τ₁ e) (fundS τ₂ e)
fundS (`∀ τ) {σ} {η} e = eq-∀ (fundS τ {liftsₖ σ} {lifte η} (weaken-⟦⟧≋ e))
fundS (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = subₖ σ τ}) 
        (eq-λ (fundS τ e S eq-refl)))
fundS (π ⇒ τ) {σ} {η} e = eq-⇒ (fundSPred π e) (fundS τ e)
fundS (lab l) {σ} {η} e = eq-refl
fundS ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fundS τ e)
fundS (Π {notLabel = nl}) {σ} {η} e = sound-Π {nl = nl}
fundS Σ {σ} {η} e = {!!} --  sound-Σ  
fundS (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | inspect (λ x → eval x η) τ₂ | fundS τ₂ e 
... | ne x | [[ eq ]] | w =
  eq-<$> 
    (eq-trans 
      eq-η 
      (eq-λ 
        (reify-⟦⟧≋ (fundS τ₁ e S {` Z} {reflect (` Z)} (reflect-⟦⟧≋ eq-refl))))) 
    (eq-trans 
      (reify-⟦⟧≋ (fundS τ₂ e)) 
      (eq-trans (inst (cong (⇑ ∘ reify) eq)) eq-refl))
... | row (n , P) _ | [[ eq ]] | eqₜ , rel = 
    (eq-trans 
      (eq-<$> 
        eq-refl
        eqₜ) 
    (eq-trans 
      eq-map 
      (eq-row (reify-⟦⟧r≋ (fundS-map-app n P τ₁ rel e) )))) , 
    refl-⟦⟧r≋ (fundS-map-app n P τ₁ rel e)  
... | l ▹ τ | [[ eq ]] | eqₜ , rel = 
  (eq-trans 
    (eq-<$> eq-refl eqₜ) 
    (eq-trans 
      eq-▹$ 
      (eq-▹ 
        eq-refl 
        (eq-trans 
          (eq-· 
            (inst (sym (renₖ-id (subₖ σ τ₁)))) 
            eq-refl) 
          (reify-⟦⟧≋ (fundS τ₁ e id rel)))))) , 
  refl-⟦⟧≋ (fundS τ₁ e id rel)
fundS  {Δ₂ = Δ₂} ( _<$>_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {σ} {η} e | (ρ₂ ─ ρ₁) {nr} | [[ eq ]] | t-eq , rel₂ , rel₁ = 
  (eq-trans 
    (eq-<$> eq-refl t-eq) 
    (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify (ρ₂ ─ ρ₁))) (ρ₂ ─ ρ₁) (fundS τ₁ e) (eq-refl , rel₂ , rel₁) .fst)) , 
    refl-⟦⟧≋ (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify ρ₂)) ρ₂ (fundS τ₁ e) rel₂) , 
    refl-⟦⟧≋ (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify ρ₁)) ρ₁ (fundS τ₁ e) rel₁)
fundS (⦅ xs ⦆ oxs) {σ} {η} e with fundSRow xs e
fundS (⦅ [] ⦆ tt) {σ} {η} e | tt = eq-refl , tt
fundS (⦅ (l , τ) ∷ xs ⦆ oxs) {σ} {η} e | ((refl , ih-τ) , ih-xs) = eq-row (eq-cons refl (reify-⟦⟧≋ (fundS τ e)) (reify-⟦⟧r≋ ih-xs)) , ((refl , refl-⟦⟧≋ ih-τ) , refl-⟦⟧r≋ ih-xs)
fundS (ρ₂ ─ ρ₁) {σ} {η} e with eval ρ₂ η | fundS ρ₂ e 
fundS (ρ₂ ─ ρ₁) {σ} {η} e | ne x₁ | ih with eval ρ₁ η | fundS ρ₁ e 
... | ne x₂    | ih' = (eq-─ ih ih') , (eq-refl , eq-refl)
... | x₂ ▹ x₃  | ih' = (eq-─ ih (ih' .fst)) , (eq-refl , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = (eq-─ ih (eq-trans (ih' .fst) (eq-row reflᵣ))) , (eq-refl , ((eq-row reflᵣ) , (ih' .snd)))
... | c ─ c₁   | ih' = (eq-─ ih (ih' .fst)) , (eq-refl , (eq-refl , (ih' .snd .fst) , (ih' .snd .snd)))
fundS (ρ₂ ─ ρ₁) {σ} {η} e | x₁ ▹ x₂ | (eq , rel) with eval ρ₁ η | fundS ρ₁ e 
... | ne x₂    | ih' = (eq-─ eq ih') , (eq-refl , rel) , eq-refl
... | x₂ ▹ x₃  | ih' = eq-─ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
... | row ρ x₂ | ih' = eq-─ eq (eq-trans (ih' .fst) (eq-row reflᵣ)) , (eq-refl , rel) , (eq-row reflᵣ , (ih' .snd))
... | c ─ c₁   | ih' = eq-─ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
fundS (ρ₂ ─ ρ₁) {σ} {η} e | row (n , P) oP | ih with eval ρ₁ η | fundS ρ₁ e 
... | ne x₂    | ih' = eq-─ (eq-trans (ih .fst) (eq-row reflᵣ)) ih' , ((eq-row reflᵣ , (ih .snd)) , eq-refl)
... | x₂ ▹ x₃  | ih' = eq-─ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , (ih' .snd)))
... | row (m , Q) oQ | ih' = 
  eq-trans 
    (eq-─ (ih .fst) (ih' .fst)) 
    (eq-trans 
      (eq-compl {ozs = fromWitness (ordered-─s {xs = ⇑Row (reifyRow (n , P))}
                {ys = ⇑Row (reifyRow (m , Q))} (Ordered⇑ (reifyRow' n P) (reifyRowOrdered (n , P) oP)))}) 
      (eq-row (reify-⟦⟧r≋ (cong-compl⟦⟧≋ (ih .snd) (ih' .snd))))) , 
  refl-⟦⟧r≋ (cong-compl⟦⟧≋ (ih .snd) (ih' .snd))
... | c ─ c₁   | ih' = eq-─ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
fundS (ρ₂ ─ ρ₁) {σ} {η} e | c ─ c₁ | ih with eval ρ₁ η | fundS ρ₁ e 
... | ne x₂    | ih' = eq-─ (ih .fst) ih' , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , eq-refl)
... | x₂ ▹ x₃  | ih' = eq-─ (ih .fst) (ih' .fst) , ((eq-refl , (ih .snd)) , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = eq-trans (eq-─ (ih .fst) (ih' .fst)) (eq-─ eq-refl (eq-row reflᵣ)) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-row reflᵣ , (ih' .snd)))
... | c ─ c₁   | ih' = eq-─ (ih .fst) (ih' .fst) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
fundS (l ▹ τ) {σ} {η} e with eval l η | fundS l e
... | ne x₁ | ih = (eq-▹ ih (reify-⟦⟧≋ (fundS τ e))) , refl-⟦⟧≋ (fundS τ e)
... | lab l' | ih = eq-trans (eq-▹ eq-refl (reify-⟦⟧≋ (fundS τ e))) (eq-labTy ih) , 
                    (refl , (refl-⟦⟧≋ (fundS τ e))) , 
                    tt

--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity

⊢⟦_⟧≋ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≋ eval τ idEnv
⊢⟦ τ ⟧≋ = subst-⟦⟧≋ (inst (subₖ-id τ)) (fundS τ idSR)

--------------------------------------------------------------------------------
-- Soundness claim  


soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
soundness τ = reify-⟦⟧≋ (⊢⟦ τ ⟧≋)
  
 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (soundness τ₂) 

