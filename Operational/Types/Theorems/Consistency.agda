{-# OPTIONS --safe #-}
module Rome.Operational.Types.Theorems.Consistency where

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

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Consistency.Relation public

--------------------------------------------------------------------------------
-- ⇑ ∘ reify commutes over _─_

↻-⇑-reify-─ : ∀ (ρ₂ ρ₁ : RowType Δ₂ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]) → 
                   {nr   : NotRow ρ₂ or NotRow ρ₁} → 
                  ⇑ (reify ((ρ₂ ─ ρ₁) {nr})) ≡t ⇑ (reify ρ₂) ─ ⇑ (reify ρ₁)
↻-⇑-reify-─ (φ <$> n) (φ' <$> n') {nr} = eq-refl
↻-⇑-reify-─ (φ <$> n) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-─ (φ <$> n) (row ρ x₂) {nr} = eq-refl
↻-⇑-reify-─ (φ <$> n) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (φ <$> n) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (x₃ ▹ x₄) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (row ρ x₃) {nr} = eq-refl
↻-⇑-reify-─ (x₁ ▹ x₂) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (φ <$> n) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-─ (row ρ x₁) (row ρ₁ x₂) {left ()}
↻-⇑-reify-─ (row ρ x₁) (row ρ₁ x₂) {right ()}
↻-⇑-reify-─ (row ρ x₁) (ρ₁ ─ ρ₂) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (φ <$> n) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (x₁ ▹ x₂) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (row ρ x₁) {nr} = eq-refl
↻-⇑-reify-─ (ρ₂ ─ ρ₃) (ρ₁ ─ ρ₄) {nr} = eq-refl

--------------------------------------------------------------------------------
-- syntactic mapping relates to semantic precomposition

map-over-⇑Row : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (n : ℕ) (P : Fin n → Label × SemType Δ κ₁) → 
                ⟦ f ⟧≋ F → 
                ⟦ ⇑Row (reifyRow (n , P)) ⟧r≋ (n , P) → 
                ⟦ map (map₂ (f ·_)) (⇑Row (reifyRow (n , P))) ⟧r≋ (n , map₂ (F id) ∘ P)
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
cong-<$>⟦⟧≋ f F v (φ <$> n) rel-f (g , g-eq , g-sound) = 
  (`λ (weakenₖ f · (weakenₖ g · (` Z)))) , 
  (eq-trans (eq-<$> eq-refl g-eq) eq-map-∘) , 
  (λ r vee → 
    subst-⟦⟧≋ 
      (eq-trans 
        (eq-· 
          (inst (subₖ-weaken-over-lift r f _)) 
          (eq-· 
            (inst (subₖ-weaken-over-lift r g _)) 
            eq-refl)) (eq-sym eq-β)) 
      (rel-f r (g-sound r vee)))
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
sound-Σ : ∀ {nl : True (notLabel? κ₁)} → 
        SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Σ {notLabel = nl}) Σ-Kripke

-- Mapping _apply_ over a row is semantic application
map-apply : ∀ (n : ℕ) (P : Fin n → Label × KripkeFunction Δ₁ κ₁ κ₂) → 
               (φ : Renamingₖ Δ₁ Δ₂) → 
               (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
               (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → 
               (rel-v : ⟦ v ⟧≋ V) → 
             ⟦ map (map₂ (_·_ (`λ (` Z · weakenₖ v))))
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
        ⟦ map (map₂ (_·_ (Π {notLabel = nl}))) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΠV (P i .snd))

map-Σ : ∀ {nl : True (notLabel? κ)} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (map₂ (_·_ (Σ {notLabel = nl}))) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΣV (P i .snd))

--------------------------------------------------------------------------------
-- Consistency of Π and ΠV definition

sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {v} {φ <$> n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc)
    (sound-Π id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-<$> 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₖ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₖ-≡t S (inst (subₖ-weaken (renₖ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₖ-weaken (renₖ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₖ-weaken (renₖ r (⇑NE n)) v')) 
        (eq-sym (inst (↻-ren-⇑NE r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : SoundKripkeNE 
              (`λ (renₖ S (renₖ r f) · ` Z · renₖ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≋ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₖ-id _) (renₖ-comp r r₁  f))) 
                  (inst (renₖ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₖ-weaken-over-lift r₁ (renₖ r f) _)) eq-refl) 
                (inst (subₖ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≋ r₁ rel-v))     
sound-Π {κ₁ = R[ κ ]} ρ {v} {φ <$> n} (f , eq , sound-f) = 
  (`λ (weakenₖ Π · (weakenₖ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Π (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≋ 
      (eq-sym eq-β) 
      (sound-Π id 
        (subst-⟦⟧≋ 
          (eq-· 
            (inst (subₖ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
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
-- Consistency of Σ and ΣV definition (identical to Π def'n above)

sound-Σ {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Σ {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {v} {φ <$> n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Σ-assoc)
    (sound-Σ id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-<$> 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₖ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₖ-≡t S (inst (subₖ-weaken (renₖ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₖ-weaken (renₖ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₖ-weaken (renₖ r (⇑NE n)) v')) 
        (eq-sym (inst (↻-ren-⇑NE r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : SoundKripkeNE 
              (`λ (renₖ S (renₖ r f) · ` Z · renₖ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≋ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₖ-id _) (renₖ-comp r r₁  f))) 
                  (inst (renₖ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₖ-weaken-over-lift r₁ (renₖ r f) _)) eq-refl) 
                (inst (subₖ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≋ r₁ rel-v))     
sound-Σ {κ₁ = R[ κ ]} ρ {v} {φ <$> n} (f , eq , sound-f) = 
  (`λ (weakenₖ Σ · (weakenₖ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Σ (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≋ 
      (eq-sym eq-β) 
      (sound-Σ id 
        (subst-⟦⟧≋ 
          (eq-· 
            (inst (subₖ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (eq , rel) ρ₂ {v} {V} rel-v = 
  subst-⟦⟧≋ (eq-sym (eq-Σ-assoc)) (sound-Σ ρ₂ {renₖ ρ₂ f ?? v} 
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
sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {f} {l ▹ F} (eq , sound-F) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ (eq-sym (eq-Σ-assoc)) 
    (sound-Σ r₂ 
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
  
sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ─ V₁) {nr}} rel r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ (eq-trans (rel .fst) (↻-⇑-reify-─ V₂ V₁ {nr}))))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Σ-assoc) 
  (sound-Σ r₂ 
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
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (eq , rel) =
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  (eq-trans 
    eq-map 
    (eq-row (reify-⟦⟧r≋ (map-Σ n P rel))))) , 
  refl-⟦⟧r≋ (map-Σ {nl = nl} n P rel)
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (eq , rel) = 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Σ (eq-trans eq-▹$ (eq-▹ eq-refl (reify-⟦⟧≋ (sound-Σ id rel)))))) , 
  (refl-⟦⟧≋ (sound-Σ {nl = nl} id rel))
sound-Σ {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ─ ρ₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  (eq-trans 
    (eq-<$> eq-refl (↻-⇑-reify-─ ρ₂ ρ₁ {nr})) 
  (eq-trans 
    eq-<$>-─ 
  (eq-trans 
    (eq-─ (eq-sym eq-Σ) (eq-sym eq-Σ)) 
  (eq-trans 
    (eq-─ (reify-⟦⟧≋ (sound-Σ id rel₂)) (reify-⟦⟧≋ (sound-Σ id rel₁))) 
  (eq-trans (eq-sym (↻-⇑-reify-─ ((λ ρ → ΣV) <$>V ρ₂) ((λ ρ → ΣV) <$>V ρ₁) {nr = NotRow<$> nr})) eq-refl))))))) , (refl-⟦⟧≋ (sound-Σ {nl = nl} id rel₂)) , ((refl-⟦⟧≋ (sound-Σ {nl = nl} id rel₁)))

map-Σ zero P rel = tt
map-Σ {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Σ {nl = nl} id rel-fzero) , (map-Σ n (P ∘ fsuc) rel-fsuc)


--------------------------------------------------------------------------------
-- Fundamental lemma  

fundC : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)

--------------------------------------------------------------------------------
-- Fundamental lemma for rows

fundCRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)
fundCRow [] e = tt
fundCRow ((l , τ) ∷ xs) e = (refl , fundC τ e ) , fundCRow xs e

--------------------------------------------------------------------------------
-- mapping an application over a row is application of the semantic row.

fundC-map-app : ∀ (n : ℕ) (P : Fin n → Label × SemType Δ₂ κ₁) →  
                (τ₁ : Type Δ₁ (κ₁ `→ κ₂)) → 
                (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
                {σ : Substitutionₖ Δ₁ Δ₂} → {η : SemEnv Δ₁ Δ₂} → 
                ⟦ σ ⟧≋e η → 
                ⟦ map (map₂ (_·_ (subₖ σ τ₁))) (⇑Row (reifyRow' n P)) ⟧r≋ (n , (λ x → P x .fst , eval τ₁ η id (P x .snd)))

fundC-map-app zero P _ _ _ = tt
fundC-map-app (suc n) P τ₁ (rel-fzero , rel-fsuc) {σ} e =
  (refl , (subst-⟦⟧≋ (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) (fundC τ₁ e id (rel-fzero .snd)))) ,
  fundC-map-app n (P ∘ fsuc) τ₁ rel-fsuc e

--------------------------------------------------------------------------------
-- Fundamental lemma for predicates
          
fundCPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η)           
fundCPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≋ (fundC ρ₁ e)) eq-· (reify-⟦⟧≋ (fundC ρ₂ e)) ~ (reify-⟦⟧≋ (fundC ρ₃ e))
fundCPred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≋ (fundC ρ₁ e)) eq-≲ (reify-⟦⟧≋ (fundC ρ₂ e))

--------------------------------------------------------------------------------
-- Fundamental lemma definition 

fundC (` α) {σ} {η} e = e α
fundC (`λ τ) {σ} {η} e ρ {v} {V} q = 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
    (subst-⟦⟧≋ 
      (eq-trans 
        (eq-trans 
          (inst (subₖ-cong (λ { Z → refl ; (S x) → trans (renₖ-subₖ-id ρ (σ x)) (↻-subₖ-renₖ (σ x)) }) τ)) 
          (inst (subₖ-comp τ))) 
        (inst (↻-subₖ-renₖ (subₖ (liftsₖ σ) τ)))) 
      (fundC τ (extend-⟦⟧≋ (ren-⟦⟧≋ ρ ∘ e) q)))
fundC (τ₁ · τ₂) {σ} {η} e  = 
  subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) 
    (fundC τ₁ e id (fundC τ₂ e))
fundC (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fundC τ₁ e) (fundC τ₂ e)
fundC (`∀ τ) {σ} {η} e = eq-∀ (fundC τ {liftsₖ σ} {lifte η} (weaken-⟦⟧≋ e))
fundC (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = subₖ σ τ}) 
        (eq-λ (fundC τ e S eq-refl)))
fundC (π ⇒ τ) {σ} {η} e = eq-⇒ (fundCPred π e) (fundC τ e)
fundC (lab l) {σ} {η} e = eq-refl
fundC ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fundC τ e)
fundC (Π {notLabel = nl}) {σ} {η} e = sound-Π {nl = nl}
fundC Σ {σ} {η} e = sound-Σ
fundC (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | inspect (λ x → eval x η) τ₂ | fundC τ₂ e 
... | row (n , P) _ | [[ eq ]] | eqₜ , rel = 
    (eq-trans 
      (eq-<$> 
        eq-refl
        eqₜ) 
    (eq-trans 
      eq-map 
      (eq-row (reify-⟦⟧r≋ (fundC-map-app n P τ₁ rel e) )))) , 
    refl-⟦⟧r≋ (fundC-map-app n P τ₁ rel e)  
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
          (reify-⟦⟧≋ (fundC τ₁ e id rel)))))) , 
  refl-⟦⟧≋ (fundC τ₁ e id rel)
fundC  {Δ₂ = Δ₂} ( _<$>_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {σ} {η} e | (ρ₂ ─ ρ₁) {nr} | [[ eq ]] | t-eq , rel₂ , rel₁ = 
  (eq-trans 
    (eq-<$> eq-refl t-eq) 
    (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify (ρ₂ ─ ρ₁))) (ρ₂ ─ ρ₁) (fundC τ₁ e) (eq-refl , rel₂ , rel₁) .fst)) , 
    refl-⟦⟧≋ (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify ρ₂)) ρ₂ (fundC τ₁ e) rel₂) , 
    refl-⟦⟧≋ (cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) (⇑ (reify ρ₁)) ρ₁ (fundC τ₁ e) rel₁)
fundC (τ₁ <$> τ₂) {σ} {η} e | φ <$> n | [[ eq ]] | (f , eq-f , rel-f) with eval τ₁ η | fundC τ₁ e
... | F | rel-F = cong-<$>⟦⟧≋ (subₖ σ τ₁) F (subₖ σ τ₂) (φ <$> n) rel-F (f , eq-f , rel-f)
fundC (⦅ xs ⦆ oxs) {σ} {η} e with fundCRow xs e
fundC (⦅ [] ⦆ tt) {σ} {η} e | tt = eq-refl , tt
fundC (⦅ (l , τ) ∷ xs ⦆ oxs) {σ} {η} e | ((refl , ih-τ) , ih-xs) = eq-row (eq-cons refl (reify-⟦⟧≋ (fundC τ e)) (reify-⟦⟧r≋ ih-xs)) , ((refl , refl-⟦⟧≋ ih-τ) , refl-⟦⟧r≋ ih-xs)
fundC (ρ₂ ─ ρ₁) {σ} {η} e with eval ρ₂ η | fundC ρ₂ e 
fundC (ρ₂ ─ ρ₁) {σ} {η} e | φ <$> n | (f , eq-f , rel-f) with eval ρ₁ η | fundC ρ₁ e 
... | φ₂ <$> n₂   | (g , eq-g , rel-g) = (eq-─ (reifySoundKripkeNE-≡t eq-f rel-f) (reifySoundKripkeNE-≡t eq-g rel-g)) , 
  (f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f) , 
  (g , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-g) , rel-g)
... | x₂ ▹ x₃  | ih' = (eq-─ (reifySoundKripkeNE-≡t eq-f rel-f) (ih' .fst)) , ((f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f) , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = 
  (eq-─ (reifySoundKripkeNE-≡t eq-f rel-f) (eq-trans (ih' .fst) (eq-row reflᵣ))) , 
  ((f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f)  , ((eq-row reflᵣ) , (ih' .snd)))
... | c ─ c₁   | ih' = 
    (eq-─ (reifySoundKripkeNE-≡t eq-f rel-f) (ih' .fst)) , 
    ((f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f) , (eq-refl , (ih' .snd .fst) , (ih' .snd .snd)))
fundC (ρ₂ ─ ρ₁) {σ} {η} e | x₁ ▹ x₂ | (eq , rel) with eval ρ₁ η | fundC ρ₁ e 
... | φ <$> n    | (f , eq-f , rel-f) = 
   eq-─ eq (reifySoundKripkeNE-≡t eq-f rel-f) , 
    (eq-refl , rel) , (f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f)
... | x₂ ▹ x₃  | ih' = eq-─ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
... | row ρ x₂ | ih' = eq-─ eq (eq-trans (ih' .fst) (eq-row reflᵣ)) , (eq-refl , rel) , (eq-row reflᵣ , (ih' .snd))
... | c ─ c₁   | ih' = eq-─ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
fundC (ρ₂ ─ ρ₁) {σ} {η} e | row (n , P) oP | ih with eval ρ₁ η | fundC ρ₁ e 
... | φ <$> n    | (f , eq-f , rel-f) = 
  eq-─ (eq-trans (ih .fst) (eq-row reflᵣ)) (reifySoundKripkeNE-≡t eq-f rel-f) , 
  ((eq-row reflᵣ , (ih .snd)) , f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f)
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
fundC (ρ₂ ─ ρ₁) {σ} {η} e | c ─ c₁ | ih with eval ρ₁ η | fundC ρ₁ e 
... | φ <$> n    | (f , eq-f , rel-f) = 
  eq-─ (ih .fst) (reifySoundKripkeNE-≡t eq-f rel-f) , 
  ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (f , eq-sym (reifySoundKripkeNE-≡t eq-refl rel-f) , rel-f))
... | x₂ ▹ x₃  | ih' = eq-─ (ih .fst) (ih' .fst) , ((eq-refl , (ih .snd)) , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = eq-trans (eq-─ (ih .fst) (ih' .fst)) (eq-─ eq-refl (eq-row reflᵣ)) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-row reflᵣ , (ih' .snd)))
... | c ─ c₁   | ih' = eq-─ (ih .fst) (ih' .fst) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
fundC (l ▹ τ) {σ} {η} e with eval l η | fundC l e
... | ne x₁ | ih = (eq-▹ ih (reify-⟦⟧≋ (fundC τ e))) , refl-⟦⟧≋ (fundC τ e)
... | lab l' | ih = eq-trans (eq-▹ eq-refl (reify-⟦⟧≋ (fundC τ e))) (eq-labTy ih) , 
                    (refl , (refl-⟦⟧≋ (fundC τ e))) , 
                    tt

--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity

⊢⟦_⟧≋ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≋ eval τ idEnv
⊢⟦ τ ⟧≋ = subst-⟦⟧≋ (inst (subₖ-id τ)) (fundC τ idSR)

--------------------------------------------------------------------------------
-- Consistency claim  

Consistency : Set 
Consistency = ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 

consistency : Consistency
consistency τ = reify-⟦⟧≋ (⊢⟦ τ ⟧≋)

 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (consistency τ₂) 

--------------------------------------------------------------------------------
-- Our definition of Consistency is equivalent to the converse of soundness

Completeness : Set 
Completeness = ∀ {Δ κ} → (τ₁ τ₂ : Type Δ κ) → ⇓ τ₁ ≡ ⇓ τ₂ → τ₁ ≡t τ₂

-- Consistency implies soundness-converse
Consistency→Completeness : Consistency → Completeness 
Consistency→Completeness consistency τ₁ τ₂ eq = eq-trans (consistency τ₁) (embed-≡t eq)

Completeness→Consistency : Completeness → Consistency
Completeness→Consistency ⇓-inj τ = (⇓-inj τ (⇑ (⇓ τ))) (sym (stability (⇓ τ)))

--------------------------------------------------------------------------------
-- ⇓ is injective w.r.t. type equivalence (converse of soundness lemma)

completeness : Completeness 
completeness = Consistency→Completeness consistency

-- A separate (and technically circular) proof of consistency
consistency₂ : Consistency
consistency₂ = Completeness→Consistency completeness

--------------------------------------------------------------------------------
-- consistency in lifted environments

consistency-liftsₖ : ∀ {Δ₁ κ} → (τ : Type (Δ₁ ,, κ₁) κ) → subₖ (liftsₖ `) τ ≡t ⇑ (reify (eval τ (lifte idEnv)))
consistency-liftsₖ τ = 
  reify-⟦⟧≋ (fundC τ (weaken-⟦⟧≋ {σ = `} {η = idEnv} idSR))
