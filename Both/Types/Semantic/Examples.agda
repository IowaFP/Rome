{-# OPTIONS --safe #-}
module Rome.Both.Types.Semantic.Examples where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming
open import Rome.Both.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Testing.

----------------------------------------
-- Labels.

ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
-- l l₁ l₂ l₃ : NormalType Δ L
ℓ  = lab "l"
-- l  = lab "l"

ℓ₁ = lab "l1"
-- l₁ = lab "l1"

ℓ₂ = lab "l2"
-- l₂ = lab "l2"

ℓ₃ = lab "l3"
-- l₃ = lab "l3"

----------------------------------------
-- Important types

wand : Type Δ ★ 
wand = `∀ (`∀ (`∀ (`∀ (`∀ 
    (((ℓ' ▹ τ) ≲ ρ₃) ⇒ ((ρ₁ · ρ₂ ~ ρ₃) ⇒ ((Π · ρ₁) `→ ((Π · ρ₂) `→ τ))))))))
    where  
        τ  = ` Z 
        ℓ' = ` (S Z)
        ρ₃ = ` (S (S Z))
        ρ₂ = ` (S (S (S Z)))
        ρ₁ = ` (S (S (S (S Z))))

`Π = (Π ·_)
`Σ = (Π ·_)


record-prj : Type ∅ ★
record-prj = `∀ (`Π (ℓ ▹ ` Z) `→ ` Z)

-- _ : ⇓ record-prj ≡ `∀ (Π ⦅ [ (ne (` Z)) ] ⦆ `→ ne (` Z))
-- _ = refl

----------------------------------------
-- Some function types.

app : Type Δ ((★ `→ ★) `→ ★ `→ ★)
app = (`λ (`λ ((` (S Z)) · (` Z))))

_ : ∀ {Δ} → ⇓ (app {Δ}) ≡ `λ (`λ (ne (` (S Z) · ne (` Z))))
_ = refl

app₂ : Type Δ (★ `→ (★ `→ ★) `→ ★)
app₂ = `λ (`λ ((` Z) · (` (S Z))))

_ : ∀ {Δ} → ⇓ (app₂ {Δ}) ≡ `λ (`λ (ne (` Z · ne (` (S Z)))))
_ = refl

ID : Type Δ (★ `→ ★)
ID = `λ (` Z)

_ : ∀ {Δ} → ⇓ (ID {Δ}) ≡ `λ (ne (` Z))
_ = refl

Const-U : Type Δ (★ `→ ★)
Const-U = `λ Unit

_ : ∀ {Δ} → ⇓ (Const-U {Δ}) ≡ `λ UnitNF
_ = refl




-- ----------------------------------------
-- -- Simple terms.

A₀ : Type Δ R[ ★ ]
A₀ = (ℓ ▹ Unit)

_ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡  ⦅ [ ("l" , UnitNF ) ] ⦆ tt
_ = refl

A₁ : Type (Δ ,, L) R[ ★ ] 
A₁ = (` Z ▹ Unit)

_ : ∀ {Δ} → ⇓ (A₁ {Δ}) ≡  (` Z ▹ₙ UnitNF)
_ = refl

-- ----------------------------------------
-- -- Row-kinded function types.

Id-R : Type Δ R[ ★ `→ ★ ]
Id-R = ℓ ▹ (`λ (` Z))

_ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡  ⦅ [ "l" , `λ (ne (` Z)) ]  ⦆ tt 
_ = refl

_ : ∀ {Δ} → ⇓ (Π · (Id-R {Δ})) ≡  `λ (Π (⦅ [ "l" , (ne (` Z)) ]  ⦆ tt )) 
_ = refl

-- app-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
-- app-R = ℓ₁ ▹ app

-- _ : ∀ {Δ} → ⇓ (app-R {Δ}) ≡  ⦅ [ ⇓ app ] ⦆
-- _ = refl

-- -- ----------------------------------------
-- -- -- Function types with congruences. 

-- C₁ : Type Δ ★
-- C₁ = Π · (ℓ ▹ Unit)

-- _ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π ⦅ [ UnitNF ] ⦆
-- _ = refl

-- C₂ : Type Δ (★ `→ ★)
-- C₂ = Π · (ℓ ▹ (`λ (` Z)))

-- _ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ `λ (Π ⦅ [ ne (` Z) ] ⦆)
-- _ = refl 

-- C₃ : Type Δ ★
-- C₃ = `Π (`Π (ℓ₁ ▹ (ℓ₂ ▹ ((app · Const-U) · Unit))))

-- _ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π ⦅ [ (Π ⦅ [ UnitNF ] ⦆) ] ⦆ 
-- _ = refl


-- -- ----------------------------------------
-- -- -- Unreduced Π applications

-- NR₀ : Type Δ ★
-- NR₀ = `Π (`Π (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- _ : ⇓ {Δ = Δ} NR₀ ≡ Π ⦅ [ (Π ⦅ [ UnitNF ] ⦆) ] ⦆ 
-- _ = refl 

-- NR₁ : Type Δ (L `→ L `→ ★ `→ ★)
-- NR₁ = `λ (`λ (`Π (` Z ▹ (`Π (` (S Z) ▹ ID)))))

-- _ : ⇓ {Δ = Δ} NR₁ ≡ `λ (`λ (`λ (Π ⦅ [ Π ⦅ [ ne (` Z) ] ⦆ ] ⦆)))
-- _ = refl


-- -- NR₂ : Type Δ R[ ★ ]
-- -- NR₂ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (((app · Const-U) · Unit))))

-- -- _ : ∀ {Δ} → ⇓ (NR₂ {Δ}) ≡  (l₁ ▹ (Π (l₂ ▹ UnitNF)))
-- -- _ = refl

-- -- NR₃ : Type Δ R[ ★ `→ ★ ]
-- -- NR₃ = `Π (ℓ₁ ▹ (ℓ₂ ▹ ID))

-- -- _ : ⇓ {Δ = Δ} NR₃ ≡  (l₁ ▹ `λ (Π (l₂ ▹ (ne (` Z)))))
-- -- _ = refl

-- -- NR₄ : Type Δ R[ R[ ★ ] ]
-- -- NR₄ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ Unit)))

-- -- _ : ⇓ {Δ = Δ} NR₄ ≡  (l₁ ▹ ( (l₂ ▹ (Π (l₃ ▹ UnitNF)))))
-- -- _ = refl

-- -- NR₅ : Type Δ R[ R[ ★ `→ ★ ] ]
-- -- NR₅ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ ID)))

-- -- _ : ⇓ {Δ = Δ} NR₅ ≡  (l₁ ▹ ( (l₂ ▹ `λ (Π (l₃ ▹ ne (` Z))))))
-- -- _ = refl


-- -- NR₆ : Type Δ R[ R[ R[ ★ `→ ★ ] ] ]
-- -- NR₆ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ (ℓ ▹ ID))))

-- -- _ : ⇓ {Δ = Δ} NR₆ ≡  (lab "l1" ▹  (lab "l2" ▹  (lab "l3" ▹ `λ (Π (lab "l" ▹ ne (` Z))))))
-- -- _ = refl


-- -- -- -- ----------------------------------------
-- -- -- -- -- Mixed Π and Σ w/ unreduced computation

-- mix₀ : Type Δ ★
-- mix₀ = `Π (`Σ (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- _ : ⇓ {Δ = Δ} mix₀ ≡ Π ⦅ [ Σ ⦅ [ UnitNF ] ⦆ ] ⦆
-- _ = refl


-- -- -- -- --------------------------------------------------------------------------------
-- -- -- -- -- Lifting nonsense

-- lift-λ : Type Δ ★
-- lift-λ = `Π (`λ (` Z) <$> (ℓ ▹ Unit))

-- _ : ⇓ {Δ = Δ} lift-λ ≡ Π ⦅ [ UnitNF ] ⦆
-- _ = refl

-- lift-λ₂  : Type Δ ((★ `→ ★) `→ R[ ★ ])
-- lift-λ₂ = `Π (ℓ₁ ▹ (`λ (`λ (` Z) <$> (ℓ₂ ▹ Unit)))) -- `Π (ℓ₁ ▹ (`λ  (↑ · (` Z)) · (ℓ₂ ▹ Unit)))

-- _ : ⇓ {Δ = Δ} lift-λ₂ ≡ `λ ⦅ [ Π ⦅ [ UnitNF ] ⦆ ] ⦆
-- _ = refl

-- lift-var : Type Δ (R[ ★ ] `→ R[ ★ ])
-- lift-var = `λ (`λ (` Z) <$> (` Z))

-- _ : ⇓ {Δ = Δ} lift-var ≡ `λ (ne (`λ (ne (` Z)) <$> ` Z))
-- _ = refl 

-- lift-assoc₁ : Type Δ ★
-- lift-assoc₁ =  (Π · (ℓ ▹ `λ (` Z))) · Unit

-- _ : ⇓ {Δ = Δ} lift-assoc₁ ≡ Π ⦅ [ UnitNF ] ⦆
-- _ = refl

-- lift-assoc₂ : Type (Δ ,, (★ `→ ★)) ★
-- lift-assoc₂ =  (Π · (ℓ ▹ F)) · Unit 
--     where
--         F = ` Z

-- _ : ⇓ {Δ = Δ ,, (★ `→ ★)} lift-assoc₂ ≡ Π ⦅ [ ne (` Z · UnitNF) ] ⦆
-- _ = refl

-- lift-assoc₃ : Type (Δ ,, R[ ★ `→ ★ ]) ★
-- lift-assoc₃ =  (Π · F) · Unit
--     where
--         F = ` Z

-- lift-assoc₃' : Type (Δ ,, R[ ★ `→ ★ ]) ★
-- lift-assoc₃' =  Π · (F ?? Unit)
--     where
--         F = ` Z

-- _ : ⇓ {Δ = Δ ,, R[ ★ `→ ★ ]} lift-assoc₃ ≡ ⇓ {Δ = Δ ,, R[ ★ `→ ★ ]} lift-assoc₃'
-- _ = refl

-- --------------------------------------------------------------------------------
-- -- Commuting λ's out of rows

-- ffs : Type Δ (★ `→ ★)
-- ffs = Π · ⦅ (`λ (` Z) ∷ (`λ Unit) ∷ []) ⦆

-- _ : ⇓ {Δ = ∅} ffs ≡ `λ (Π ⦅ ne (` Z) ∷ weakenₖNF UnitNF ∷ [] ⦆) 
-- _ = refl



-- -- --------------------------------------------------------------------------------
-- -- -- Simple rows

-- _ : Type Δ ★
-- _ = (`∀ (((` Z) ≲ ⦅ Unit ∷ Unit ∷ [] ⦆) ⇒ ((Π · (` Z)) `→ Unit)))
 
