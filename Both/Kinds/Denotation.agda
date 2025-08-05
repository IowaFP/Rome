module Rome.Both.Kinds.Denotation where

open import Rome.Both.Prelude
open import Rome.Preludes.Level
open import Rome.Both.Kinds.Syntax 
open import Rome.Both.Kinds.GVars
open import Rome.IndexCalculus using (Row ; sing ; ε ; _⨾⨾_)
--------------------------------------------------------------------------------
-- Denotation

⟦_⟧k : Kind ι → Set (lsuc ι)
⟦ ★ {ι} ⟧k = Set ι
⟦ κ₁ `→ κ₂ ⟧k = ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
⟦ L {ι} ⟧k = Label'
⟦ R[ k ] ⟧k = Row (Label × ⟦ k ⟧k)

⟦_⟧ke : KEnv ι → Set (lsuc ι)
⟦ (∅ {ι = ι}) ⟧ke = ⊤' {lsuc ι}
⟦ Δ ,, κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k
