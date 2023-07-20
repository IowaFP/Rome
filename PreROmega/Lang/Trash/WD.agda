--------------------------------------------------------------------------------
-- Why trash: I believe ⊢ₑ implies WD.

--------------------------------------------------------------------------------
-- Well defined Types. From MetaLib:
{-

(** A type [T] is well-defined with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    @ahubers:
    N.B. Why not roll this in with LC? Having so many predicates is:
    (i) confusing to the reader, and
    (ii) annoying to the writer.
-}

data WDₜ : Env → Type → Set
data WDπ : Env → Pred → Set

data WDₜ where
   wdₓ : ∀ Γ a →
          a ∈ dom Γ →
        -----------------
         WDₜ Γ (fvar a)
         
   wd∀ : ∀ L Γ k t →
           cofinite L (λ a → WDₜ ((a ⦂ₖ k) ∷ Γ) (t ^ₜ fvar a)) →
         -------------------------------------------------------
                          WDₜ Γ (`∀ k t)
                          
   wdλ : ∀ L Γ k t →
         cofinite L (λ a → WDₜ ((a ⦂ₖ k) ∷ Γ) (t ^ₜ fvar a)) →
         --------------------------------------------------
                          WDₜ Γ (`λ k t)
                          
   wd⇒ : ∀ Γ p t →
           WDπ Γ p   →   WDₜ Γ t   →
           --------------------------
                WDₜ Γ (p ⇒ t)

   wd· : ∀ Γ t₁ t₂ →
           WDₜ Γ t₁   →   WDₜ Γ t₂ →
           --------------------------
                 WDₜ Γ (t₁ · t₂)
   
   wdℓ : ∀ Γ l →
   
         -----------
         WDₜ Γ (ℓ l)
         
   wd⌊⌋ : ∀ Γ t →
           WDₜ Γ t →
         --------------
           WDₜ Γ ⌊ t ⌋
           
   wd▹ : ∀  Γ t₁ t₂ →
           WDₜ Γ t₁   →   WDₜ Γ t₂ →
           -------------------------
                WDₜ Γ (t₁ ▹ t₂)
                
          
   wdΠ  : ∀ Γ t →
          WDₜ Γ t →
          ----------
          WDₜ Γ (Π t)
   wdΣ  : ∀ Γ t →
          WDₜ Γ t →
          ----------
          WDₜ Γ (Σ t)

data WDπ where
  WD≲        : ∀ Γ t₁ t₂ →
               WDₜ Γ t₁ → WDₜ Γ t₂ →
               ----------------------
                  WDπ Γ (t₁ ≲ t₂)
                  
  wd·~       : ∀ Γ t₁ t₂ t₃ →
                  WDₜ Γ t₁   →   WDₜ Γ t₂   →   WDₜ Γ t₃ →
                  ------------------------------------------
                           WDπ Γ (t₁ · t₂ ~ t₃)
