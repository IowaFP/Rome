
--------------------------------------------------------------------------------
-- Why trash: Local closure follows from well-typing, and we are using
-- an intrinsic semantics.
--
-- Also, I literally can't find a place yet I've need this.

--------------------------------------------------------------------------------
-- Local closure:
-- 
-- The proposition [LC t] holds whewn a type [t] is locally closed,
-- meaning it has no unbound indices.

-- For example:
--   λ.λ.0 1
-- is locally closed, whereas
--   λ.7
-- is not.

-- You have the same requirement of De Bruijn indices:
-- we must restrict the set of locally nameless terms down to only
-- those which correspond directly to terms in the regular lambda calculus.
-- In short: "No junk".

data LCₜ    : Type → Set
data LCπ : Pred → Set

data LCₜ where
  -- N.B. only *free* variables are locally closed, because
  -- the lc rules at binding sites *open* the type, which
  -- makes bound terms free.
  lcₓ             : ∀ a →
  
                    -----------
                    LCₜ (fvar a)
                    
  _lc→_           : ∀ t₁ t₂ →
                   LCₜ t₁   →   LCₜ t₂ →
                   ---------------------
                      LCₜ (t₁ `→ t₂)
                      
  _lc⇒_           : ∀ p t →
                    
                    LCπ p   →   LCₜ t →
                    ---------------------
                        LCₜ (p ⇒ t)
                        
  lc∀             :  ∀ L t k →
                      cofinite L (λ a → LCₜ (t ^ₜ fvar a)) → 
                  -----------------------------------------
                                LCₜ (`∀ k t)
                                
  lcλ             :  ∀ L t k →
                      cofinite L (λ a → LCₜ (t ^ₜ fvar a)) →
                   -----------------------------------------
                                 LCₜ (`λ k t)
                                 
  _lc·_           : ∀ t₁ t₂ →
                    LCₜ t₁   →   LCₜ t₂ →
                    ----------------------
                         LCₜ (t₁ · t₂)
                         
  lcℓ             : ∀ (l : Label) →
  
                    ---------
                    LCₜ (ℓ l)
                    
  lc⌊_⌋           : ∀ t →
                      LCₜ t → 
                   --------------
                   LCₜ ( ⌊ t ⌋ )
                   
  _lc▹_           : ∀ t₁ t₂ →
                    LCₜ t₁   →   LCₜ t₂ →
                    ----------------------
                        LCₜ (t₁ ▹ t₂)
                    
  lcΠ             : ∀ t →
                    LCₜ t →
                    ---------
                    LCₜ (Π t)
                    
  lcΣ             : ∀ t →
                    LCₜ t →
                    -----------
                    LCₜ (Σ t)

data LCπ where
  lc≲ : ∀ z₁ z₂ →
        LCₜ z₁   →   LCₜ z₂ →
        ---------------------
            LCπ (z₁ ≲ z₂)
            
  lc~ : ∀ z₁ z₂ z₃ →
        LCₜ z₁   →   LCₜ z₂   →   LCₜ z₃ →
        -----------------------------------
                LCπ (z₁ · z₂ ~ z₃)
