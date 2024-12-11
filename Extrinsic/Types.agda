module Rome.Extrinsic.Types where

open import Rome.Extrinsic.Kinds
open import Data.String

Label = String

--------------------------------------------------------------------------------
-- 2.4 Types v

data Type (v : Set) : Set where

  Unit :

      --------
      Type v

  ` : 
      v →
      --------
      Type v

  `λ : 
      
      Type v → 
      ---------------
      Type v

  _·_ : 
      
      Type v → 
      Type v → 
      ----------------
      Type v

  _`→_ : 

         Type v →
         Type v → 
         --------
         Type v

  `∀    :
      
         (κ : Kind) → Type v →
         -------------
         Type v

  μ     :
      
         Type v → 
         -------------
         Type v

  ------------------------------------------------------------------
  -- Rω business
  
  -- labels
  lab :
    
        Label → 
        --------
        Type v

  -- singleton formation
  _▹_ :
        Type v → Type v →
        -------------------
        Type v

  -- Row singleton formation
  _R▹_ :
         Type v → Type v →
         -------------------
         Type v

  -- label constant formation
  ⌊_⌋ :
        Type v →
        ----------
        Type v

  -- Record formation
  Π     :

          Type v → 
          ----------------
          Type v

  -- Variant formation
  Σ     :

          Type v → 
          ----------------
          Type v

  ↑_ : 

       Type v →
       ------------------------------
       Type v


  _↑ : 

       Type v →
       ------------------------------
       Type v

