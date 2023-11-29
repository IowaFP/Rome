{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, RankNTypes, ExistentialQuantification, DataKinds, GADTs, TypeOperators, PolyKinds, FlexibleContexts #-}

{-- Toying with some encodings of Rω etc in hs. --}
module FCR where

--------------------------------------------------------------------------------
--
data l :> t = LabTy t

type Row = [*]

data Record (r :: Row) where
  Empty :: Record r
  Ext   :: (l :> t) -> Record r -> Record ((l :> t) :: r)

class Comb a b c where
  
wand :: forall l. forall t. forall (r1 :: Row). forall (r2 :: Row). forall (r3 :: Row).
        Comb r1 r2 r3 => Record r1 -> Record r2 -> Record r3
wand = _

-- r : Row
-- r = 



--------------------------------------------------------------------------------
--

data Nat = Z | S Nat
data Ix (a :: Nat) where
  Fz :: forall (n :: Nat). Ix n
  Fs :: forall (n :: Nat). (Ix n) -> (Ix (S n))
