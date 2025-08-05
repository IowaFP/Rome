{-# OPTIONS --safe #-}
module Rome.RelatingSemantics.Kinds.GVars where

open import Rome.RelatingSemantics.Kinds.Syntax
open import Rome.Preludes.Level

-- variable
--   ι ι₁ ι₂ ι₃ : Level
--   Δ Δ₁ Δ₂ Δ₃ : KEnv ιΔ 
--   κ κ₁ κ₂ κ₃ : Kind ι

variable
  ι ι₁ ι₂ ι₃ : Level
  ιΔ ιL ιΓ ιΦ ικ ικ₁ ικ₂ ικ₃ ικ₄ ικ₅ : Level
  κ κ' : Kind ικ
  κ₁ : Kind ικ₁
  κ₂ : Kind ικ₂
  κ₃ : Kind ικ₃
  κ₄ : Kind ικ₄
  κ₅ : Kind ικ₅
  Δ Δ₁ Δ₂ Δ₃ : KEnv ιΔ 
