{-# OPTIONS --safe #-}
module Rome.Both.Kinds.GVars where

open import Rome.Both.Kinds.Syntax
open import Rome.Preludes.Level

-- variable
--   ι ι₁ ι₂ ι₃ : Level
--   Δ Δ₁ Δ₂ Δ₃ : KEnv ιΔ 
--   κ κ₁ κ₂ κ₃ : Kind ι

variable
  ι ι₁ ι₂ ι₃ ι₄ ι₅ ι∅ : Level
  ιΔ ιΔ₁ ιΔ₂ ιΔ₃ ιΔ₄ ιΦ ιΦ₁ ιΦ₂ ιΦ₃ ιΦ₄ ιL ιΓ ικ ικ' ικ₁ ικ₂ ικ₃ ικ₄ ικ₅ : Level
  κ κ' : Kind ικ
  κ₁ : Kind ικ₁
  κ₂ : Kind ικ₂
  κ₃ : Kind ικ₃
  κ₄ : Kind ικ₄
  κ₅ : Kind ικ₅
  Δ Δ₁ Δ₂ Δ₃ : KEnv ιΔ 
