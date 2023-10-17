{-# OPTIONS --safe #-}

module SyntheticGeometry.Powerset where

open import Cubical.Foundations.HLevels
import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude

open Cubical.Foundations.Powerset public

infix 7 _∈ₚ_

_∈ₚ_ : {ℓ : Level} → {X : Type ℓ} → (x : X) → (P : ℙ X) → hProp ℓ
x ∈ₚ P = x ∈ P , ∈-isProp P x
