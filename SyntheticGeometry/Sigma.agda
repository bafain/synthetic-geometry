{-# OPTIONS --safe #-}

module SyntheticGeometry.Sigma where

open import Cubical.Data.Sigma public

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic

module _
  {ℓA}  {A  : Type ℓA}
  {ℓB}  {B  : (a : A) → Type ℓB}  (B-prop  : ∀ a → isProp (B  a))
  {ℓB'} {B' : (a : A) → Type ℓB'} (B'-prop : ∀ a → isProp (B' a))
  where

  Σ-cong-equiv-snd-prop : (to : ∀ a → B a → B' a) → (from : ∀ a → B' a → B a) → Σ A B ≃ Σ A B'
  Σ-cong-equiv-snd-prop = Σ-cong-equiv-prop (idEquiv A) B-prop B'-prop
