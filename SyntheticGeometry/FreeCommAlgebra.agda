import Cubical.Algebra.CommAlgebra.FreeCommAlgebra

open import Cubical.Algebra.CommRing

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

module SyntheticGeometry.FreeCommAlgebra where

open Cubical.Algebra.CommAlgebra.FreeCommAlgebra public

module _
  {ℓR : Level}
  (R : CommRing ℓR)
  {ℓX : Level}
  {X  : Type ℓX}
  {ℓY : Level}
  {Y  : Type ℓY}
  where

  mapFree : (f : X → Y) → ⟨ R [ X ] ⟩ → ⟨ R [ Y ] ⟩
  mapFree f = inducedHom (R [ Y ]) (λ x → Construction.var (f x)) .fst
