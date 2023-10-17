import Cubical.Data.FinData
open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude

module SyntheticGeometry.FinData where

private
  variable
    ℓ   : Level
    A B : Type ℓ
    n   : ℕ

open Cubical.Data.FinData public

_∷Fin_ : (a : A) → (as : FinVec A n) → FinVec A (1 + n)
_∷Fin_ a as zero    = a
_∷Fin_ a as (suc i) = as i

mapFin : (f : A → B) → (as : FinVec A n) → FinVec B n
mapFin f as i = f (as i)
