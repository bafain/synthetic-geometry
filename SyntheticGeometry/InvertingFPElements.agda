open import SyntheticGeometry.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FGIdeal
import Cubical.Algebra.CommAlgebra.FPAlgebra
open import SyntheticGeometry.FreeCommAlgebra
import SyntheticGeometry.InvertingElements
-- open import SyntheticGeometry.LocalisationAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra

open import Cubical.Algebra.CommRing

open import SyntheticGeometry.FinData
open import Cubical.Data.Nat
-- open import Cubical.Data.Vec

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

module SyntheticGeometry.InvertingFPElements
  {ℓR : Level}
  (R : CommRing ℓR)
  (let Polynomials : (n : ℕ) → CommAlgebra R ℓR
       Polynomials = λ n → Cubical.Algebra.CommAlgebra.FPAlgebra.Polynomials {ℓR} {R} n)
  (n : ℕ)
  {m : ℕ}
  (relation : FinVec ⟨ Polynomials n ⟩ m)
  (p : ⟨ Polynomials n ⟩)
  (let ℓB = ℓR)
  (B : CommAlgebra R ℓB)
  where

  open CommAlgebraStr (str (Polynomials n)) using () renaming (_·_ to _·n_)
  open SyntheticGeometry.InvertingElements R

  private
    FPAlgebra : (n : ℕ) → {m : ℕ} → (relation : FinVec ⟨ Polynomials n ⟩ m) → CommAlgebra R ℓR
    FPAlgebra = λ n relation → Polynomials n / generatedIdeal (Polynomials n) relation

    var : (n : ℕ) → ⟨ Polynomials (1 + n) ⟩
    var n = Construction.var (fromℕ n)

    weaken : ⟨ Polynomials n ⟩ → ⟨ Polynomials (1 + n) ⟩
    weaken = mapFree R weakenFin

    f : ⟨ FPAlgebra n relation ⟩
    f = [ p ]/

  _ : CommAlgebraHom (FPAlgebra n relation [1/ f ]) B ≃ CommAlgebraHom (FPAlgebra (1 + n) (var n ∷Fin mapFin weaken relation)) B
  _ = {!!}
