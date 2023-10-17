```agda
{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Algebra.Algebra using (_$a_)

open import SyntheticGeometry.CommAlgebra using (CommAlgebra; _ˣ) -- CommAlgebraHom; CommAlgebra→CommRing; CommAlgebraHom→RingHom
open import Cubical.Algebra.CommAlgebra.Instances.Initial using () renaming (initialCAlg to _-as-algebra)
import SyntheticGeometry.InvertingElements using (module UniversalProperty; _[1/_])
-- import SyntheticGeometry.LocalisationAlgebra

open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.CommRing.LocalRing using (isLocal)

-- open import Cubical.Data.Nat using (ℕ)

open import Cubical.Foundations.Equiv using (invEquiv; _≃_)
open import Cubical.Foundations.Powerset using (_∈_) -- ℙ
open import Cubical.Foundations.Prelude using (Level; Σ-syntax; _,_) -- Type; Σ-syntax; sym; fst; snd
open import Cubical.Foundations.Structure using (⟨_⟩)

-- open import Cubical.Functions.Logic using (∃[∶]-syntax)

-- open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

import SyntheticGeometry.Affine using (is-affine)
import SyntheticGeometry.Open using (qc-open-as-type; qc-opens-in) renaming (simple-qc-open-prop to is-invₒ)
import SyntheticGeometry.Spec using (Spec)
open import SyntheticGeometry.SQC using (sqc-over-itself)

module SyntheticGeometry.StandardOpen 
  {ℓR : Level}
  (R : CommRing ℓR)
  where

open SyntheticGeometry.InvertingElements R

open SyntheticGeometry.Open R
open SyntheticGeometry.Spec R

module _
  (let ℓA = ℓR)
  (A : CommAlgebra R ℓA)
  (f : ⟨ A ⟩)
  where

  -- Standard open subset (Definition 1.3.11)
  D : qc-opens-in (Spec A)
  D = λ x → is-invₒ (x $a f)

  -- (total(D(f)) =) Σₓ D(f)(x) = Spec(A[f⁻¹]) (Proposition 3.1.6)
  module _ where
    open UniversalProperty A f

    _ : qc-open-as-type D ≃ Spec (A [1/ f ])
    _ = invEquiv (_ , universalProperty (R -as-algebra))

  module _
    (R-local : isLocal R)
    (R-sqc   : sqc-over-itself R)
    where

    open SyntheticGeometry.Affine R R-local R-sqc

    -- Hom(R[X]/(p)[1/inc(q)],A) ≃ Σ (φ : Hom(R[X]/(p),A)) φ(inc(q)) ∈ Aˣ
    --                           ≃ Σ (φ : Hom(R[X],A)) φ(p) = 0 × φ(q) ∈ Aˣ
    --                           ≃ Σ (φ : Hom(R,A), a : A) lift(φ,a)(p) = 0 × lift(φ,a)(q) ∈ Aˣ
    --                           ≃ Σ (φ : Hom(R,A), a : A, b : A) lift(φ,a)(p) = 0 × lift(φ,a)(q)b - 1 = 0
    --                           ≃ Σ (φ : Hom(R[X,Y],A)) lift(φ∘incXY,φ(X))(p) = 0 × lift(φ∘incXY,φ(X))(q)φ(Y) - 1 = 0
    --                           ≃ Σ (φ : Hom(R[X,Y],A)) φ(incY(p)) = 0 × φ(incYq)φ(Y) - 1 = 0
    --                           ≃ Hom(R[X,Y]/(incY(p),incY(q)Y-1),A)
    -- D-affine : ⟨ is-affine (qc-open-as-type D) ⟩
    -- D-affine = {!!}
```
