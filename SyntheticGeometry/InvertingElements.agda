{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Algebra.Algebra
open Cubical.Algebra.Algebra.AlgebraHoms

open import Cubical.Algebra.CommRing using (CommRing)

open import Cubical.Algebra.CommRing.Localisation using (module InvertingElementsBase)

open import SyntheticGeometry.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation

open import SyntheticGeometry.CommAlgebra
import SyntheticGeometry.LocalisationAlgebra

module SyntheticGeometry.InvertingElements
  {ℓR : Level}
  (R : CommRing ℓR)
  where

  private
    module LocalisationAlgebra = SyntheticGeometry.LocalisationAlgebra R

  open LocalisationAlgebra hiding (module UniversalProperty; _[1/_])

  module _
    (let ℓA = ℓR)
    (A : CommAlgebra R ℓA)
    (a : ⟨ A ⟩)
    where

    private
      A-as-ring = CommAlgebra→CommRing A

    open CommAlgebraStr (str A)
    open InvertingElementsBase A-as-ring

    _∈[ⁿ|n≥0] : a ∈ [ a ⁿ|n≥0]
    _∈[ⁿ|n≥0] = ∣ 1 , sym (·IdR _) ∣₁

    private
      S : Σ[ S ∈ ℙ ⟨ A ⟩ ] isMultClosedSubset A S
      S = [ a ⁿ|n≥0] , powersFormMultClosedSubset a

    _[1/_] : CommAlgebra R ℓA
    _[1/_] = A LocalisationAlgebra.[1/ S ]

    module UniversalProperty where
      private
        module UniversalProperty = LocalisationAlgebra.UniversalProperty A S

        module _
          (let ℓB = ℓA)
          {B : CommAlgebra R ℓB}
          where

          from : ∀ (φ : CommAlgebraHom A B) → (φa-inv : φ $a a ∈ B ˣ) → (∀ p → (p∈S : p ∈ S .fst) → φ $a p ∈ B ˣ)
          from φ φa-inv = powersPropElim (λ p → ∈-isProp _ (φ $a p)) (λ n → subst (_∈ B ˣ) (sym (pres-^ φ a n)) (^-presUnit _ n φa-inv))

          to : ∀ (φ : CommAlgebraHom A B) → (φS-inv : ∀ p → (p∈S : p ∈ S .fst) → φ $a p ∈ B ˣ) → φ $a a ∈ B ˣ
          to φ φS-inv = φS-inv a _∈[ⁿ|n≥0]

          e : (Σ[ φ ∈ CommAlgebraHom A B ] (∀ a → (a∈S : a ∈ S .fst) → φ $a a ∈ B ˣ)) ≃ (Σ[ φ ∈ CommAlgebraHom A B ] (φ $a a ∈ B ˣ))
          e = Σ-cong-equiv-snd-prop
                (λ φ → isPropΠ (λ a → isPropΠ (λ a∈S → ∈-isProp (B ˣ) (φ $a a))))
                (λ φ → ∈-isProp (B ˣ) (φ $a a))
                to
                from

      module _
        (let ℓB = ℓA)
        {B : CommAlgebra R ℓB}
        where
    
        -- ext : Σ[ φ ∈ CommAlgebraHom A B ] (∀ a → (a∈S : a ∈ S .fst) → φ $a a ∈ B ˣ) → CommAlgebraHom (A [1/ S ]) B
        -- ext (φ , φS-inv) = S⁻¹AHasUniversalProp A (S .fst) (S .snd) B φ φS-inv .fst .fst
    
        res : CommAlgebraHom _[1/_] B → Σ[ φ ∈ CommAlgebraHom A B ] (φ $a a ∈ B ˣ)
        res φ = equivFun e (UniversalProperty.res φ)

      module _
        (let ℓB = ℓA)
        (B : CommAlgebra R ℓB)
        where

        universalProperty : isEquiv (res {B = B})
        universalProperty = compEquiv (_ , UniversalProperty.universalProperty B) e .snd
