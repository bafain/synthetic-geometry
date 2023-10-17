{-# OPTIONS --safe #-}

open import Cubical.Algebra.Algebra
import Cubical.Algebra.CommAlgebra

open import Cubical.Algebra.CommRing hiding (_ˣ)
open import Cubical.Algebra.CommRing.Localisation

open import Cubical.Data.Nat hiding (_·_; _^_)
open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation

module SyntheticGeometry.CommAlgebra
  where

open Cubical.Algebra.CommAlgebra public

module _
  {ℓR : Level}
  {R : CommRing ℓR}
  where

  _ˣ : {ℓA : Level} → (A : CommAlgebra R ℓA) → ℙ ⟨ A ⟩
  A ˣ = CommAlgebra→CommRing A Cubical.Algebra.CommRing.ˣ

  module _
    {ℓA : Level}
    {A : CommAlgebra R ℓA}
    where

    private
      A-as-ring = CommAlgebra→CommRing A

    open Cubical.Algebra.CommRing.Exponentiation A-as-ring public using (^-presUnit)

    module _
      (let ℓB = ℓA)
      {B : CommAlgebra R ℓB}
      (φ : CommAlgebraHom A B)
      where
        private
          B-as-ring = CommAlgebra→CommRing B
      
        open CommAlgebraStr (str B)
        open CommRingHomTheory {ℓA} {A-as-ring} {B-as-ring} (CommAlgebraHom→CommRingHom A B φ)
        open Cubical.Algebra.CommRing.Exponentiation A-as-ring using () renaming (_^_ to _^A_)
        open Cubical.Algebra.CommRing.Exponentiation B-as-ring using () renaming (_^_ to _^B_)
        open InvertingElementsBase A-as-ring using (powersPropElim) renaming ([_ⁿ|n≥0] to [_ⁿ|n≥0]A)
        open InvertingElementsBase B-as-ring using () renaming ([_ⁿ|n≥0] to [_ⁿ|n≥0]B)
        open IsAlgebraHom (φ .snd)
      
        pres-inv : ∀ a → (a-inv : a ∈ A ˣ) → φ $a a ∈ B ˣ
        pres-inv a a-inv = RingHomRespInv a {{a-inv}}
      
        pres-^ : ∀ a n → φ $a (a ^A n) ≡ (φ $a a) ^B n
        pres-^ a zero    = pres1
        pres-^ a (suc n) = pres· _ _ ∙ congS (λ hole → _ · hole) (pres-^ a n)
      
        pres-powers : ∀ a p → (p-exp : p ∈ [ a ⁿ|n≥0]A) → φ $a p ∈ [ φ $a a ⁿ|n≥0]B
        pres-powers a = powersPropElim (λ p → ∈-isProp [ φ $a a ⁿ|n≥0]B (φ $a p)) (λ n → ∣ n , pres-^ a n ∣₁)
      
        module _
          (ψ : CommAlgebraHom A B)
          where
          AlgebraHom≡Equiv : (φ .fst ≡ ψ .fst) ≃ (φ ≡ ψ)
          AlgebraHom≡Equiv = Σ≡PropEquiv (λ φ → isPropIsAlgebraHom _ _ φ _)
