{-# OPTIONS --safe              #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Algebra.Algebra
open Cubical.Algebra.Algebra.AlgebraHoms

open import SyntheticGeometry.CommAlgebra
import Cubical.Algebra.CommAlgebra.LocalisationAlgebra

open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.CommRing.Localisation hiding (isMultClosedSubset)

open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import SyntheticGeometry.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic

module SyntheticGeometry.LocalisationAlgebra
  {ℓR : Level}
  (R : CommRing ℓR)
  where

open Cubical.Algebra.CommAlgebra.LocalisationAlgebra R public

module _
  {ℓA : Level}
  (A : CommAlgebra R ℓA)
  where

  private
    A-as-ring = CommAlgebra→CommRing A
  
  isMultClosedSubset = Cubical.Algebra.CommRing.Localisation.isMultClosedSubset A-as-ring
  
  module _
    (S : Σ[ S ∈ ℙ ⟨ A ⟩ ] isMultClosedSubset S)
    where
  
    _[1/_] : CommAlgebra R ℓA
    _[1/_] = S⁻¹AAsCommAlgebra A (S .fst) (S .snd)

module UniversalProperty
  (let ℓA = ℓR)
  (A : CommAlgebra R ℓA)
  (S : Σ[ S ∈ ℙ ⟨ A ⟩ ] isMultClosedSubset A S)
  where

  open S⁻¹AUniversalProp public

  private
    A-as-ring = CommAlgebra→CommRing A

  _/1 : ⟨ A ⟩ → ⟨ A [1/ S ] ⟩
  _/1 = S⁻¹RUniversalProp._/1 A-as-ring (S .fst) (S .snd)

  S/1-inv : ∀ a → (a∈S : a ∈ S .fst) → a /1 ∈ A [1/ S ] ˣ
  S/1-inv = S⁻¹RUniversalProp.S/1⊆S⁻¹Rˣ A-as-ring (S .fst) (S .snd)

  module _
    (let ℓB = ℓA)
    {B : CommAlgebra R ℓB}
    where

    -- ext : Σ[ φ ∈ CommAlgebraHom A B ] (∀ a → (a∈S : a ∈ S .fst) → φ $a a ∈ B ˣ) → CommAlgebraHom (A [1/ S ]) B
    -- ext (φ , φS-inv) = S⁻¹AHasUniversalProp A (S .fst) (S .snd) B φ φS-inv .fst .fst

    res : CommAlgebraHom (A [1/ S ]) B → Σ[ φ ∈ CommAlgebraHom A B ] (∀ a → (a∈S : a ∈ S .fst) → φ $a a ∈ B ˣ)
    res φ = φ ∘a /1AsCommAlgebraHom A (S .fst) (S .snd) , λ a a∈S → pres-inv φ (a /1) (S/1-inv a a∈S)

  module _
    (let ℓB = ℓA)
    (B : CommAlgebra R ℓB)
    where

    private
      module _
        {ℓA : Level}
        {A : Type ℓA}
        {ℓB : Level}
        {B : Type ℓB}
        (f : A → B)
        {ℓP : Level}
        (P : B → hProp ℓP)
        (r : ∀ b → ⟨ P b ⟩ → ∃![ a ∈ A ] f a ≡ b)
        (f-p : ∀ a → ⟨ P (f a) ⟩)
        where

        private
          f' : A → Σ[ b ∈ B ] ⟨ P b ⟩
          f' a = f a , f-p a

          f'-equiv : isEquiv f'
          f'-equiv .equiv-proof = λ (b , p) → isOfHLevelRespectEquiv 0 (invEquiv (obs b p)) (r b p)
            where
              obs : ∀ b p → fiber f' (b , p) ≃ fiber f b
              obs b p = Σ-cong-equiv-snd (λ a → invEquiv (ΣPathTransport≃PathΣ (f' a) (b , p))) ∙ₑ
                        invEquiv Σ-assoc-≃ ∙ₑ
                        Σ-contractSnd (λ _ → isProp→isContrPath (P b .snd) _ _)
        
        e : A ≃ (Σ[ b ∈ B ] ⟨ P b ⟩)
        e = f' , f'-equiv

        _ : ∀ a → equivFun e a .fst ≡ f a
        _ = λ a → refl

    universalProperty : isEquiv (res {B = B})
    universalProperty = e
      (λ φ' → res {B = B} φ' .fst)
      (λ φ → ∀[ a ∶ ⟨ A ⟩ ] a ∈ₚ S .fst ⇒ φ $a a ∈ₚ B ˣ)
      (λ φ φS-inv → isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd (λ _φ → AlgebraHom≡Equiv _ _)) (S⁻¹AHasUniversalProp A (S .fst) (S .snd) B φ φS-inv))
      (λ φ' → res {B = B} φ' .snd)
      .snd
