Facts about the projective line ℙ¹
==================================

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout as Pushout

open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveLine
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open import SyntheticGeometry.Open k
open import SyntheticGeometry.Affine k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open SyntheticGeometry.SQC k
```

Exhibit ℙ¹ as a pushout of two copies of 𝔸¹.

```agda
𝔸¹ˣ : Type ℓ
𝔸¹ˣ = Σ[ x ∈ ⟨ k ⟩ ] x ∈ k ˣ

private
  f g : 𝔸¹ˣ → ⟨ k ⟩
  f (x , _) = x
  g (_ , (x⁻¹ , _)) = x⁻¹

ℙ¹-as-pushout : Type ℓ
ℙ¹-as-pushout =
  Pushout {A = 𝔸¹ˣ} {B = ⟨ k ⟩} {C = ⟨ k ⟩} f g

module Comparison
  where

  open CommRingStr (snd k)
  open Consequences k k-local

  inversion : 𝔸¹ˣ → 𝔸¹ˣ
  inversion (x , x-inv) = (x ⁻¹) , RˣInvClosed x
    where
    open Units k
    instance
      _ : x ∈ k ˣ
      _ = x-inv

  -- Just checking that this is definitional.
  g≡f∘inversion : (x : 𝔸¹ˣ) → g x ≡ f (inversion x)
  g≡f∘inversion x = refl

  isEquiv-inversion : isEquiv inversion
  isEquiv-inversion = involIsEquiv (λ x → Σ≡Prop (snd ∘ (k ˣ)) refl)

  isSet-ℙ¹-as-pushout : isSet ℙ¹-as-pushout
  isSet-ℙ¹-as-pushout =
    Pushout.preserveHLevelEmbedding _ _
      isEmbedding-f
      (isEmbedding-∘ isEmbedding-f (isEquiv→isEmbedding isEquiv-inversion))
      is-set
      is-set
    where
    isEmbedding-f = snd (snd (Subset→Embedding (k ˣ)))

  module To
    where

    ι₀ ι₁ : ⟨ k ⟩ → 𝔸ⁿ⁺¹-0 1
    ι₀ x = (λ{ zero → 1r ; one → x }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 zero))
    ι₁ x = (λ{ zero → x ; one → 1r }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 one))

    -- I think we will also need the converse...?
    path : (x y : ⟨ k ⟩) → x · y ≡ 1r → [ ι₀ x ] ≡ [ ι₁ y ]
    path x y xy≡1 =
      let yx≡1 : y · x ≡ 1r
          yx≡1 = ·Comm y x ∙ xy≡1
      in eq/ _ _ (y , ((x , yx≡1) , funExt (λ{ zero → ·IdR y ; one → yx≡1 })))

    to : ℙ¹-as-pushout → ℙ 1
    to (inl x) = [ ι₀ x ]
    to (inr x) = [ ι₁ x ]
    to (push (x , y , xy≡1) i) = path x y xy≡1 i

  module From
    where

    from-𝔸²-0 : 𝔸ⁿ⁺¹-0 1 → ℙ¹-as-pushout
    from-𝔸²-0 (xy , xy≢0) =
        let x = xy zero
            y = xy one
        in
          PT.rec→Set
            isSet-ℙ¹-as-pushout
            (λ{ (zero , x⁻¹ , _) → inl (x⁻¹ · y)
              ; (one , y⁻¹ , _) → inr (y⁻¹ · x) })
            (λ{ (zero , _) (zero , _) → cong (λ x-inv → inl (fst x-inv · y)) (snd ((k ˣ) x) _ _)
              ; (zero , x-inv) (one , y-inv) → {!!}
              ; (one , y-inv) (zero , x-inv) → {!!}
              ; (one , _) (one , _) → cong (λ y-inv → inr (fst y-inv · x)) (snd ((k ˣ) y) _ _)})
            (generalized-field-property k-local k-sqc xy xy≢0)

    from : ℙ 1 → ℙ¹-as-pushout
    from = SQ.rec
      isSet-ℙ¹-as-pushout
      from-𝔸²-0
      λ{ (xy , xy≢0) (x'y' , x'y'≢0) xy~x'y' → {!!} }

  module From∘To
    where

    open From
    open To

    from-𝔸²-0∘ι₀ : (x : ⟨ k ⟩) → from-𝔸²-0 (ι₀ x) ≡ inl x
    from-𝔸²-0∘ι₀ = {!!}

    from-𝔸²-0∘ι₁ : (x : ⟨ k ⟩) → from-𝔸²-0 (ι₁ x) ≡ inr x
    from-𝔸²-0∘ι₁ = {!!}

    from∘to : (x : ℙ¹-as-pushout) → from (to x) ≡ x
    from∘to =
      Pushout.elimProp
        _
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        from-𝔸²-0∘ι₀
        from-𝔸²-0∘ι₁
```
