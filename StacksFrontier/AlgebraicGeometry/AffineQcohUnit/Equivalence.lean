module

public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Unit

/-!
# Direct image along an affine morphism is an equivalence on quasi-coherent modules

Let `f : X ⟶ S` be an affine morphism of schemes.  This file proves the first assertion of
Stacks Tag 01SB: direct image induces an equivalence from quasi-coherent `𝒪_X`-modules to
quasi-coherent modules over `f_* 𝒪_X`.

Nothing is constructed here.  The functor is
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward`, its quasi-inverse
is `Stacks.AlgebraicGeometry.AffineQcohEquivalence.quasicoherentPullback`, and
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
reduces the assertion to three hypotheses; all three are now available, so this file is the
assembly of the reduction with its three inputs.

* `hL`, that the quasi-inverse preserves quasi-coherence, is
  `Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pullbackModules`;
* `hunit` is `Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent`;
* `hcounit` is
  `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_isQuasicoherent`.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward`:
  **the first assertion of Stacks Tag 01SB.**

## The shape of the statement

The assertion is recorded as the invertibility of the functor induced by direct image, rather
than as an abstract equivalence of the two categories, so that it says which functor realises
it.  Together with
`Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff`, which is the
second assertion of the tag, this completes Tag 01SB.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineQcohUnit

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks Project, Tag 01SB, first assertion.**  For an affine morphism `f : X ⟶ S`, direct
image induces an equivalence from quasi-coherent `𝒪_X`-modules to quasi-coherent modules over
`f_* 𝒪_X`, with quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X`. -/
@[stacks 01SB "the equivalence"]
theorem isEquivalence_affineQuasicoherentPushforward [IsAffineHom f] :
    (affineQuasicoherentPushforward f).IsEquivalence :=
  AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward f
    (RestrictEquivalence.isQuasicoherent_pullbackModules f)
    (isIso_unit_app_of_isQuasicoherent f)
    (PushforwardColimits.isIso_counit_app_of_isQuasicoherent f)

end Stacks.AlgebraicGeometry.AffineQcohUnit

end
