module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RealizationPullbackAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackGradedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraPushforwardIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization

/-!
# The base change of [Stacks, Tag 0897] is the relative spectrum of `𝓑 = f^* B̃`

Let `A` be a commutative ring, `B` a graded `A`-algebra, `f : X ⟶ Spec A` a morphism of
schemes, and `𝓑 = f^* B̃`. This file shows that the base change `X' = Spec(B) ×_{Spec(A)} X` is
isomorphic, as a scheme over `X`, to the relative spectrum `\underline{Spec}_X(𝓑)`, the
identification used in [Stacks, Tag 0897].

## Main definitions

* `Stacks.AffineGradedAlgebra.gradedTildePullbackAlgebraSheaf`: `𝓑 = f^* B̃` read as a sheaf of
  commutative `𝒪_X`-algebras.
* `Stacks.AffineGradedAlgebra.pushforwardAlgebraBaseChangeIsoGradedTildePullback`: the
  pushforward of the structure sheaf of `X'` along `π` is `𝓑`.
* `Stacks.AffineGradedAlgebra.baseChangeIsoRelativeSpecGradedTildePullback`: **`X'` is, over
  `X`, the relative spectrum of `𝓑`.**

## Implementation notes

`Stacks.RelativeSpec.gradedAlgebraSheaf` takes the commutativity of the homogeneous
multiplication as a `Prop`-valued argument, so the two spellings of that proof which occur
here — `Stacks.AffineGradedAlgebra.gradedTildePullback_mul_comm` and the
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm` that
`Stacks.RelativeSpec.RealizationPullback.pullbackRealization` uses — give definitionally equal
algebra sheaves by proof irrelevance, and nothing transports between them.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.AffineGradedAlgebra

variable {X : Scheme.{u}} (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] [DirectSum.Decomposition 𝒜]
  (f : X ⟶ Spec (CommRingCat.of A))

/-- **The graded algebra `𝓑 = f^* B̃` of [Stacks, Tag 0897], read as a sheaf of commutative
`𝒪_X`-algebras.** -/
abbrev gradedTildePullbackAlgebraSheaf : AlgebraSheaf X :=
  Stacks.RelativeSpec.gradedAlgebraSheaf X
    (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
    (gradedTildePullback_mul_comm A 𝒜 f)

/-- **The pushforward of the structure sheaf of `X' = Spec(B) ×_{Spec(A)} X` along the
projection `π : X' ⟶ X` is `𝓑 = f^* B̃`.** -/
def pushforwardAlgebraBaseChangeIsoGradedTildePullback :
    pushforwardAlgebra (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f) ≅
      gradedTildePullbackAlgebraSheaf A 𝒜 f :=
  (algebraPullback_pushforwardAlgebra_iso_of_isPullback
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).symm ≪≫
    (algebraPullback f).mapIso
        (gradedTildeToPushforwardAlgebraIso (R := CommRingCat.of A) 𝒜).symm ≪≫
      Stacks.RelativeSpec.RealizationPullback.realizationPullbackIso f (gradedTildeOf A 𝒜)
        (gradedTilde_mul_comm (R := CommRingCat.of A) 𝒜)

/-- **[Stacks, Tag 01LX] read at `𝓑 = f^* B̃`: the base change
`X' = Spec(B) ×_{Spec(A)} X` is, over `X`, the relative spectrum of `𝓑`.** -/
def baseChangeIsoRelativeSpecGradedTildePullback :
    Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f) ≅
      Over.mk (@relativeSpecToBase X (gradedTildePullbackAlgebraSheaf A 𝒜 f)
        (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f)) :=
  haveI := isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
    ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
  letI : IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  relativeSpecIsoOfAlgebraIso
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)
    (gradedTildePullbackAlgebraSheaf A 𝒜 f)
    (pushforwardAlgebraBaseChangeIsoGradedTildePullback A 𝒜 f)

end Stacks.AffineGradedAlgebra

end
