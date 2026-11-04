module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicate
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.RefinementSquare
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesData
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper

/-!
# The upper shriek functor of a compactification, with every hypothesis discharged

`Stacks.Duality.upperShriek` ([Stacks, Tag 0A9Y]) is `f^! = j^* ∘ ā` for a compactification `j` of
`X` over `Y`, and it takes as arguments the two quasi-coherence facts of [Stacks, Tag 08D5] part
(1) and [Stacks, Tag 08DW] part (1) together with the adjointness instance of
[Stacks, Tag 0A9E].  Over a Noetherian base all three are available in this repository:

* [Stacks, Tag 08DW] part (1) is unconditional, as
  `Stacks.Duality.isQuasicoherent_homology_derivedPullback'`;
* [Stacks, Tag 08D5] part (1) and [Stacks, Tag 0A9E] hold for a quasi-compact quasi-separated
  morphism with quasi-compact target, as
  `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` and
  `AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, and the structure
  morphism `j.toBase` of a compactification is proper, hence quasi-compact and quasi-separated,
  with quasi-compact target because an object of `AlgebraicGeometry.FTS S` is quasi-compact over
  a quasi-compact `S`.

So `Stacks.Duality.compactificationUpperShriek` below is `f^!` as a function of the
compactification alone, which is what the independence statement of [Stacks, Tag 0AA0] is
about.  As in the source, it is read on `D⁺_QCoh(𝒪_Y)`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `compactificationTwistedPlus` — `ā` of a compactification on `D⁺_QCoh(𝒪_Y)`.
* `compactificationUpperShriek` — `f^! = j^* ∘ ā` of a compactification on `D⁺_QCoh(𝒪_Y)`, with
  all arguments discharged.

## Main results

* `AlgebraicGeometry.CompactificationOf.isNoetherian_space`,
  `AlgebraicGeometry.CompactificationOf.quasiCompact_immersion_unconditional` — over a Noetherian
  base the ambient scheme of a compactification is Noetherian and its open immersion is
  quasi-compact.
* `Stacks.Duality.compactificationUpperShriek_eq_upperShriek` — the identification with
  `Stacks.Duality.upperShriek`, so that the results proved there (exactness, the value on an
  object) apply.

## Implementation notes

*Why the base is Noetherian.* [Stacks, Tag 0F42], the situation in which [Stacks, Tag 0AA0] is
stated, has a Noetherian base `S`; this is what makes the ambient scheme of a compactification
Noetherian and so its open immersion quasi-compact, which is needed for [Stacks, Tag 08D5] along
the open immersion.  Quasi-compactness of `S` alone would suffice for the definition below.

*Why the domain is `D⁺_QCoh(𝒪_Y)`.*  [Stacks, Tag 0AA0] states `f^!` as a functor
`D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`, and the bounded-below restriction of the domain is not
cosmetic: it is exactly what makes the comparison of two compactifications an instance of
[Stacks, Tag 0A9P], whose conclusion is about the bounded-below part only.  See the module
documentation of
`StacksFrontier/AlgebraicGeometry/Duality/Compactification/ShriekIndependence.lean`.  The codomain
is left as `D_QCoh(𝒪_X)`: that the values are again bounded below is [Stacks, Tag 0A9I], which
this repository proves — as `Stacks.Duality.isBoundedBelow_rightAdjoint_obj` — only at
`CategoryTheory.HasDerivedCategory.standard`, while `ā` exists only at the locally small model
used here.  Nothing is lost, the inclusion of `D⁺_QCoh(𝒪_X)` being fully faithful.

*Proof irrelevance.* The quasi-coherence arguments of `Stacks.Duality.upperShriek` and the
adjointness instance are all `Prop`-valued, so the functor does not depend on which proof is
supplied; two spellings of the same morphism therefore give definitionally equal functors.  This
is why no compatibility lemma between different choices of the arguments is needed below.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {X : Over S}

/-- The ambient scheme of a compactification of a scheme over a locally Noetherian base is
locally Noetherian: it is proper, hence locally of finite type, over the base. -/
instance isLocallyNoetherian_space [IsLocallyNoetherian S] (j : CompactificationOf X) :
    IsLocallyNoetherian j.space :=
  LocallyOfFiniteType.isLocallyNoetherian j.toBase

/-- The interior of a compactification over a Noetherian base is a Noetherian space: it is an
open subspace of the ambient scheme, which is Noetherian. -/
theorem noetherianSpace_interior [IsNoetherian S] (j : CompactificationOf X) :
    TopologicalSpace.NoetherianSpace X.left :=
  j.immersion.isOpenEmbedding.isInducing.noetherianSpace

/-- **The open immersion of a compactification over a Noetherian base is quasi-compact.**  The
`AlgebraicGeometry.CompactificationOf` structure does not carry this, but over a Noetherian base
the ambient scheme is a Noetherian space and every morphism into it is quasi-compact. -/
instance quasiCompact_immersion_unconditional [IsNoetherian S] (j : CompactificationOf X) :
    QuasiCompact j.immersion :=
  have := j.noetherianSpace_interior
  inferInstance

end AlgebraicGeometry.CompactificationOf


namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- **The twisted inverse image `ā = (j.toBase)^×` of the structure morphism of a
compactification**, with the argument of [Stacks, Tag 08D5] part (1) and the adjointness instance
of [Stacks, Tag 0A9E] discharged: `j.toBase` is proper, hence quasi-compact and quasi-separated,
and the base is quasi-compact. -/
def compactificationTwisted (j : CompactificationOf (Over.mk f.left)) :
    quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory j.space :=
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j.toBase
  twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)

/-- **Restriction `j^* = Lj^*` along the open immersion of a compactification**, with the
argument of [Stacks, Tag 08DW] part (1) discharged — that one is unconditional. -/
abbrev compactificationRestrict (j : CompactificationOf (Over.mk f.left)) :
    quasiCoherentDerivedCategory j.space ⥤ quasiCoherentDerivedCategory X.left :=
  quasiCoherentDerivedPullback j.immersion
    (isQuasicoherent_homology_derivedPullback' j.immersion)

/-- **`ā` of a compactification, read on `D⁺_QCoh(𝒪_Y)`.**  [Stacks, Tag 0AA0] takes `f^!` to be
a functor out of `D⁺_QCoh(𝒪_Y)`, and this is the first of its two factors there: the twisted
inverse image of the structure morphism precomposed with the inclusion of the bounded-below
part. -/
abbrev compactificationTwistedPlus (j : CompactificationOf (Over.mk f.left)) :
    quasiCoherentDerivedCategoryPlusAtModel Y.left ⥤ quasiCoherentDerivedCategory j.space :=
  ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙ compactificationTwisted f j

/-- **The upper shriek functor `f^!` of a compactification, with no arguments left to supply.**
This is `Stacks.Duality.upperShriek` of [Stacks, Tag 0A9Y] with the quasi-coherence hypotheses of
[Stacks, Tag 08D5] part (1) and [Stacks, Tag 08DW] part (1) and the adjointness instance of
[Stacks, Tag 0A9E] discharged, which is possible because the structure morphism `j.toBase` of a
compactification is proper and the base is Noetherian.

It is `j^* ∘ ā`, the restriction along the open immersion `j.immersion : X ⟶ X̄` of the twisted
inverse image of the proper morphism `j.toBase : X̄ ⟶ Y`, **read on `D⁺_QCoh(𝒪_Y)`** — which is
where the source puts it.  [Stacks, Tag 0AA0] is the statement that it is independent of `j` up
to canonical isomorphism, and the bounded-below restriction is what puts the comparison of two
compactifications inside [Stacks, Tag 0A9P]; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/Compactification/ShriekIndependence.lean`. -/
def compactificationUpperShriek (j : CompactificationOf (Over.mk f.left)) :
    quasiCoherentDerivedCategoryPlusAtModel Y.left ⥤ quasiCoherentDerivedCategory X.left :=
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j.toBase
  ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
    upperShriek f j

/-- `Stacks.Duality.compactificationUpperShriek` is `Stacks.Duality.upperShriek` restricted
along the inclusion of `D⁺_QCoh(𝒪_Y)`, so everything proved about the latter — that it is an
exact functor of triangulated categories, and its value on an object — applies to it. -/
theorem compactificationUpperShriek_eq_upperShriek (j : CompactificationOf (Over.mk f.left)) :
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j.toBase
    compactificationUpperShriek f j =
      ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
        upperShriek f j :=
  rfl

/-- `f^!` of a compactification is `ā` followed by restriction to the interior. -/
theorem compactificationUpperShriek_eq_comp (j : CompactificationOf (Over.mk f.left)) :
    compactificationUpperShriek f j =
      compactificationTwistedPlus f j ⋙ compactificationRestrict f j :=
  rfl

end Stacks.Duality

end
