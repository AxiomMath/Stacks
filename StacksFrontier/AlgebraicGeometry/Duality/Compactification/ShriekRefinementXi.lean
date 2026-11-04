module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementComparison
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionBaseChange

/-!
# Tag 0A9K for the square of an interior-preserving refinement

For an interior-preserving morphism `g : j ⟶ k` of compactifications of `X` over `Y`, with
underlying morphism `G : X̄₁ ⟶ X̄₂` of ambient schemes, the square

```
X --j₁--> X̄₁
|𝟙         |G
X --j₂--> X̄₂
```

is cartesian — [Stacks, Tag 0ATU], in the form
`AlgebraicGeometry.CompactificationOf.isPullback_of_preservesInterior` —
and its base change morphism `j₂` is an open immersion.  So
`Stacks.Duality.OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`
applies, and the transformation `ξ` of [Stacks, Tag 0A9K] attached to the square is invertible.

This is the first of the two inputs the comparison
`Stacks.Duality.compactificationUpperShriekIso` of [Stacks, Tag 0AA0] needs, and it is proved
here rather than carried; the other, [Stacks, Tag 0A9P], is
`Stacks.Duality.isIso_refinementBaseChangePlus` of
`StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementBaseChange`.

## Main results

* `Stacks.Duality.isIso_refinementXi` — **[Stacks, Tag 0A9K] for the square of every
  interior-preserving refinement.**  It is an instance, so the first instance argument of
  `Stacks.Duality.refinementBaseChange` and of `Stacks.Duality.refinementIso` is discharged
  automatically.

## References

* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k : CompactificationOf (Over.mk f.left)} (g : j ⟶ k)

/-- **[Stacks, Tag 0A9K] for the cartesian square of an interior-preserving morphism of
compactifications.**  The base change morphism of that square is the open immersion `j₂` of the
target compactification, so this is
`Stacks.Duality.OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`;
no hypothesis is carried. -/
@[stacks 0A9K "for the cartesian square of an interior-preserving morphism of compactifications \
  of a morphism of AlgebraicGeometry.FTS S over a Noetherian base, whose base change morphism is \
  the open immersion of the target compactification. See \
  Stacks.Duality.OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion \
  for the scope of the registration and for why the general Tor-independent case is not proved. \
  What this discharges is the instance argument IsIso (Stacks.Duality.refinementXi ..) of \
  Stacks.Duality.refinementBaseChange and of Stacks.Duality.refinementIso; the other instance \
  argument, Stacks 0A9P, is Stacks.Duality.isIso_refinementBaseChangePlus"]
instance isIso_refinementXi (hg : CompactificationOf.PreservesInterior g) :
    IsIso (refinementXi f g hg) :=
  letI := CompactificationOf.isProper_homMap g
  @OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion.{u}
    X.left j.space X.left k.space
    j.immersion (𝟙 X.left) (CompactificationOf.Hom.map g) k.immersion
    inferInstance inferInstance
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion)
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g))
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
    (CompactificationOf.isPullback_of_preservesInterior g hg).flip

end Stacks.Duality

end
