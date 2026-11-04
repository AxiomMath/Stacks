module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementXi
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow

/-!
# Tag 0A9P for the squares of the interior-preserving refinements

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` over a Noetherian `S`, and let
`g : j ⟶ k` be an interior-preserving morphism of compactifications of `X` over `Y`, with
underlying morphism `G : X̄₁ ⟶ X̄₂` of ambient schemes. The square

```
X --j₁--> X̄₁
|𝟙         |G
X --j₂--> X̄₂
```

is cartesian, `G` is proper and `X̄₂` is Noetherian. So [Stacks, Tag 0A9P] (2), read through the
base change map of [Stacks, Tag 0AA6]
(`Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_isProper`), says that the base
change map `Stacks.Duality.refinementBaseChange` of the square is invertible at every object of
`D^+_QCoh(𝒪_{X̄₂})`. Composed with `ā_k : D^+_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_{X̄₂})`, which lands in
`D^+_QCoh(𝒪_{X̄₂})` by [Stacks, Tag 0A9I]
(`Stacks.Duality.isBoundedBelow_twistedInverseImage_obj`), this is the invertibility of
`Stacks.Duality.refinementBaseChangePlus`, the one input `Stacks.Duality.refinementIso` asks for.

## Main results

* `Stacks.Duality.isIso_refinementBaseChange_app` — the base change map of the square of `g` is
  invertible at every bounded-below object.
* `Stacks.Duality.isIso_refinementBaseChangePlus` — **the instance argument of
  `Stacks.Duality.refinementIso` beyond [Stacks, Tag 0A9K], discharged**, as an instance.

## References

* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
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

/-- **[Stacks, Tag 0A9P] for the square of an interior-preserving refinement**: the base change
map of [Stacks, Tag 0AA6] for the cartesian square of `g` is invertible at every object of
`D_QCoh(𝒪_{X̄₂})` whose cohomology is bounded below. -/
theorem isIso_refinementBaseChange_app (hg : CompactificationOf.PreservesInterior g)
    (M : quasiCoherentDerivedCategory k.space) (hM : DerivedCategoryB.IsBoundedBelow M.obj) :
    IsIso ((refinementBaseChange f g hg).app M) :=
  let := CompactificationOf.isProper_homMap g
  @isIso_twistedInverseImageBaseChangeMap_app_of_isProper.{u}
    X.left j.space X.left k.space
    j.immersion (𝟙 X.left) (CompactificationOf.Hom.map g) k.immersion
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion)
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g))
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
    (CompactificationOf.isPullback_of_preservesInterior g hg).flip
    (isIso_refinementXi f g hg) inferInstance inferInstance inferInstance inferInstance M hM

/-- **The base change map of the square of an interior-preserving refinement is invertible on
`ā_k(D^+_QCoh(𝒪_Y))`.** This is the instance argument of `Stacks.Duality.refinementIso` that
[Stacks, Tag 0A9P] supplies; [Stacks, Tag 0A9I] places the values of `ā_k` on
`D^+_QCoh(𝒪_Y)` in `D^+_QCoh(𝒪_{X̄₂})`. -/
instance isIso_refinementBaseChangePlus (hg : CompactificationOf.PreservesInterior g) :
    IsIso (refinementBaseChangePlus f g hg) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward k.toBase
  exact isIso_refinementBaseChange_app f g hg _
    (isBoundedBelow_twistedInverseImage_obj k.toBase K.obj K.property)

end Stacks.Duality

end
