module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence

/-!
# The membership conclusion of Stacks 06N2, read on the algebraic space

**Stacks 06N2** and **Stacks 06MD** both conclude with a point-set clause of the shape "the open
subspace `V ⊆ U` contains `p(z)`", and the two are formalized at *different levels*.
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale` of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingOpenSubspace.lean` reads it at the level of
**stacks**: `z` is a point of the algebraic stack `F = U ×_𝒳 Spec k`, the projection acts on
points by `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap` of
`AlgebraicGeometry.Stack.fibreProjection`, and the subspace contributes the *image* of its point
set under `AlgebraicGeometry.Stack.spacePointMap`. Whereas
`Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`,
the `@[stacks 06MD]` declaration, reads it at the level of **algebraic spaces**: the point is a point of
an algebraic space `Fsp` representing `F`, the projection is
`AlgebraicGeometry.Stack.fibreSpaceProjection`, and membership is in
`Set.range (AlgebraicGeometry.Space.pointsMap V.ι)` with no image taken.

This file carries the Stacks 06N2 clause down to the second form, so that the chart construction
of **Stacks 06N3** — which consumes the two clauses interchangeably — can take either leg.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_fibreProjection_spacePointMap`: the comparison of the two
  readings of the projection `p : F ⟶ U` on points. The point of `|U|` that
  `AlgebraicGeometry.Stack.fibreSpaceProjection` sends a point `x` of `|Fsp|` to is, under the
  identification of `|U|` with `|S_U|`, the point that
  `AlgebraicGeometry.Stack.fibreProjection` sends the point of `|F|` named by `x` to.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι`: **Stacks 06N2**
  with the point-set clause in the form Stacks 06MD states it.

## How it is proved

The comparison is `AlgebraicGeometry.Stack.spacePointMap_representing_naturality` — the naturality
of the canonical map on points in the chart, read at the representing charts of the two stacks
involved — instantiated at the representing equivalence `eF` of the fibre and at the *tautological*
representation `StacksRepresentableCFG.EquivalenceOver.refl` of the algebraic space `U`, which is
precisely the pair of representations `AlgebraicGeometry.Stack.fibreSpaceProjection` is defined
with. No massaging is needed: at `EquivalenceOver.refl` the chart of the representing equivalence
is the identity based functor on the nose, and the fibred-in-groupoids witnesses that
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap` chooses with `Classical.choose` occur only in
proof positions of `AlgebraicGeometry.Stack.pointsMap`, so both differences are definitional.

Given the comparison, the image of the range collapses: the tautological chart of `U` is injective
on points (`AlgebraicGeometry.Stack.spacePointMap_id_bijective`), so a point of `|U|` whose image
lies in the image of a set lies in that set. That is the only use the bijectivity of the chart is
put to here — surjectivity is not needed, because the statement is made at an arbitrary point `x`
of `|Fsp|` rather than at a point of `|F|`.

## Implementation notes

The statement is made at a variable point `x` of `|Fsp|` and a variable algebraic space `Fsp`
representing the fibre, with the unramifiedness hypothesis read at the point of `|F|` that `x`
names. That is the shape in which it composes on both sides:
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt` delivers the hypothesis at exactly
that spelling, and taking `x` to be the underlying point `z.image` of a geometric point `z` of
`Fsp` gives back, on the nose, the point-set conjunct of Stacks 06MD.

No `@[stacks]` attribute is claimed. The Stacks 06N2 registration sits on
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`, which states the source's own conclusion;
nothing here is a step of Stacks 06N2 itself, only a reading of its conclusion. Nor is any part of
**Stacks 06N3** claimed, though both ingredients of its chart construction are available. The
identification of the fibre of the Stacks 06MD
slice is
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList` of
`StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceChartZeroScheme`, read at the chart by
`StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceUnramifiedFieldPoint` and carried to the fibre
hypothesis of Stacks 06N2 by
`StacksFrontier.AlgebraicGeometry.Stacks.SliceFibreSubspaceComparison`; and the assembly is complete,
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional` of
`StacksFrontier.AlgebraicGeometry.Stacks.AbsolutelyDMEtaleChartAssembly` stating Stacks 06N3 with no
hypothesis at all.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-- **The two readings of the projection `p : F ⟶ U` agree on points.** Let `Fsp` be an algebraic
space representing the fibre `F = U ×_𝒳 Spec k` and let `x` be a point of `|Fsp|`. The point of
`|F|` that `x` names, pushed to `|S_U|` by the 1-morphism `p : F ⟶ U` of the source's cartesian
diagram, is the image under the identification of `|U|` with `|S_U|` of the point of `|U|` that
the morphism of algebraic spaces `AlgebraicGeometry.Stack.fibreSpaceProjection` of **Stacks 04SW**
sends `x` to.

This is `AlgebraicGeometry.Stack.spacePointMap_representing_naturality` at the two representations
`fibreSpaceProjection` is defined with: `eF` on the source and the tautological
`StacksRepresentableCFG.EquivalenceOver.refl` on the target, whose chart is the identity based
functor. -/
theorem pointsMap_fibreProjection_spacePointMap (x : Space.points B S hS Fsp) :
    AlgebraicStacks.pointsMap B S hS (fibreProjection B S hS 𝒳 U hU k hk toBase f g)
        (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
          (representingEquivalence B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor x) =
      spacePointMap B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val
        (BasedFunctor.id (fibredCategory B S hS U).val)
        (Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) x) :=
  (spacePointMap_representing_naturality B S hS Fsp U
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
    (algebraicSpaceStack.{u, w} B S hS U hU).val eF
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (fibreProjection B S hS 𝒳 U hU k hk toBase f g).hom x).symm

/-- **Stacks 06N2, with the point-set clause read on the algebraic space.** Let `𝒳` be an
algebraic stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳` which is flat and
locally of finite presentation, let `Spec k ⟶ 𝒳` be a field-valued point, let `Fsp` be an
algebraic space representing the fibre `F = U ×_𝒳 Spec k` and let `p : Fsp ⟶ U` be the projection
read on it. If `F ⟶ Spec k` is unramified near the point of `|F|` named by `x ∈ |Fsp|`, then there
is an open subspace `V ⊆ U`, in the sense of **Stacks 02YU**, part (2), with

* `p(x) ∈ |V|`, as membership of `p(x)` in the **point set of `V` itself**, and
* the composite of the 1-morphism of **Stacks 0458** induced by `V` with `f` étale.

Nothing is added to `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`: the subspace, its
openness and the étaleness are the ones Stacks 06N2 returns, and only the point-set clause is
moved. That clause is stated there as membership in the *image* of `|V|` under the identification
of `|U|` with `|S_U|`, of the point of `|S_U|` that `AlgebraicGeometry.Stack.fibreProjection`
produces; here it is the point set of `V` itself, and the point of `|U|` is the one
`AlgebraicGeometry.Stack.fibreSpaceProjection` produces. The two are matched by
`AlgebraicGeometry.Stack.pointsMap_fibreProjection_spacePointMap` and the injectivity of the
tautological chart, `AlgebraicGeometry.Stack.spacePointMap_id_bijective`.

This is the form in which
`Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`,
the library's **Stacks 06MD**, already states its own point-set clause: taking `x` to be the
underlying point `z.image` of a geometric point `z` of `Fsp` returns that conjunct verbatim. -/
theorem exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (x : Space.points B S hS Fsp)
    (hx : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor x)) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) x ∈
        Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
      IsEtale B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) := by
  obtain ⟨V, hV, hmem, het⟩ := exists_isOpenSubspace_isEtale.{u, w} B S hS 𝒳 U hU k hk toBase
    f g hflat hfp _ hx
  refine ⟨V, hV, ?_, het⟩
  exact (spacePointMap_id_bijective B S hS U).injective.mem_set_image.1
    (pointsMap_fibreProjection_spacePointMap B S hS 𝒳 U hU k hk toBase f g Fsp eF x ▸ hmem)

end AlgebraicGeometry.Stack

end
