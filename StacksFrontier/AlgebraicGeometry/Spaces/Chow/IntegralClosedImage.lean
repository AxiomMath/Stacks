module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The integral closed image of an integral closed subspace

Let `f : X ⟶ Y` be a morphism of good algebraic spaces over the fixed base of the theory of
cycles and let `Z ⊂ X` be an integral closed subspace. There is exactly one integral closed
subspace `Z' ⊂ Y` admitting a morphism `Z ⟶ Z'` over `f`, that is one making the square with
`Z ⟶ X`, `Z' ⟶ Y` and `f` commute, which is dominant; it is the integral closed subspace of
`Y` on the closure of the image of `|Z|`. When `f` is proper that morphism is proper and
surjective.

## Main definitions

* `AlgebraicGeometry.Space.cycleImageSubspace`: the subspace `Z'`, which is
  `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage` at the morphism `f` itself.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.existsUnique_isDominant_hom_of_isGood`:
  **Stacks 0EEG**, both sentences of the source — existence and uniqueness of `Z'` with a
  dominant `Z ⟶ Z'` over `f`, and properness and surjectivity of that morphism when `f` is
  proper.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.subspacePointSet_eq_closure_image_of_isDominant`:
  a target of a dominant morphism from `Z` over `f` has for its point set the closure of the
  image of the point set of `Z`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_hom_closureImage` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage`: the
  morphism to the closure of the image exists and is dominant.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.isProper_of_comp_ι_eq` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.isSurjective_of_comp_ι_eq`: the second
  sentence of the source, for any target of a morphism from `Z` over `f`.

## Implementation notes

The source constructs `Z'` from the generic point `ξ` of `|Z|`, as the integral closed subspace
of `Y` whose generic point is `f(ξ)`. Here `Z'` is instead the integral closed subspace on
`closure (f(|Z|))`, which is
`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage` — the same subspace, because
`|Z|` is the closure of `{ξ}` and so `closure (f(|Z|)) = closure {f(ξ)}`. Taking it this way
needs no generic point and no soberness: nothing below uses Stacks 0EDU or Stacks 0EDV, and
goodness of `Y` enters only through decency, which is what
`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage` asks for. Goodness of `X` enters
only through `X` being an algebraic space.

The morphism `Z ⟶ Z'` is produced by Stacks 03JJ: `Z` is reduced, being integral, and the image
of `|Z|` in `|Y|` lies in `closure (f(|Z|))`, which is the point set of `Z'`. Its dominance and
the uniqueness of `Z'` are both the same computation, that the inclusion of an integral closed
subspace is a closed embedding on points and so commutes with closures: for any target `W` of a
dominant morphism from `Z` over `f`, that computation gives `|W| = closure (f(|Z|))`, and an
integral closed subspace is determined by its point set by Stacks 0ENF.

Properness is Stacks 04NX part (2) applied to `Z ⟶ Z' ⟶ Y`: the composite is `Z ⟶ X ⟶ Y`,
proper by Stacks 04XZ and Stacks 04XY, and `Z' ⟶ Y` is separated by Stacks 04CH. Surjectivity
is then dominance together with closedness of the image, which is universal closedness of the
composite against separatedness of `Z' ⟶ Y`.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 04CH](https://stacks.math.columbia.edu/tag/04CH)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section OverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The point set of the composite of the inclusion of an integral closed subspace with a
morphism is the image of the point set of that subspace. -/
theorem IntegralClosedSubspace.range_pointsMap_ι_comp (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS X) :
    Set.range (pointsMap B S hS Z.subspace.toFunctor (Z.subspace.ι ≫ f)) =
      pointsMap B S hS X f '' subspacePointSet B S hS X Z.subspace := by
  rw [pointsMap_comp, Set.range_comp]

/-- The inclusion of `W` carries the image of a morphism `g : Z ⟶ W` over `f` to the image of
the point set of `Z` under `f`. -/
private theorem image_pointsMap_ι_range_pointsMap (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS X) (W : IntegralClosedSubspace B S hS Y)
    (g : Z.subspace.toFunctor ⟶ W.subspace.toFunctor)
    (hg : g ≫ W.subspace.ι = Z.subspace.ι ≫ f) :
    pointsMap B S hS W.subspace.toFunctor W.subspace.ι ''
      Set.range (pointsMap B S hS Z.subspace.toFunctor g) =
      pointsMap B S hS X f '' subspacePointSet B S hS X Z.subspace := by
  rw [← Set.range_comp, ← pointsMap_comp, hg,
    IntegralClosedSubspace.range_pointsMap_ι_comp B S hS f Z]

/-- An integral closed subspace of `Y` receiving a dominant morphism from `Z` over `f` has for
its point set the closure of the image of the point set of `Z`.

The inclusion of an integral closed subspace is a closed embedding on points, so it carries the
closure of the image of the morphism — all of `|W|`, by dominance — to the closure of the image
of `|Z|`. -/
theorem IntegralClosedSubspace.subspacePointSet_eq_closure_image_of_isDominant
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (Z : IntegralClosedSubspace B S hS X)
    (W : IntegralClosedSubspace B S hS Y) (g : Z.subspace.toFunctor ⟶ W.subspace.toFunctor)
    (hg : g ≫ W.subspace.ι = Z.subspace.ι ≫ f) (hdom : IsDominant B S hS g) :
    subspacePointSet B S hS Y W.subspace =
      closure (pointsMap B S hS X f '' subspacePointSet B S hS X Z.subspace) := by
  have hemb := W.isClosedEmbedding_pointsMap B S hS hY
  rw [← image_pointsMap_ι_range_pointsMap B S hS f Z W g hg, hemb.closure_image_eq,
    hdom.closure_range, Set.image_univ]

/-- **Stacks 0EEG, uniqueness.** An integral closed subspace of `Y` receiving a dominant
morphism from `Z` over `f` is the integral closed subspace on the closure of the image of
`|Z|`: the two have the same point set, and by Stacks 0ENF an integral closed subspace is
determined by its point set. -/
theorem IntegralClosedSubspace.eq_closureImage_of_isDominant (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (Z : IntegralClosedSubspace B S hS X)
    (W : IntegralClosedSubspace B S hS Y) (g : Z.subspace.toFunctor ⟶ W.subspace.toFunctor)
    (hg : g ≫ W.subspace.ι = Z.subspace.ι ≫ f) (hdom : IsDominant B S hS g) :
    W = IntegralClosedSubspace.closureImage B S hS hY hYdec f Z :=
  injective_integralClosedSubspaceSupport B S hS hY
    (IrreducibleCloseds.ext
      ((IntegralClosedSubspace.subspacePointSet_eq_closure_image_of_isDominant B S hS hY f Z W g
          hg hdom).trans
        (IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f Z).symm))

/-- **Stacks 0EEG, the commutative square.** There is a morphism from an integral closed
subspace `Z` of `X` to the integral closed subspace of `Y` on the closure of the image of
`|Z|`, making the square with `Z ⟶ X`, `Z' ⟶ Y` and `f` commute.

By Stacks 03JJ it suffices that `Z` be reduced, which it is because it is integral, and that
the image of `|Z|` in `|Y|` lie in the point set of the target, which is the closure of that
image. -/
theorem IntegralClosedSubspace.exists_hom_closureImage (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (Z : IntegralClosedSubspace B S hS X) :
    ∃ g : Z.subspace.toFunctor ⟶
        (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.toFunctor,
      g ≫ (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.ι =
        Z.subspace.ι ≫ f := by
  refine (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY
    Z.isClosedSubspace.1 (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace
    (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).isClosedSubspace
    Z.isIntegralSpace.1 (Z.subspace.ι ≫ f)).2 ?_
  rw [IntegralClosedSubspace.range_pointsMap_ι_comp B S hS f Z,
    show Set.range (pointsMap B S hS
        (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.ι) =
      closure (pointsMap B S hS X f '' subspacePointSet B S hS X Z.subspace) from
      IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f Z]
  exact subset_closure

/-- **Stacks 0EEG, dominance.** A morphism from an integral closed subspace `Z` of `X` to the
integral closed subspace of `Y` on the closure of the image of `|Z|`, over `f`, is dominant.

Its image spans the point set of the target under closure: the inclusion of the target is a
closed embedding on points, so it carries the closure of that image to the closure of the image
of `|Z|`, which is the whole point set of the target. -/
theorem IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS X)
    (g : Z.subspace.toFunctor ⟶
      (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.toFunctor)
    (hg : g ≫ (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).subspace.ι =
      Z.subspace.ι ≫ f) :
    IsDominant B S hS g := by
  have hemb := (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).isClosedEmbedding_pointsMap
    B S hS hY
  have hdense : closure (Set.range (pointsMap B S hS Z.subspace.toFunctor g)) = Set.univ := by
    refine hemb.injective.image_injective ?_
    rw [← hemb.closure_image_eq,
      image_pointsMap_ι_range_pointsMap B S hS f Z _ g hg, Set.image_univ]
    exact (IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f Z).symm
  exact dense_iff_closure_eq.mpr hdense

/-- The composite of the inclusion of an integral closed subspace of `X` with a proper
`f : X ⟶ Y` is proper. -/
private theorem isProper_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (Z : IntegralClosedSubspace B S hS X) : IsProper B S hS (Z.subspace.ι ≫ f) :=
  isProper_comp B S hS Z.isClosedSubspace.1 hX hY Z.subspace.ι f
    (isProper_of_isClosedImmersion B S hS Z.isClosedSubspace.1 hX Z.subspace.ι
      Z.isClosedSubspace.2) hf

/-- **Stacks 0EEG, properness.** If `f : X ⟶ Y` is proper, then a morphism from an integral
closed subspace `Z` of `X` to an integral closed subspace `W` of `Y` over `f` is proper.

The composite `Z ⟶ W ⟶ Y` is `Z ⟶ X ⟶ Y`, which is proper by Stacks 04XZ and Stacks 04XY, and
`W ⟶ Y` is separated by Stacks 04CH; properness cancels by Stacks 04NX part (2). -/
theorem IntegralClosedSubspace.isProper_of_comp_ι_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (Z : IntegralClosedSubspace B S hS X) (W : IntegralClosedSubspace B S hS Y)
    (g : Z.subspace.toFunctor ⟶ W.subspace.toFunctor)
    (hg : g ≫ W.subspace.ι = Z.subspace.ι ≫ f) :
    IsProper B S hS g := by
  refine isProper_of_comp_of_isSeparated B S hS Z.isClosedSubspace.1 W.isClosedSubspace.1 hY g
    W.subspace.ι ?_
    (isSeparated_of_isClosedImmersion B S hS W.subspace.ι W.isClosedSubspace.2)
  rw [hg]
  exact isProper_ι_comp B S hS hX hY f hf Z

/-- **Stacks 0EEG, surjectivity.** If `f : X ⟶ Y` is proper, then a dominant morphism from an
integral closed subspace `Z` of `X` to an integral closed subspace `W` of `Y` over `f` is
surjective.

Its image is dense by dominance, and closed because the composite `Z ⟶ W ⟶ Y` is universally
closed and `W ⟶ Y` is separated. -/
theorem IntegralClosedSubspace.isSurjective_of_comp_ι_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (Z : IntegralClosedSubspace B S hS X) (W : IntegralClosedSubspace B S hS Y)
    (g : Z.subspace.toFunctor ⟶ W.subspace.toFunctor)
    (hg : g ≫ W.subspace.ι = Z.subspace.ι ≫ f) (hdom : IsDominant B S hS g) :
    IsSurjective B S hS g := by
  have huniv : UniversallyClosed B S hS (g ≫ W.subspace.ι) := by
    rw [hg]
    exact (isProper_ι_comp B S hS hX hY f hf Z).2.2
  have hclosed := isClosed_range_of_comp_of_isSeparated B S hS Z.isClosedSubspace.1
    W.isClosedSubspace.1 hY g W.subspace.ι huniv
    (isSeparated_of_isClosedImmersion B S hS W.subspace.ι W.isClosedSubspace.2)
  refine Set.range_eq_univ.mp ?_
  rw [← hclosed.closure_eq]
  exact hdom.closure_range

end OverBase

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EEG.** In Situation 0EDT, let `X` and `Y` be good algebraic spaces over the base
and let `f : X ⟶ Y` be a morphism over the base. For an integral closed subspace `Z ⊂ X` there
is exactly one integral closed subspace `Z' ⊂ Y` admitting a morphism `Z ⟶ Z'` over `f` — that
is, one making the square with `Z ⟶ X`, `Z' ⟶ Y` and `f` commute — which is dominant; and if
`f` is proper, then every such morphism is proper and surjective. Every morphism making that
square commute is a morphism over the base, so the whole diagram is one over the base.

The subspace is `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage` at `f`, the
integral closed subspace of `Y` on the closure of the image of `|Z|`. -/
@[stacks 0EEG]
theorem IntegralClosedSubspace.existsUnique_isDominant_hom_of_isGood (pX : X ⟶ D.space)
    (pY : Y ⟶ D.space) (hX : D.IsGood pX) (hY : D.IsGood pY) (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∃! Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        ∃ g : Z.subspace.toFunctor ⟶ Z'.subspace.toFunctor,
          g ≫ Z'.subspace.ι = Z.subspace.ι ≫ f ∧
            IsDominant D.site D.base D.base_mem g) ∧
      (∀ (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
          (g : Z.subspace.toFunctor ⟶ Z'.subspace.toFunctor),
          g ≫ Z'.subspace.ι = Z.subspace.ι ≫ f →
            g ≫ Z'.subspace.ι ≫ pY = Z.subspace.ι ≫ pX) ∧
      (IsProper D.site D.base D.base_mem f →
        ∀ (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
          (g : Z.subspace.toFunctor ⟶ Z'.subspace.toFunctor),
          g ≫ Z'.subspace.ι = Z.subspace.ι ≫ f → IsDominant D.site D.base D.base_mem g →
            IsProper D.site D.base D.base_mem g ∧
              IsSurjective D.site D.base D.base_mem g) := by
  have hYdec : IsDecentSpace D.site D.base D.base_mem Y := D.isDecentSpace_of_isGood pY hY
  obtain ⟨g, hg⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem
    hY.1 hYdec f Z
  refine ⟨⟨IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z,
    ⟨g, hg, IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base D.base_mem
      hY.1 hYdec f Z g hg⟩, ?_⟩, ?_, ?_⟩
  · rintro W ⟨h, hh, hhdom⟩
    exact IntegralClosedSubspace.eq_closureImage_of_isDominant D.site D.base D.base_mem hY.1
      hYdec f Z W h hh hhdom
  · intro W h hh
    rw [← Category.assoc, hh, Category.assoc, hf]
  · intro hfproper W h hh hhdom
    exact ⟨IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 f
        hfproper Z W h hh,
      IntegralClosedSubspace.isSurjective_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 f
        hfproper Z W h hh hhdom⟩

/-- **The subspace `Z'` of Stacks 0EEG.** The integral closed image of an integral closed
subspace `Z ⊂ X` along a morphism `f : X ⟶ Y` of good algebraic spaces over the base: the
integral closed subspace of `Y` on the closure of the image of `|Z|`. -/
noncomputable abbrev cycleImageSubspace (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem Y :=
  IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) f Z

end Situation

end AlgebraicGeometry.Space

end
