module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionOpenness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locally quasi-finite part of a morphism of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces which is locally of finite type has a canonical open
subspace `X' ⊆ X`, the locus where the relative dimension of `f` is zero, such that `f` restricted
to `X'` is locally quasi-finite and the relative dimension of `f` at a point outside `|X'|` is at
least `1`.

## Main definitions

* `AlgebraicGeometry.Space.relativeDimensionZeroLocus` is the open subspace `X'`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_etale_comp` and
  `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp` transport a chart condition, resp. the
  relative dimension at a point, along a relatively étale morphism into the source.
* `AlgebraicGeometry.Space.isOpenSubspace_relativeDimensionZeroLocus`: `X'` is an open subspace.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_relativeDimensionZeroLocus`: `f` restricted to
  `X'` is locally quasi-finite.
* `AlgebraicGeometry.Space.one_le_of_hasRelativeDimensionAt_of_notMem_relativeDimensionZeroLocus`:
  the relative dimension of `f` at a point outside `|X'|` is at least `1`.
* `AlgebraicGeometry.Space.range_pointsMap_relativeDimensionZeroLocus` identifies the point set
  of `X'`.

## Implementation notes

The restriction `f|_{X'}` is the composite `X'.ι ≫ f`. The relative dimension at a point is the
predicate `AlgebraicGeometry.Space.HasRelativeDimensionAt` rather than a single element of
`{0, 1, 2, …, ∞}`, so the bound outside `|X'|` says that every value the relative dimension takes
at such a point is at least `1`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A property of scheme morphisms which holds on every étale chart of `f` holds on every
étale chart of `g ≫ f`, for `g` étale after every representable base change. -/
theorem holdsOnEveryEtaleChart_etale_comp {P : MorphismProperty Scheme.{u}} (g : E ⟶ F)
    (f : F ⟶ G)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (g ≫ f) := by
  intro U V a b h ha hb hcomm
  refine hf U V (a ≫ g) b h (MorphismProperty.comp_mem _ a g ha hg) hb ?_
  rw [hcomm, Category.assoc]

/-- For `g` étale after every representable base change, the relative dimension of `g ≫ f` at
`x` is the relative dimension of `f` at the image of `x`. -/
theorem hasRelativeDimensionAt_comp (d : ℕ∞) (g : E ⟶ F) (f : F ⟶ G)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (x : points B S hS E)
    (hd : HasRelativeDimensionAt d B S hS f (pointsMap B S hS E g x)) :
    HasRelativeDimensionAt d B S hS (g ≫ f) x := by
  intro c
  refine hd { c with
    a := c.a ≫ g
    a_etale := MorphismProperty.comp_mem _ c.a g c.a_etale hg
    comm := by rw [c.comm, Category.assoc]
    maps_to := ?_ }
  rw [pointsMap_comp_apply, c.maps_to]

/-- The locus in the source of a morphism of algebraic spaces where its relative dimension is
zero, as a subfunctor of the source. -/
def relativeDimensionZeroLocus (f : F ⟶ G) : Subfunctor F :=
  openSubspaceOfPoints B S hS F {x | HasRelativeDimensionAt 0 B S hS f x}

/-- The set of points where the relative dimension is zero is the set of points where the
relative dimension is at most `0`. -/
private theorem setOf_hasRelativeDimensionAt_zero_eq (f : F ⟶ G) :
    {x : points B S hS F | HasRelativeDimensionAt 0 B S hS f x} =
      {x : points B S hS F |
        ∃ d : ℕ∞, d ≤ ((0 : ℕ) : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} := by
  ext x
  simp only [Set.mem_ofPred_eq, Nat.cast_zero, nonpos_iff_eq_zero]
  exact ⟨fun hx ↦ ⟨0, rfl, hx⟩, fun ⟨d, hd, hx⟩ ↦ hd ▸ hx⟩

/-- For a morphism of algebraic spaces over `S` which is locally of finite type, the locus where
the relative dimension is zero is an open subspace of the source. -/
@[stacks 04NW "the canonical open subspace"]
theorem isOpenSubspace_relativeDimensionZeroLocus (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f) :
    IsOpenSubspace B S hS (relativeDimensionZeroLocus B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hF _ <| by
    rw [setOf_hasRelativeDimensionAt_zero_eq]
    exact isOpen_setOf_hasRelativeDimensionAt_le B S hS hF hG f hf 0

/-- The point set of the relative-dimension-zero locus is the set of points at which the
relative dimension is zero. -/
theorem range_pointsMap_relativeDimensionZeroLocus (f : F ⟶ G) :
    Set.range (pointsMap B S hS (relativeDimensionZeroLocus B S hS f).toFunctor
        (relativeDimensionZeroLocus B S hS f).ι) =
      {x : points B S hS F | HasRelativeDimensionAt 0 B S hS f x} :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- A morphism of algebraic spaces over `S` which is locally of finite type is locally
quasi-finite on the open subspace of its source where its relative dimension is zero. -/
@[stacks 04NW "local quasi-finiteness of the restriction", ega "III 4.4.12" "partial"]
theorem isLocallyQuasiFinite_relativeDimensionZeroLocus (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyQuasiFinite B S hS ((relativeDimensionZeroLocus B S hS f).ι ≫ f) := by
  have hι : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (relativeDimensionZeroLocus B S hS f).ι :=
    presheaf_etale_of_isOpenImmersion B S hS
      (isOpenSubspace_relativeDimensionZeroLocus B S hS hF hG f hf).2
  refine (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _
    (holdsOnEveryEtaleChart_etale_comp B S hS _ f hι hf)).mpr fun x ↦ ?_
  exact hasRelativeDimensionAt_comp B S hS 0 _ f hι x
    ((range_pointsMap_relativeDimensionZeroLocus B S hS f).subset (Set.mem_range_self x))

/-- At a point of the source which is not in the relative-dimension-zero locus, every value of
the relative dimension of the morphism is at least `1`. -/
@[stacks 04NW "relative dimension at least one outside the subspace"]
theorem one_le_of_hasRelativeDimensionAt_of_notMem_relativeDimensionZeroLocus (f : F ⟶ G)
    (x : points B S hS F)
    (hx : x ∉ Set.range (pointsMap B S hS (relativeDimensionZeroLocus B S hS f).toFunctor
      (relativeDimensionZeroLocus B S hS f).ι))
    (d : ℕ∞) (hd : HasRelativeDimensionAt d B S hS f x) : 1 ≤ d := by
  rw [range_pointsMap_relativeDimensionZeroLocus B S hS f] at hx
  exact Order.one_le_iff_ne_zero.mpr fun hzero ↦ hx (hzero ▸ hd)

end AlgebraicGeometry.Space

end
