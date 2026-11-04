module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack

/-!
# The base change of a full-subcategory inclusion along a scheme-valued point is an open subspace

Let `𝒳` be an algebraic stack over `S` and let `Ω` be an **open** set of points of `|𝒳|`
(**Stacks 04XL**). The property `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` of the objects of `𝒳`
is inherited along morphisms, so it cuts out a subfunctor
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of `yoneda V` at every
scheme-valued point `z` of `𝒳` with values in `V`. This file proves that that subfunctor is an
**open subspace** of `V` in the sense of **Stacks 02YU**, part (2).

## Main definitions

* `AlgebraicGeometry.Stack.pointChart`: a scheme-valued point of `𝒳` with values in `V`, read as
  a 1-morphism to `𝒳` from the category of elements of `yoneda V`.
* `AlgebraicGeometry.Stack.pointChartSchemePointSet`: the set of points of the scheme `V` whose
  image in `|𝒳|` lies in `Ω`.

## Main results

* `AlgebraicGeometry.Stack.pointsWithin_iff_range_subset_pointChartSchemePointSet`: an object
  `z T` of `𝒳` lies in the locus of `Ω` exactly when the image of `T` in `V` lies in the set of
  points of `V` going into `Ω`.
* `AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor_eq_openSubspaceOfPoints`: the
  subfunctor is the subspace of **Stacks 03BZ** cut out by a set of points.
* `AlgebraicGeometry.Stack.isOpenSubspace_fullSubcategoryBaseChangeSubfunctor`: **the main
  result**, for a property of the objects of `𝒳` cut out by an open set of points.
* `AlgebraicGeometry.Stack.isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_pointsWithin`: the
  main result at `AlgebraicGeometry.Stack.pointsWithin` itself, where no hypothesis beyond
  openness of `Ω` is carried.
* `Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin`:
  the inclusion of the full subcategory cut out by an open set of points is representable by
  algebraic spaces (**Stacks 02ZW**), the algebraicity input of
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion` being
  discharged by the main result.
* `AlgebraicGeometry.Stack.isAlgebraicStack_fullSubcategoryBased_pointsWithin`: the full
  subcategory cut out by an open set of points is an algebraic stack, by **Stacks 05UM**.

## Implementation notes

A scheme-valued point `z` of `𝒳` with values in `V` is read as a 1-morphism to `𝒳` from the
category of elements of the algebraic space `yoneda V`, `AlgebraicGeometry.Stack.pointChart`,
assembled from `AlgebraicGeometry.Stack.elementsToSlice`, `AlgebraicGeometry.Stack.sliceToSite`
and `z` itself. Its value at the tautological section over an object `T` of the site of `V` is
`z T` *definitionally*.

The hypothesis carried by the main result is that the property is the locus of an *open* set of
points of `|𝒳|`. That is the invariance condition the construction needs, and it is the form a
consumer has it in: an invariant open subspace of a smooth chart has open image in `|𝒳|`, because
a smooth chart is open on points by **Stacks 04XL**, and invariance is exactly what makes the
locus of that image pull back to the subspace one started from. No quotient stack, no groupoid
and no change of universe occurs.

`CategoryTheory.Over.iteratedSliceForward_comp_map` is the one place where a comparison of
structure functors is *not* definitional: the two values at an object `α` of `(C/X)/V` are
`Over.mk (α.hom.left ≫ V.hom)` and `α.left`, and they agree only through
`CategoryTheory.Over.w`. Mathlib has the reverse composite
`CategoryTheory.Over.iteratedSliceBackward_forget` as a `rfl`, which is why the chart is built in
this direction and `z` is used as given rather than reconstructed from a 1-morphism out of the
slice.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A condition on the points of a represented presheaf, read on the representing scheme.** The
image of the points of `yoneda A` along a morphism `s : A ⟶ W` of the site lies in a set `P` of
points of `yoneda W` exactly when the image of the underlying scheme morphism lies in the image of
`P` on the underlying scheme. -/
theorem range_pointsMap_yoneda_subset_iff {A W : BigFppfOver B S hS} (s : A ⟶ W)
    (P : Set (points B S hS (yoneda.obj W))) :
    Set.range (pointsMap B S hS (yoneda.obj A) (yoneda.map s)) ⊆ P ↔
      Set.range ((BigFppfOver.toScheme B S hS).map s) ⊆
        pointsToScheme B S hS W '' P := by
  constructor
  · rintro h y ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS A x
    refine ⟨pointsMap B S hS (yoneda.obj A) (yoneda.map s) w, h ⟨w, rfl⟩, ?_⟩
    rw [pointsToScheme_pointsMap_yoneda, hw]
  · rintro h y ⟨w, rfl⟩
    obtain ⟨p, hp, hpeq⟩ := h ⟨pointsToScheme B S hS A w, rfl⟩
    have hw : pointsToScheme B S hS W
        (pointsMap B S hS (yoneda.obj A) (yoneda.map s) w) =
        pointsToScheme B S hS W p := by
      rw [pointsToScheme_pointsMap_yoneda, hpeq]
    rw [injective_pointsToScheme B S hS W hw]
    exact hp

/-- A morphism `s : A ⟶ W` of the site lies in the subspace of `yoneda W` cut out by a set `P` of
points exactly when its image on the underlying schemes lies in the image of `P`. -/
private theorem mem_openSubspaceOfPoints_yoneda_iff {A W : BigFppfOver B S hS} (s : A ⟶ W)
    (P : Set (points B S hS (yoneda.obj W))) :
    s ∈ (openSubspaceOfPoints B S hS (yoneda.obj W) P).obj (Opposite.op A) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map s) ⊆ pointsToScheme B S hS W '' P :=
  range_pointsMap_yoneda_subset_iff B S hS s P

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading a scheme-valued point as a chart by an algebraic space -/

/-- **The category of elements of `yoneda V` is the slice of the big fppf site of `S` over `V`.**
An object of the category of elements is an object `A` of the site together with a morphism
`A ⟶ V`, which is an object of the slice; the structure functors agree on the nose, since both
send it to `A`. -/
def elementsToSlice (V : BigFppfOver B S hS) :
    (fibredCategory B S hS (yoneda.obj V)).val ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget V) where
  toFunctor :=
    { obj X := Over.mk X.fiber.as
      map {_ _} u := Over.homMk u.base (Discrete.eq_of_hom u.fiber).symm
      map_id _ := by apply Over.OverMorphism.ext; rfl
      map_comp _ _ := by apply Over.OverMorphism.ext; rfl }
  w := rfl

/-- **The slice of the big fppf site of `S` over `V` is the big fppf site of `V`.** The
comparison is Mathlib's iterated-slice functor, and it commutes with the structure functors by
`CategoryTheory.Over.iteratedSliceForward_comp_map`. -/
def sliceToSite (V : BigFppfOver B S hS) :
    BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
      BasedCategory.ofFunctor (Over.map V.hom) where
  toFunctor := Over.iteratedSliceForward V
  w := CategoryTheory.Over.iteratedSliceForward_comp_map V

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {V : BigFppfOver B S hS}
  (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
  (hz : z ⋙ 𝒳.val.val.p = Over.map V.hom)

/-- **A scheme-valued point of `𝒳` with values in `V`, read as a chart by the algebraic space
`yoneda V`.** The 1-morphism to `𝒳` from the category of elements of `yoneda V` obtained by
composing the two comparisons above with `z` itself, which is a 1-morphism out of the big fppf
site of `V` by its own defining equation.

Its value at the tautological section over an object `T` of the site of `V` is `z T`
definitionally, which is
`AlgebraicGeometry.Stack.pointChart_obj_tautological`. -/
def pointChart : (fibredCategory B S hS (yoneda.obj V)).val ⥤ᵇ 𝒳.val.val :=
  (elementsToSlice B S hS V).comp
    ((sliceToSite B S hS V).comp
      ({ toFunctor := z, w := hz } : BasedCategory.ofFunctor (Over.map V.hom) ⥤ᵇ 𝒳.val.val))

/-- The chart attached to a scheme-valued point takes the tautological section of `yoneda V` over
an object `T` of the big fppf site of `V` to the value of the point at `T`. -/
theorem pointChart_obj_tautological (T : BigFppfOver B V.left.1 V.left.2) :
    (pointChart B S hS 𝒳 z hz).toFunctor.obj
        ⟨(Over.map V.hom).obj T, Discrete.mk (Over.homMk T.hom)⟩ = z.obj T :=
  rfl

/-! ### The set of points cut out on the scheme -/

variable (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))

/-- The set of points of the scheme underlying `V` whose image in `|𝒳|` along a scheme-valued
point `z` lies in `Ω`. -/
noncomputable def pointChartSchemePointSet :
    Set ((BigFppfOver.toScheme B S hS).obj V) :=
  Space.pointsToScheme B S hS V ''
    (spacePointMap B S hS (yoneda.obj V) 𝒳.val (pointChart B S hS 𝒳 z hz) ⁻¹' Ω)

include hz in
/-- **The set of points cut out on the scheme underlying `V` is open** when `Ω` is open: the
canonical map on points of a chart is continuous by **Stacks 04XL**, and the comparison with the
points of the representing scheme is a homeomorphism by clause (1) of **Stacks 03BX**. -/
theorem isOpen_pointChartSchemePointSet
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    IsOpen (pointChartSchemePointSet B S hS 𝒳 z hz Ω) := by
  let := Space.pointTopology B S hS (yoneda.obj V)
  exact (Space.schemePointsHomeomorph B S hS V).isOpenMap _
    (isOpen_spacePointMap_preimage B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V) Ω (pointChart B S hS 𝒳 z hz) hΩ)

include hz in
/-- **The locus of `Ω` at a scheme-valued point, read on the underlying schemes.** The object
`z T` of `𝒳` lies in `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` exactly when the image of the
scheme underlying `T` in the scheme underlying `V` lies in
`AlgebraicGeometry.Stack.pointChartSchemePointSet`. -/
theorem pointsWithin_iff_range_subset_pointChartSchemePointSet
    (T : BigFppfOver B V.left.1 V.left.2) :
    pointsWithin 𝒳 Ω (z.obj T) ↔
      Set.range (B.inclusion.map T.hom) ⊆ pointChartSchemePointSet B S hS 𝒳 z hz Ω := by
  have hmem := mem_openSubspaceOfPoints_spacePointMap_preimage_iff B S hS (yoneda.obj V) Ω
    (pointChart B S hS 𝒳 z hz)
    (A := (Over.map V.hom).obj T) (Over.homMk T.hom)
  rw [Space.mem_openSubspaceOfPoints_yoneda_iff] at hmem
  exact hmem.symm

/-! ### The subfunctor is an open subspace -/

/-- The set of points of `V`, read inside the big fppf site of `V`, whose image in `|𝒳|` lies in
`Ω`: the inverse image of `AlgebraicGeometry.Stack.pointChartSchemePointSet` along the comparison
of clause (1) of **Stacks 03BX**. -/
noncomputable def pointChartPointSet :
    Set (Space.points B V.left.1 V.left.2
      (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
  Space.pointsToScheme B V.left.1 V.left.2 (Over.mk (𝟙 V.left)) ⁻¹'
    pointChartSchemePointSet B S hS 𝒳 z hz Ω

include hz in
/-- The image of `AlgebraicGeometry.Stack.pointChartPointSet` on the representing scheme is
`AlgebraicGeometry.Stack.pointChartSchemePointSet`: the comparison of clause (1) of
**Stacks 03BX** is surjective. -/
theorem image_pointsToScheme_pointChartPointSet :
    Space.pointsToScheme B V.left.1 V.left.2 (Over.mk (𝟙 V.left)) ''
        pointChartPointSet B S hS 𝒳 z hz Ω =
      pointChartSchemePointSet B S hS 𝒳 z hz Ω :=
  Set.image_preimage_eq _
    (Space.surjective_pointsToScheme B V.left.1 V.left.2 (Over.mk (𝟙 V.left)))

include hz in
/-- **`AlgebraicGeometry.Stack.pointChartPointSet` is open** when `Ω` is. -/
theorem isOpen_pointChartPointSet
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    @IsOpen _ (Space.pointTopology B V.left.1 V.left.2 _)
      (pointChartPointSet B S hS 𝒳 z hz Ω) := by
  let := Space.pointTopology B V.left.1 V.left.2
    (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
  exact (Space.schemePointsHomeomorph B V.left.1 V.left.2 (Over.mk (𝟙 V.left))).continuous
    |>.isOpen_preimage _ (isOpen_pointChartSchemePointSet B S hS 𝒳 z hz Ω hΩ)

variable {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)

include hz in
/-- **The base change of the inclusion of the locus of `Ω` is the subspace of Stacks 03BZ cut out
by a set of points.** For a property `P` of the objects of `𝒳` which is the locus of a set `Ω` of
points of `|𝒳|`, the subfunctor of `yoneda V` that `P` cuts out at a scheme-valued point `z` is
`AlgebraicGeometry.Space.openSubspaceOfPoints` at
`AlgebraicGeometry.Stack.pointChartPointSet`. -/
theorem fullSubcategoryBaseChangeSubfunctor_eq_openSubspaceOfPoints
    (hPΩ : ∀ x : 𝒳.val.val.obj, P x ↔ pointsWithin 𝒳 Ω x) :
    fullSubcategoryBaseChangeSubfunctor 𝒳 hP z =
      Space.openSubspaceOfPoints B V.left.1 V.left.2
        (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (pointChartPointSet B S hS 𝒳 z hz Ω) := by
  refine Subfunctor.ext (funext fun T => Set.ext fun x => ?_)
  have hx : x = Over.homMk T.unop.hom := Over.mkIdTerminal.hom_ext _ _
  subst hx
  rw [Space.mem_openSubspaceOfPoints_yoneda_iff, image_pointsToScheme_pointChartPointSet]
  exact (hPΩ _).trans (pointsWithin_iff_range_subset_pointChartSchemePointSet B S hS 𝒳 z hz Ω _)

include hz in
/-- **The base change of a full-subcategory inclusion along a scheme-valued point is an open
subspace of `V`.**

Let `𝒳` be an algebraic stack over `S`, let `Ω` be an **open** set of points of `|𝒳|`
(**Stacks 04XL**), and let `P` be the property of the objects of `𝒳` that `Ω` cuts out, i.e. the
locus `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` of **Stacks 04YM**. Then for every
scheme-valued point `z` of `𝒳` with values in `V`, the subfunctor
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of `yoneda V` cut out by `P` is an
open subspace of `V` in the sense of **Stacks 02YU**, part (2): it is an algebraic space over `V`
and its inclusion is an open immersion. -/
theorem isOpenSubspace_fullSubcategoryBaseChangeSubfunctor
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω)
    (hPΩ : ∀ x : 𝒳.val.val.obj, P x ↔ pointsWithin 𝒳 Ω x) :
    Space.IsOpenSubspace B V.left.1 V.left.2
      (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z) := by
  rw [fullSubcategoryBaseChangeSubfunctor_eq_openSubspaceOfPoints B S hS 𝒳 z hz Ω hP hPΩ]
  exact Space.isOpenSubspace_openSubspaceOfPoints B V.left.1 V.left.2
    (isAlgebraicSpace_yoneda B V.left.1 V.left.2 (Over.mk (𝟙 V.left))) _
    (isOpen_pointChartPointSet B S hS 𝒳 z hz Ω hΩ)

include hz in
/-- **The base change of the inclusion of the locus of an open set of points is an open subspace
of `V`.** `AlgebraicGeometry.Stack.isOpenSubspace_fullSubcategoryBaseChangeSubfunctor` at
`P = AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` itself, where the only hypothesis is that `Ω` is
open. -/
theorem isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_pointsWithin
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    Space.IsOpenSubspace B V.left.1 V.left.2
      (fullSubcategoryBaseChangeSubfunctor 𝒳
        (fun f => pointsWithin_of_hom 𝒳 Ω f) z) :=
  isOpenSubspace_fullSubcategoryBaseChangeSubfunctor B S hS 𝒳 z hz Ω
    (fun f => pointsWithin_of_hom 𝒳 Ω f) hΩ (fun _ => Iff.rfl)

/-- **The inclusion of the locus of an open set of points is representable by algebraic spaces
(Stacks 02ZW).** -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryBasedInclusion 𝒳 (pointsWithin 𝒳 Ω)) :=
  isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion 𝒳
    (fun f => pointsWithin_of_hom 𝒳 Ω f)
    (fun _ y hy =>
      (isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_pointsWithin B S hS 𝒳 y hy Ω hΩ).1)

/-- **The full subcategory cut out by an open set of points is an algebraic stack** (an
application of **Stacks 05UM**). This is the algebraicity clause of
`AlgebraicGeometry.Stack.OpenSubstack` for the locus of an open set of points. -/
theorem isAlgebraicStack_fullSubcategoryBased_pointsWithin
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (pointsWithin 𝒳 Ω)) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces.{u, w} B S hS
    (𝒳 := CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 (pointsWithin 𝒳 Ω))
      (isFiberedInGroupoids_fullSubcategoryBased 𝒳 (fun f => pointsWithin_of_hom 𝒳 Ω f)))
    (𝒴 := 𝒳.val)
    (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 (pointsWithin 𝒳 Ω)))
    (isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin
      B S hS 𝒳 Ω hΩ)
    𝒳.property

end AlgebraicGeometry.Stack

end
