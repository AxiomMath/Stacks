module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# The locus of a set of points of an algebraic stack, read on a chart

Let `𝒳` be an algebraic stack over `S`, let `Ω` be a set of points of `|𝒳|` (**Stacks 04XG**),
and let `a : U ⟶ 𝒳` be a 1-morphism from the category of elements of an algebraic space `U` over
`S`. **Stacks 04YM** calls an object `x` of `𝒳` *within* `Ω` when every field-valued point of
`𝒳` admitting a morphism to `x` represents a point of `Ω`; that property is
`AlgebraicGeometry.Stack.pointsWithin`.

This file identifies the locus `pointsWithin 𝒳 Ω` on the chart: a section `s` of `U` over an
object `A` of the site has `pointsWithin 𝒳 Ω (a (A, s))` exactly when every point of `|A|` is
carried by `s` and `a` into `Ω`, which is exactly membership of `s` in the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` of `U` cut out by the inverse image of `Ω`. For
`Ω` open that subfunctor is an **open subspace** of `U` by **Stacks 03BZ**.

## Main results

* `AlgebraicGeometry.Stack.range_spacePointMap_subset_of_pointsWithin` and
  `AlgebraicGeometry.Stack.pointsWithin_of_range_spacePointMap_subset`: the two directions of
  the identification; by the second, an object of the chart all of whose points go into `Ω` lies
  in the locus.
* `AlgebraicGeometry.Stack.mem_openSubspaceOfPoints_spacePointMap_preimage_iff`: the two
  directions assembled, in the shape the subfunctor of **Stacks 03BZ** has.
* `AlgebraicGeometry.Stack.isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage`: for `Ω`
  open the locus cuts out an open subspace of the chart.
* `AlgebraicGeometry.Stack.pointsWithin_obj_of_pointsWithin_preimage`: the locus is carried along
  a 1-morphism of algebraic stacks; an object in the locus of the inverse image of `Ω` has its
  image in the locus of `Ω`.

## Related results

The open substack attached to an open `Ω` is the full subcategory cut out by
`AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`, which is
`AlgebraicGeometry.Stack.pointsWithinOpenSubstack`; the three clauses of
`AlgebraicGeometry.Stack.OpenSubstack` for it are the following.

* Closure under isomorphism is `AlgebraicGeometry.Stack.pointsWithin_of_hom`.
* Representability of the inclusion by algebraic spaces is
  `isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin`
  and algebraicity of the full subcategory is, by **Stacks 05UM**,
  `AlgebraicGeometry.Stack.isAlgebraicStack_fullSubcategoryBased_pointsWithin`.
* The open-immersion clause is
  `AlgebraicGeometry.Stack.isOpenImmersion_fullSubcategoryInclusion_pointsWithin`.

All three rest on the base change of the inclusion along a scheme-valued point being the open
subspace this file produces, which is
`AlgebraicGeometry.Stack.isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_pointsWithin`.
Every open subset of `|𝒳|` is thereby the point set of an open substack
(`AlgebraicGeometry.Stack.exists_openSubstack_pointSet_eq`, part of **Stacks 06FJ**), and
**Stacks 06M3** is
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_and_isRelativePropertyLocus_baseChange`.

The comparison of the 2-fibre product `U ×_𝒳 𝒲` of a chart with the category of elements of the
subfunctor this file cuts out on `U` is
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange`, for an arbitrary 2-fibre
product square over the cospan
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_of_isTwoFibreProduct`, and at
`AlgebraicGeometry.Stack.pointsWithin`
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_pointsWithin`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The locus of a set of points, read on a chart -/

variable (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- An object of a chart in the locus of `Ω` has all its points in `Ω`: if the object of `𝒳`
that a 1-morphism `a` from the category of elements of `U` attaches to a section `s` of `U` over
`A` lies in `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`, then every point of `|A|` is carried into
`Ω` by `s` followed by `a`. -/
theorem range_spacePointMap_subset_of_pointsWithin {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (a : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val)
    {A : BigFppfOver B S hS} (s : U.obj (Opposite.op A))
    (h : pointsWithin 𝒳 Ω (a.toFunctor.obj ⟨A, Discrete.mk s⟩)) :
    Set.range (spacePointMap B S hS U 𝒳.val a ∘
      Space.pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm s)) ⊆ Ω := by
  rintro z ⟨wq, rfl⟩
  obtain ⟨pp, rfl⟩ := Quot.exists_rep wq
  rw [Function.comp_apply, Space.pointsMap_class, spacePointMap_class]
  refine h _ (a.toFunctor.map ?_)
  exact (PresheafOfCategories.homEquiv (U ⋙ typeToCat) _ _).symm
    ⟨pp.value, eqToHom (congrArg Discrete.mk (by
      change U.map pp.value.op s = (yonedaEquiv.symm s).app (Opposite.op pp.siteObject) pp.value
      simp))⟩

/-- An object of a chart all of whose points lie in `Ω` lies in the locus of `Ω`: if every
point of `|A|` is carried into `Ω` by a section `s` of `U` over `A` followed by a 1-morphism `a`
from the category of elements of `U`, then the object of `𝒳` that `a` attaches to `s` lies in
`AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`. -/
theorem pointsWithin_of_range_spacePointMap_subset {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (a : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val)
    {A : BigFppfOver B S hS} (s : U.obj (Opposite.op A))
    (hrange : Set.range (spacePointMap B S hS U 𝒳.val a ∘
      Space.pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm s)) ⊆ Ω) :
    pointsWithin 𝒳 Ω (a.toFunctor.obj ⟨A, Discrete.mk s⟩) := by
  intro q φ
  have hfib : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  have hxbase : 𝒳.val.val.p.obj (a.toFunctor.obj
      (⟨A, Discrete.mk s⟩ : (fibredCategory B S hS U).val.obj)) = A := a.w_obj _
  set ψ : q.base ⟶ A := eqToHom q.over.symm ≫ 𝒳.val.val.p.map φ ≫ eqToHom hxbase with hψdef
  have hφlift : 𝒳.val.val.p.IsHomLift ψ φ :=
    IsHomLift.of_fac' _ ψ φ q.over hxbase (by rw [hψdef]; simp)
  set pval : spectrumSiteObject B S hS q ⟶ A :=
    (spectrumSiteObjectIso B S hS q).hom ≫ ψ with hpval
  set p : Space.FieldValuedPoint B S hS (yoneda.obj A) :=
    { carrier := q.carrier, field := q.field,
      contained := contains_spectrum_fieldValuedPoint B S hS q,
      toBase := spectrumStructureMorphism B S hS q, value := pval } with hpdef
  have key : pointClass B S hS 𝒳.val.val 𝒳.val.property q
      = spacePointMap B S hS U 𝒳.val a
          (Space.pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm s)
            (Space.FieldValuedPoint.class B S hS (yoneda.obj A) p)) := by
    rw [Space.pointsMap_class, spacePointMap_class]
    refine (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2 ⟨q, ⟨𝟙 _⟩, ⟨?_⟩⟩
    have hval : (yonedaEquiv.symm s).app
          (Opposite.op (spectrumSiteObject B S hS q)) pval
        = U.map pval.op s := by simp
    set χ : (⟨spectrumSiteObject B S hS q,
          Discrete.mk ((yonedaEquiv.symm s).app
            (Opposite.op (spectrumSiteObject B S hS q)) pval)⟩ :
        (fibredCategory B S hS U).val.obj) ⟶
        (⟨A, Discrete.mk s⟩ : (fibredCategory B S hS U).val.obj) :=
      (PresheafOfCategories.homEquiv (U ⋙ typeToCat) _ _).symm
        ⟨pval, eqToHom (congrArg Discrete.mk hval)⟩ with hχdef
    have hχ : (fibredCategory B S hS U).val.p.IsHomLift pval χ :=
      IsHomLift.of_fac' _ pval χ rfl rfl (by rfl)
    have haχ : 𝒳.val.val.p.IsHomLift pval (a.toFunctor.map χ) :=
      BasedFunctor.preserves_isHomLift a pval χ
    have hcart : 𝒳.val.val.p.IsStronglyCartesian pval (a.toFunctor.map χ) :=
      hfib.isStronglyCartesian_homLift pval (a.toFunctor.map χ)
    have hfac : ψ = (spectrumSiteObjectIso B S hS q).inv ≫ pval := by
      rw [hpval, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact Functor.IsStronglyCartesian.map 𝒳.val.val.p pval (a.toFunctor.map χ) hfac φ
  rw [key]
  exact hrange ⟨_, rfl⟩

/-- The locus of `Ω` on a chart is the subfunctor of Stacks 03BZ cut out by the inverse image
of `Ω`: a section `s` of `U` over `A` lies in
`AlgebraicGeometry.Space.openSubspaceOfPoints` of `U` at the inverse image of `Ω` along the
canonical map on points of the chart exactly when the object of `𝒳` the chart attaches to `s`
lies in `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`. -/
theorem mem_openSubspaceOfPoints_spacePointMap_preimage_iff
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (a : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val)
    {A : BigFppfOver B S hS} (s : U.obj (Opposite.op A)) :
    s ∈ (Space.openSubspaceOfPoints B S hS U
        (spacePointMap B S hS U 𝒳.val a ⁻¹' Ω)).obj (Opposite.op A) ↔
      pointsWithin 𝒳 Ω (a.toFunctor.obj ⟨A, Discrete.mk s⟩) := by
  rw [Space.mem_openSubspaceOfPoints_iff, ← Set.image_subset_iff, ← Set.range_comp]
  exact ⟨pointsWithin_of_range_spacePointMap_subset B S hS U Ω a s,
    range_spacePointMap_subset_of_pointsWithin B S hS U Ω a s⟩

/-- The inverse image along the canonical map on points of a chart of an open set of points of an
algebraic stack is open, the canonical map being continuous by **Stacks 04XL**. -/
theorem isOpen_spacePointMap_preimage {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (hU : IsAlgebraicSpace B S hS U)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (a : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val)
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    @IsOpen _ (Space.pointTopology B S hS U) (spacePointMap B S hS U 𝒳.val a ⁻¹' Ω) := by
  let := Space.pointTopology B S hS U
  let := pointTopology B S hS 𝒳.val
  exact (continuous_spacePointMap B S hS U hU 𝒳.val a).isOpen_preimage _ hΩ

/-- The locus of an open set of points cuts out an open subspace of a chart: for `Ω` an open
set of points of an algebraic stack `𝒳` and `a` a 1-morphism to `𝒳` from the category of elements
of an algebraic space `U` over `S`, the sections of `U` whose attached object of `𝒳` lies in
`AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` form an open subspace of `U`. -/
theorem isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (hU : IsAlgebraicSpace B S hS U)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (a : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val)
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS U
      (spacePointMap B S hS U 𝒳.val a ⁻¹' Ω)) :=
  Space.isOpenSubspace_openSubspaceOfPoints B S hS hU _
    (isOpen_spacePointMap_preimage B S hS U hU Ω a hΩ)

/-! ### The locus of a set of points along a 1-morphism -/

/-- The locus of a set of points is carried along a 1-morphism: let `F : 𝒜 ⟶ ℬ` be a
1-morphism of algebraic stacks over `S` and let `Ω` be a set of points of `|ℬ|`. An object `x` of
`𝒜` lying in the locus of the inverse image of `Ω` has its image `F x` in the locus of `Ω`. -/
theorem pointsWithin_obj_of_pointsWithin_preimage {𝒜 ℬ : AlgebraicStacks.{u, w} B S hS}
    (F : 𝒜.val.val ⥤ᵇ ℬ.val.val)
    (Ω : Set (points B S hS ℬ.val.val ℬ.val.property)) {x : 𝒜.val.val.obj}
    (hx : pointsWithin 𝒜
      (pointsMap B S hS 𝒜.val.val 𝒜.val.property ℬ.val.property F ⁻¹' Ω) x) :
    pointsWithin ℬ Ω (F.obj x) := by
  intro q φ
  have hA : 𝒜.val.val.p.IsFiberedInGroupoids := 𝒜.val.property
  have hB : ℬ.val.val.p.IsFiberedInGroupoids := ℬ.val.property
  have hxbase : ℬ.val.val.p.obj (F.obj x) = 𝒜.val.val.p.obj x := F.w_obj x
  set ψ : q.base ⟶ 𝒜.val.val.p.obj x :=
    eqToHom q.over.symm ≫ ℬ.val.val.p.map φ ≫ eqToHom hxbase with hψdef
  have hφ : ℬ.val.val.p.IsHomLift ψ φ :=
    IsHomLift.of_fac' _ ψ φ q.over hxbase (by rw [hψdef]; simp)
  obtain ⟨y, χ, hχ⟩ := hA.exists_lift ψ x rfl
  have hFχ : ℬ.val.val.p.IsHomLift ψ (F.map χ) := BasedFunctor.preserves_isHomLift F ψ χ
  have hcart : ℬ.val.val.p.IsStronglyCartesian ψ (F.map χ) :=
    hB.isStronglyCartesian_homLift ψ (F.map χ)
  set r : FieldValuedPoint B S hS 𝒜.val.val :=
    { carrier := q.carrier
      field := q.field
      base := q.base
      isSpec := q.isSpec
      obj := y
      «over» := IsHomLift.domain_eq 𝒜.val.val.p ψ χ } with hrdef
  have hmem := hx r χ
  rw [Set.mem_preimage, pointsMap_class] at hmem
  refine Set.mem_of_eq_of_mem ?_ hmem
  refine (class_eq_class_iff_hasCommonExtension B S hS ℬ.val.val ℬ.val.property _ _).2
    ⟨q, ⟨𝟙 q.obj⟩, ⟨?_⟩⟩
  exact Functor.IsStronglyCartesian.map ℬ.val.val.p ψ (F.map χ)
    (show ψ = 𝟙 q.base ≫ ψ by simp) φ

end AlgebraicGeometry.Stack

end
