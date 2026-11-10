module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceBaseChangeSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation

/-!
# Open substacks of algebraic stacks over the category of curves

Let `P` be a property of families of curves satisfying condition (o) of Section 0E0E
(`AlgebraicGeometry.IsOpenCurvesLocus`): every family of curves `X → S` has a largest open
subscheme `S' ⊂ S` over which it has `P`, and the formation of `S'` commutes with arbitrary base
change. By Stacks 0E0E the families with `P` form an open substack `Curves^P` of `Curves`.

This file proves the same statement for an arbitrary algebraic stack `𝒳` equipped with a
`1`-morphism `F : 𝒳 → Curves` to the category fibred in groupoids of families of curves: the
objects of `𝒳` whose image under `F` has `P` form an open substack `𝒳^P` of `𝒳` in the sense of
Stacks 04YM, and a scheme-valued point of `𝒳` factors through `𝒳^P` exactly when the family of
curves it classifies has `P`. For any `𝒳` it is the inverse image of `Curves^P` along `F`.

## Main definitions

* `AlgebraicGeometry.curvesOpenSubstack`: the open substack `𝒳^P` of an algebraic stack over
  the category of curves.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.exists_isOpen_range_subset`: condition (o) read as an
  open subset of the base scheme of every family.
* `AlgebraicGeometry.IsOpenCurvesLocus.of_baseLocus`: condition (o) from an open locus of points
  of the base compatible with base change.
* `AlgebraicGeometry.isOpenSubspace_curvesBaseChangeSubfunctor`: the base change of the
  inclusion of `𝒳^P` along a scheme-valued point of `𝒳` is an open subspace, the condition of
  `AlgebraicGeometry.Stack.openSubstackOfIsOpenSubspace`.
* `AlgebraicGeometry.factorsThrough_curvesOpenSubstack_iff`: a scheme-valued point of `𝒳` with
  values in `S`, whose value at `S` is sent by `F` to a family `X → S`, factors through `𝒳^P`
  exactly when `X → S` has `P`.

## Implementation notes

An open substack in the sense of Stacks 04YM is a full subcategory of an *algebraic* stack,
which is why the construction here is made over an algebraic stack `𝒳` with a `1`-morphism to
the category of curves. The total category of `AlgebraicGeometry.curvesFiberedCategory` has its
morphisms in the universe above that of the schemes, so it is not itself an object of the
2-category of algebraic stacks of Stacks 03YP; `F` is allowed to land in it all the same.

A scheme-valued point of `𝒳` with values in `V` is a functor `z` from the big fppf site of `V`
whose composite with the projection is the forgetful functor to the big fppf site of the
integers. The family `F(z(T))` attached to `T → V` maps to the family `F(z(V))`, over the
morphism `T → V` up to the identification of bases that the equation of functors supplies, so by
(o) it has `P` exactly when the image of `T` lies in the open locus of `F(z(V))`. That is the
subspace of `V` of Stacks 03BZ cut out by an open set of points, which is an open subspace.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

attribute [local instance] Space.pointTopology

/-- The image of a composite of morphisms of schemes whose first factor is an isomorphism lies in
a subset exactly when the image of the second factor followed by the third does, and the image
of a morphism followed by an isomorphism lies in a subset exactly when the image of the morphism
lies in its inverse image. -/
theorem Scheme.range_comp_comp_subset_iff {X X' Y Y' : Scheme.{u}} (e : X ⟶ X') [IsIso e]
    (g : X' ⟶ Y) (e' : Y ⟶ Y') (W : Set Y') :
    Set.range (e ≫ g ≫ e').base ⊆ W ↔ Set.range g.base ⊆ e'.base ⁻¹' W := by
  constructor
  · rintro hsub _ ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.base).2 x'
    exact hsub ⟨x, by simp [Scheme.Hom.comp_base]⟩
  · rintro hsub _ ⟨x, rfl⟩
    simpa [Scheme.Hom.comp_base] using hsub ⟨e.base x, rfl⟩

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  {P : ObjectProperty (CurveFamily B hZ)}

/-- **Condition (o) as an open subset of the base scheme.** For a property satisfying condition
(o), every family of curves `G` has an open subset `U` of its base scheme such that a family
mapping to `G` has the property exactly when its morphism of base schemes lands in `U`: the
image in the base scheme of the points of the open subspace given by condition (o). -/
theorem IsOpenCurvesLocus.exists_isOpen_range_subset (hP : IsOpenCurvesLocus B hZ P)
    (G : CurveFamily B hZ) :
    ∃ U : Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base), IsOpen U ∧
      ∀ ⦃F : CurveFamily B hZ⦄ (a : F ⟶ G),
        P F ↔ Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ U := by
  obtain ⟨W, hW, hchar⟩ := hP G
  have hΩ := Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
    (schemeSpace G.base).property W hW
  obtain ⟨V, hV, hVΩ⟩ := (Space.isSchemeOpen_iff_exists_preimage B integerBase hZ G.base _).1
    ((Space.isOpen_yoneda_iff_isSchemeOpen B integerBase hZ G.base _).1 hΩ)
  refine ⟨V, hV, fun F a => ?_⟩
  rw [hchar F a, Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property W hW]
  refine (Space.range_pointsMap_yoneda_subset_iff B integerBase hZ a.baseMap _).trans ?_
  rw [← hVΩ, Set.image_preimage_eq _ (Space.surjective_pointsToScheme B integerBase hZ G.base)]

/-- **Condition (o) from an open locus of points of the base compatible with base change.** Let
`L` assign to every family of curves an open set of points of its base, read as an algebraic
space, such that the locus of a family mapping to another is the inverse image of the locus of
the target and a family has `P` exactly when its locus is everything. Then `P` satisfies
condition (o). -/
theorem IsOpenCurvesLocus.of_baseLocus
    (L : ∀ X : CurveFamily B hZ, Set (Space.points B integerBase hZ (schemeSpace X.base).obj))
    (hopen : ∀ X, IsOpen (L X))
    (hpre : ∀ {X Y : CurveFamily B hZ} (φ : X ⟶ Y),
      Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        L Y = L X)
    (hP : ∀ X, P X ↔ L X = Set.univ) : IsOpenCurvesLocus B hZ P := by
  refine IsOpenCurvesLocus.of_points fun G => ⟨L G, hopen G, fun F a => ?_⟩
  rw [hP, ← hpre a, Set.range_subset_iff, Set.eq_univ_iff_forall]
  rfl

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
  (F : 𝒳.val.val ⥤ᵇ (curvesFiberedCategory B hZ).val)

/-- The property of the objects of an algebraic stack over the category of curves induced by a
property of families of curves: an object has it when the family of curves it is sent to does. -/
abbrev curvesObjectProperty (P : ObjectProperty (CurveFamily B hZ)) :
    ObjectProperty 𝒳.val.val.obj :=
  fun x => P (F.obj x)

variable {F}

/-- A property with an open locus on the base passes along the morphisms of an algebraic stack
over the category of curves. -/
theorem curvesObjectProperty_of_hom (hP : IsOpenCurvesLocus B hZ P)
    {a b : 𝒳.val.val.obj} (m : a ⟶ b) (hb : curvesObjectProperty F P b) :
    curvesObjectProperty F P a :=
  hP.prop_of_hom (F.map m) hb

variable (F) in
/-- **The base change of the inclusion of `𝒳^P` along a scheme-valued point is an open
subspace.** Let `z` be a scheme-valued point of `𝒳` with values in `V`. The subfunctor of
`yoneda V` whose sections over `T → V` exist exactly when the family `F(z(T))` has `P` is an open
subspace of `V`: it is the subspace of Stacks 03BZ cut out by the open locus of the family
`F(z(V))`, transported to `V` along the identification of the base of `F(z(V))` with `V`. -/
theorem isOpenSubspace_curvesBaseChangeSubfunctor (hP : IsOpenCurvesLocus B hZ P)
    (V : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map V.hom) :
    Space.IsOpenSubspace B V.left.1 V.left.2
      (Stack.fullSubcategoryBaseChangeSubfunctor 𝒳
        (curvesObjectProperty_of_hom (F := F) hP) z) := by
  let top : BigFppfOver B V.left.1 V.left.2 := Over.mk (𝟙 V.left)
  let z' := z ⋙ F.toFunctor
  have hz' : z' ⋙ (curvesFiberedCategory B hZ).val.p = Over.map V.hom := by
    change z ⋙ (F.toFunctor ⋙ (curvesFiberedCategory B hZ).val.p) = _
    rw [F.w]
    exact hz
  obtain ⟨U, hUo, hU⟩ := hP.exists_isOpen_range_subset (z'.obj top)
  have e : (Over.map V.hom).obj top = (curvesFiberedCategory B hZ).val.p.obj (z'.obj top) :=
    (Functor.congr_obj hz' top).symm
  let ψ := (BigFppfOver.toScheme B integerBase hZ).map (eqToHom e)
  let L : Set ((BigFppfOver.toScheme B V.left.1 V.left.2).obj top) := ψ ⁻¹' U
  have hL : IsOpen L := hUo.preimage ψ.continuous
  let Pset : Set (Space.points B V.left.1 V.left.2
      (yoneda.obj top : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
    Space.pointsToScheme B V.left.1 V.left.2 top ⁻¹' L
  have hPset : @IsOpen _ (Space.pointTopology B V.left.1 V.left.2 _) Pset := by
    let := Space.pointTopology B V.left.1 V.left.2
      (yoneda.obj top : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    exact (Space.schemePointsHomeomorph B V.left.1 V.left.2 top).continuous.isOpen_preimage _ hL
  have heq : Stack.fullSubcategoryBaseChangeSubfunctor 𝒳
        (curvesObjectProperty_of_hom (F := F) hP) z =
      Space.openSubspaceOfPoints B V.left.1 V.left.2
        (yoneda.obj top : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u) Pset := by
    refine Subfunctor.ext (funext fun T => Set.ext fun x => ?_)
    rw [Space.mem_openSubspaceOfPoints_iff, CategoryTheory.yonedaEquiv_symm_eq_yoneda_map,
      Space.range_pointsMap_yoneda_subset_iff,
      Set.image_preimage_eq _ (Space.surjective_pointsToScheme B V.left.1 V.left.2 top)]
    change P (z'.obj T.unop) ↔ _
    rw [hU (z'.map x)]
    have hlift : (curvesFiberedCategory B hZ).val.p.IsHomLift ((Over.map V.hom).map x)
        (z'.map x) :=
      Functor.isHomLift_map_of_comp_eq hz' ((Over.map V.hom).map x) x
    change Set.range ((BigFppfOver.toScheme B integerBase hZ).map
      ((curvesFiberedCategory B hZ).val.p.map (z'.map x))) ⊆ U ↔ _
    rw [IsHomLift.fac' (curvesFiberedCategory B hZ).val.p ((Over.map V.hom).map x) (z'.map x),
      Functor.map_comp, Functor.map_comp]
    exact Scheme.range_comp_comp_subset_iff _ _ _ U
  rw [heq]
  exact Space.isOpenSubspace_openSubspaceOfPoints B V.left.1 V.left.2
    (isAlgebraicSpace_yoneda B V.left.1 V.left.2 top) _ hPset

variable (F) in
/-- **The open substack `𝒳^P` (Section 0E0E).** Let `𝒳` be an algebraic stack with a
`1`-morphism `F` to the category of curves, and let `P` be a property of families of curves with
an open locus on the base. The full subcategory of `𝒳` on the objects whose family of curves has
`P` is an open substack of `𝒳` in the sense of Stacks 04YM. For the stack of curves itself and
its identification with families of curves, this is the open substack `Curves^P` of the
source. -/
def curvesOpenSubstack (hP : IsOpenCurvesLocus B hZ P) : Stack.OpenSubstack 𝒳 :=
  Stack.openSubstackOfIsOpenSubspace B integerBase hZ 𝒳 (curvesObjectProperty_of_hom (F := F) hP)
    (isOpenSubspace_curvesBaseChangeSubfunctor F hP)

variable (F) in
/-- The objects of `𝒳^P` are those whose family of curves has `P`. -/
@[simp]
theorem curvesOpenSubstack_property (hP : IsOpenCurvesLocus B hZ P) (x : 𝒳.val.val.obj) :
    (curvesOpenSubstack F hP).property x ↔ P (F.obj x) :=
  Iff.rfl

variable (F) in
/-- **A classifying morphism factors through `𝒳^P` exactly when the family has `P`.** Let `z` be
a scheme-valued point of `𝒳` with values in `S` whose value at `S` is sent by `F` to a family of
curves isomorphic to `X`. Then `z` factors through the open substack `𝒳^P`, over the site and up
to a 2-isomorphism, if and only if `X` has `P`.

By Stacks 0507 the factorization is the condition that every value of `z` has `P`; the value at
`S` is sent to a family isomorphic to `X`, and every other value maps to it. -/
theorem factorsThrough_curvesOpenSubstack_iff (hP : IsOpenCurvesLocus B hZ P)
    (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : F.obj (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.fullSubcategoryBased 𝒳 (curvesOpenSubstack F hP).property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 (curvesOpenSubstack F hP).property)
          ≅ { toFunctor := z, w := hz })) ↔
      P X := by
  have := (curvesOpenSubstack F hP).strictlyFull
  rw [Stack.exists_based_factorization_iff]
  exact ⟨fun hall => hP.prop_of_hom ξ.inv (hall (Over.mk (𝟙 S.left))),
    fun hX T => curvesObjectProperty_of_hom hP (z.map (Over.mkIdTerminal.from T))
      (hP.prop_of_hom ξ.hom hX)⟩

end AlgebraicGeometry

end
