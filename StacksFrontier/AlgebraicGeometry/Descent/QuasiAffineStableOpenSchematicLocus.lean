module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatMonomorphismRepresentable

/-!
# A stable quasi-affine open of a flat chart lies in the schematic locus

Let `G` be an algebraic space over `S` with a morphism `π : G ⟶ h_u` to an object of the big
fppf site, let `w : a ⟶ u` be an open immersion out of an affine object, and let
`g : h_V ⟶ G` be a chart presented as the base change of `q ≫ w` along `π`, for a surjective,
flat morphism `q : c ⟶ a` of finite presentation out of an affine object. Let `T` be an open of
`V` which is quasi-affine as a scheme and *stable* for the chart: its two preimages in the fibre
product `V ×_G V` agree. Then every point of `G` coming from `T` lies in the schematic locus of
`G` (Stacks 03JH).

The image of `T` cuts out an open subspace `G_T` of `G`
(`AlgebraicGeometry.Space.openSubspaceOfPoints`), the image being open by Stacks 01UA; by
stability the part of the chart lying over `G_T` is `T` itself, so `G_T ×_{h_u} h_c` is the
quasi-affine scheme `T`, and the descent of quasi-affine morphisms along the fpqc chart `q`
(Stacks 0247, in the form
`AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart`, which uses that
algebraic spaces are fpqc sheaves, Stacks 0APL) makes `G_T ×_{h_u} h_a` a scheme. It is an open
subspace of `G` containing the image of `T`.

This is the step of the proof of Stacks 0D40 at which an ample invertible sheaf on the chart,
with a descent datum, produces scheme charts of the descended algebraic space: the nonvanishing
locus of an invariant section of a power of an ample sheaf is quasi-affine and stable.

## Main results

* `AlgebraicGeometry.Space.image_pointsMap_subset_schematicLocus_of_isQuasiAffine`: the points
  of `G` coming from a stable quasi-affine open of a flat chart lie in the schematic locus.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_QuasiAffineStableOpenSchematicLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_QuasiAffineStableOpenSchematicLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The points of a stable quasi-affine open of a flat chart lie in the schematic locus.**
Let `G` be an algebraic space over `S` with `π : G ⟶ h_u`, let `w : a ⟶ u` be an open immersion
with `a` affine, and let `g : h_V ⟶ G` be the base change along `π` of `q ≫ w`, for a
surjective flat morphism `q : c ⟶ a` locally of finite presentation with `c` affine. Let
`π₁ π₂ : D ⟶ V` present `h_D` as the fibre product of `g` with itself, and let `T` be an open of
`V` which is a quasi-affine scheme and has `π₁⁻¹ T = π₂⁻¹ T`. Then the image of `T` in the point
space of `G` lies in the schematic locus of `G`. -/
theorem image_pointsMap_subset_schematicLocus_of_isQuasiAffine
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {u a c V D : BigFppfOver B S hS} (π : G ⟶ yoneda.obj u) (w : a ⟶ u) (q : c ⟶ a)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map w)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj a)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [Flat ((BigFppfOver.toScheme B S hS).map q)]
    [Surjective ((BigFppfOver.toScheme B S hS).map q)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q)]
    (g : yoneda.obj V ⟶ G) (ρ : V ⟶ c)
    (sqg : IsPullback g (yoneda.map ρ) π (yoneda.map (q ≫ w)))
    (π₁ π₂ : D ⟶ V) (sq : IsPullback (yoneda.map π₁) (yoneda.map π₂) g g)
    (T : ((BigFppfOver.toScheme B S hS).obj V).Opens) [(T : Scheme.{u}).IsQuasiAffine]
    (hT : (BigFppfOver.toScheme B S hS).map π₁ ⁻¹ᵁ T =
      (BigFppfOver.toScheme B S hS).map π₂ ⁻¹ᵁ T) :
    pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' (T : Set _)) ⊆
      Set.range (pointsMap B S hS (schematicLocus B S hS G).toFunctor
        (schematicLocus B S hS G).ι) := by
  classical
  -- the chart is universally open, by Stacks 01UA
  have huo : _root_.AlgebraicGeometry.UniversallyOpen
      ((BigFppfOver.toScheme B S hS).map (q ≫ w)) := by
    rw [Functor.map_comp]
    infer_instance
  have hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqg.flip
      (presheafIsOpenMap_yoneda_map_of_universallyOpen B S hS (q ≫ w) huo)
  -- the open subspace cut out by the image of `T`, and the part of the chart over it
  have hWopen := isOpen_image_pointsMap_of_isOpen B S hS g hg T.isOpen
  obtain ⟨b, i, k, hi, hirange, hsqb⟩ :=
    exists_isPullback_ι_openSubspaceOfPoints_image B S hS g hg T.isOpen
  -- by stability, that part is `T` itself
  have hsat : pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj V) g ⁻¹'
      (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' (T : Set _)))) =
      (T : Set _) := by
    refine subset_antisymm ?_ (subset_preimage_image_pointsMap B S hS g _)
    rw [image_pointsToScheme_preimage_image_pointsMap B S hS g sq]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((BigFppfOver.toScheme B S hS).map π₂ ⁻¹ᵁ T : Set _) := by
      rw [← hT]
      exact hy
    exact hy'
  have _hi := hi
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map i) = Set.range T.ι := by
    rw [hirange, hsat, Scheme.Opens.range_ι]
  generalize hWdef :
    pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' (T : Set _)) = W
    at hWopen k hsqb ⊢
  -- so `b` is a quasi-affine scheme, and quasi-affine over the affine `c`
  have hbqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    Scheme.IsQuasiAffine.of_isAffineHom
      (IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map i) T.ι hrange).hom
  have hQA : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ ρ)) :=
    isQuasiAffineHom_of_isQuasiAffine _ hbqa inferInstance
  have hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ yoneda.map ρ) := by
    rw [← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ)).2 hQA
  -- the datum of the open subspace over the chart
  have hGTsub : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS G W) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG W hWopen
  have sqg' : IsPullback g (yoneda.map ρ) π (yoneda.map q ≫ yoneda.map w) := by
    rw [← Functor.map_comp]
    exact sqg
  have sqF : IsPullback k (yoneda.map i ≫ yoneda.map ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q ≫ yoneda.map w) :=
    hsqb.paste_vert sqg'
  -- Stacks 0247 along the fpqc chart `q`
  have hpb := presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart
    (f := (openSubspaceOfPoints B S hS G W).ι ≫ π) (h := yoneda.map w) (q := q) (m := k)
    (r := yoneda.map i ≫ yoneda.map ρ)
    hGTsub.1.isSheaf_fpqc (isAlgebraicSpace_yoneda B S hS u).isSheaf_fpqc inferInstance
    inferInstance inferInstance inferInstance inferInstance sqF hr
  have _hrep : (Limits.pullback ((openSubspaceOfPoints B S hS G W).ι ≫ π)
      (yoneda.map w)).IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hpb.rep
  -- the open immersion of the base change to `h_a` into `G`
  have hwoi : IsOpenImmersion B S hS (yoneda.map w) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ w).2 inferInstance
  have hfst : IsOpenImmersion B S hS
      (pullback.fst ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map w)) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback ((openSubspaceOfPoints B S hS G W).ι ≫ π)
        (yoneda.map w)).flip hwoi
  have _hcomp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hj : IsOpenImmersion B S hS
      (pullback.fst ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map w) ≫
        (openSubspaceOfPoints B S hS G W).ι) :=
    MorphismProperty.comp_mem _ _ _ hfst hGTsub.2
  -- its image is everything in `W`
  refine subset_trans ?_ (range_pointsMap_subset_schematicLocus_of_isOpenImmersion B S hS hG
    _ hj)
  rintro _ hp
  obtain ⟨t, ht, rfl⟩ := hWdef ▸ hp
  have hmem : pointsMap B S hS (yoneda.obj V) g t ∈
      Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS G W).toFunctor
        (openSubspaceOfPoints B S hS G W).ι) := by
    rw [range_pointsMap_ι_openSubspaceOfPoints, ← hWdef]
    exact ⟨t, ht, rfl⟩
  obtain ⟨p', hp'⟩ := hmem
  have hab : pointsMap B S hS (openSubspaceOfPoints B S hS G W).toFunctor
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) p' =
      pointsMap B S hS (yoneda.obj a) (yoneda.map w)
        (pointsMap B S hS (yoneda.obj V) (yoneda.map ρ ≫ yoneda.map q) t) := by
    rw [pointsMap_comp_apply, hp', ← pointsMap_comp_apply, ← pointsMap_comp_apply, sqg'.w,
      Category.assoc]
  obtain ⟨w', hw', -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map w)) p' _ hab
  exact ⟨w', by rw [pointsMap_comp_apply, hw', hp']⟩

end AlgebraicGeometry.Space

end
