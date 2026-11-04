module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr

/-!
# The étale charts of a represented presheaf as schemes étale over the representing scheme

Let `B` be a big fppf site containing a scheme `S`, let `F` be a presheaf on the big fppf site
of `S` and let `e : F ≅ yoneda.obj V` identify `F` with the presheaf represented by an object `V`
of the site. An étale chart `φ : yoneda.obj U ⟶ F` of `F` then corresponds, by the Yoneda lemma,
to a morphism `U ⟶ V` of the site, and that morphism is étale on underlying schemes. This file
records the resulting functor from the small étale site of `F` (and from its affine étale site)
to Mathlib's small étale site `V.Etale` of the scheme underlying `V`, and the two properties of
it that are used to compute with sheaves through it: it preserves fibre products, and it is
compatible with the functors to schemes on the nose.

## Main definitions

* `AlgebraicGeometry.Space.chartToRepresented`: the morphism `U ⟶ V` of the site underlying an
  étale chart of `F`, read through `e`.
* `AlgebraicGeometry.Space.representedChartEtale`: the functor from the small étale site of `F`
  to the small étale site of the scheme underlying `V`.
* `AlgebraicGeometry.Space.representedAffineChartEtale`: its restriction to the affine étale
  site of `F`.

## Main results

* `AlgebraicGeometry.Space.etale_chartToRepresented`: the morphism underlying a chart is étale.
* `AlgebraicGeometry.Space.representedChartEtale_preservesPullbacks` and
  `AlgebraicGeometry.Space.representedAffineChartEtale_preservesPullbacks`: both functors
  preserve fibre products.

## Implementation notes

The functor is built by hand rather than as the composite of the equivalences
`AlgebraicGeometry.Space.SmallEtale.congr`,
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and
`AlgebraicGeometry.SmallEtale.toEtaleSite`, so that the scheme underlying the image of a chart is
the scheme underlying the chart by definition. Fibre products are preserved because the composite
with the forgetful functors to schemes is the functor to schemes of the small étale site, which
preserves them, and the forgetful functors from `V.Etale` to schemes reflect them: the first is
fully faithful and the second creates connected limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (e : F ≅ yoneda.obj V)

/-- The morphism of the big fppf site of `S` underlying an étale chart of `F`, read through the
identification `e` of `F` with the presheaf represented by `V`. -/
noncomputable def chartToRepresented (W : SmallEtale B S hS F) : W.obj.left ⟶ V :=
  Yoneda.fullyFaithful.preimage (W.obj.hom ≫ e.hom)

/-- The Yoneda image of the morphism underlying a chart is the chart followed by `e`. -/
@[simp]
theorem yoneda_map_chartToRepresented (W : SmallEtale B S hS F) :
    yoneda.map (chartToRepresented e W) = W.obj.hom ≫ e.hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- **The morphism underlying an étale chart of a represented presheaf is étale.** -/
theorem etale_chartToRepresented (W : SmallEtale B S hS F) :
    Etale ((BigFppfOver.toScheme B S hS).map (chartToRepresented e W)) := by
  have h : IsEtaleChart B S hS (yoneda.obj V) (CostructuredArrow.mk (W.obj.hom ≫ e.hom)) :=
    (isEtaleChart_comp_iso_iff B S hS e W.obj.hom).2 W.property
  change (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (W.obj.hom ≫ e.hom) at h
  rw [← yoneda_map_chartToRepresented e W] at h
  exact MorphismProperty.of_relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) h

/-- The morphisms underlying charts are compatible with the morphisms of charts. -/
@[reassoc (attr := simp)]
theorem map_left_comp_chartToRepresented {W W' : SmallEtale B S hS F} (f : W ⟶ W') :
    f.hom.left ≫ chartToRepresented e W' = chartToRepresented e W := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_chartToRepresented, yoneda_map_chartToRepresented,
    ← Category.assoc, CostructuredArrow.w f.hom]

/-- **The small étale site of a represented presheaf, mapped to Mathlib's small étale site of
the representing scheme.** A chart goes to its underlying scheme with the étale morphism
`AlgebraicGeometry.Space.chartToRepresented` to the scheme underlying `V`, and a morphism of
charts to its underlying morphism of schemes. -/
noncomputable def representedChartEtale :
    SmallEtale B S hS F ⥤ ((BigFppfOver.toScheme B S hS).obj V).Etale where
  obj W :=
    MorphismProperty.Over.mk (P := (@Etale.{u} : MorphismProperty Scheme.{u})) (Q := ⊤)
      ((BigFppfOver.toScheme B S hS).map (chartToRepresented e W))
      (etale_chartToRepresented e W)
  map {W W'} f :=
    MorphismProperty.Over.homMk ((BigFppfOver.toScheme B S hS).map f.hom.left) (by
      change (BigFppfOver.toScheme B S hS).map f.hom.left ≫
          (BigFppfOver.toScheme B S hS).map (chartToRepresented e W') =
        (BigFppfOver.toScheme B S hS).map (chartToRepresented e W)
      rw [← Functor.map_comp, map_left_comp_chartToRepresented])
  map_id W := MorphismProperty.Over.Hom.ext ((BigFppfOver.toScheme B S hS).map_id W.obj.left)
  map_comp f g := MorphismProperty.Over.Hom.ext
    ((BigFppfOver.toScheme B S hS).map_comp f.hom.left g.hom.left)

/-- The scheme underlying the image of a chart is the scheme underlying the chart. -/
@[simp]
theorem representedChartEtale_obj_left (W : SmallEtale B S hS F) :
    ((representedChartEtale e).obj W).left = (BigFppfOver.toScheme B S hS).obj W.obj.left :=
  rfl

/-- The structure morphism of the image of a chart is the morphism underlying the chart. -/
@[simp]
theorem representedChartEtale_obj_hom (W : SmallEtale B S hS F) :
    ((representedChartEtale e).obj W).hom =
      (BigFppfOver.toScheme B S hS).map (chartToRepresented e W) :=
  rfl

/-- The morphism of schemes underlying the image of a morphism of charts. -/
@[simp]
theorem representedChartEtale_map_left {W W' : SmallEtale B S hS F} (f : W ⟶ W') :
    ((representedChartEtale e).map f).left = (BigFppfOver.toScheme B S hS).map f.hom.left :=
  rfl

/-- The composite of `AlgebraicGeometry.Space.representedChartEtale` with the forgetful functors
to schemes is the functor to schemes of the small étale site. -/
theorem representedChartEtale_comp_forget :
    representedChartEtale e ⋙ Scheme.Etale.forget _ ⋙ Over.forget _ =
      SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS :=
  rfl

/-- The forgetful functor from the small étale site of a scheme to schemes reflects fibre
products. -/
instance reflectsPullbacks_etaleForget (X : Scheme.{u}) :
    ReflectsLimitsOfShape WalkingCospan (Scheme.Etale.forget X ⋙ Over.forget X) := by
  have : ReflectsLimitsOfShape WalkingCospan (Scheme.Etale.forget X) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  infer_instance

/-- **The functor to the small étale site of the representing scheme preserves fibre
products.** -/
instance representedChartEtale_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (representedChartEtale e) := by
  have : PreservesLimitsOfShape WalkingCospan
      (representedChartEtale e ⋙ Scheme.Etale.forget _ ⋙ Over.forget _) := by
    rw [representedChartEtale_comp_forget]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (representedChartEtale e)
    (Scheme.Etale.forget _ ⋙ Over.forget _)

/-- The affine étale site of a represented presheaf, mapped to Mathlib's small étale site of the
representing scheme. -/
noncomputable abbrev representedAffineChartEtale :
    AffineEtale B S hS F ⥤ ((BigFppfOver.toScheme B S hS).obj V).Etale :=
  AffineEtale.inclusion B S hS F ⋙ representedChartEtale e

/-- **The functor from the affine étale site preserves fibre products.** -/
instance representedAffineChartEtale_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (representedAffineChartEtale e) := by
  have : PreservesLimitsOfShape WalkingCospan
      (representedAffineChartEtale e ⋙ Scheme.Etale.forget _ ⋙ Over.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (AffineEtale.toScheme B S hS F))
  exact preservesLimitsOfShape_of_reflects_of_preserves (representedAffineChartEtale e)
    (Scheme.Etale.forget _ ⋙ Over.forget _)

/-- The scheme underlying the image of an affine chart is affine. -/
instance isAffine_representedAffineChartEtale_obj_left (W : AffineEtale B S hS F) :
    IsAffine ((representedAffineChartEtale e).obj W).left :=
  W.property

end AlgebraicGeometry.Space

end
