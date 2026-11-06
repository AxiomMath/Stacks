module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Pushouts.ThickeningAffineAtlasOfChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Stacks 07W3 at schemes of the site

Let `Y' = Y ⨿_Z Z'` be a pushout of schemes of the big fppf site of `S` along a thickening
`i : Z ⟶ Z'` and an affine morphism `f : Z ⟶ Y`. If `W ⟶ Y'` is an algebraic space flat over
`Y'`, then `W` is the pushout `W ×_{Y'} Y ⨿_{W ×_{Y'} Z} W ×_{Y'} Z'` of its three base changes,
in the category of algebraic spaces over `S`: the counit clause of [Stacks Project, Tag 07W3],
for a span of schemes.

## Main results

* `AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`: the counit clause of
  Stacks 07W3 at schemes of the site, for prescribed base changes. Unregistered.

## Implementation notes

For a span of schemes the compatible étale charts of the proof of
[Stacks Project, Tag 07VX] can be taken to be the identities: the chart of `Y` is `𝟙 Y`, its
restriction to `Z` is `𝟙 Z`, and `𝟙 Z'` is a lift of it across the thickening. So the
general chart lift of [Stacks Project, Tag 05ZS] is not needed: the atlas is
`AlgebraicGeometry.Space.C1573.nonempty_thickeningAffineAtlas_of_isPullback` at the identity
charts, and the conclusion is
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas`, transported from the
pushout of algebraic spaces the atlas produces to `Y'` itself, which is a pushout of algebraic
spaces by [Stacks Project, Tag 07SY]
(`AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom'`).

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of a multiplicative property of schemes contains the identities. -/
private theorem containsIdentities_inverseImage {C : Type*} [Category C]
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] (F : C ⥤ Scheme.{u}) :
    (P.inverseImage F).ContainsIdentities :=
  have : P.ContainsIdentities := MorphismProperty.IsMultiplicative.toContainsIdentities
  inferInstance

/-- **Stacks 07W3 at schemes of the site (trivial atlas); unregistered helper.** Let
`i ≫ a = f ≫ b` be a square of schemes of the big fppf site of `S` whose image in schemes is a
pushout `Y' = Y ⨿_Z Z'` along the thickening `i : Z ⟶ Z'` and the affine morphism `f : Z ⟶ Y`.
Let `π : W ⟶ Y'` be a flat morphism of algebraic spaces over `S`, and let `WY`, `WZ'` and `WZ`
be its base changes to `Y`, `Z'` and `Z`, with `l : WZ ⟶ WY` and `k : WZ ⟶ WZ'` the induced
morphisms. Then `W = WY ⨿_{WZ} WZ'` in the category of algebraic spaces over `S`: the counit
clause of [Stacks Project, Tag 07W3], in the prescribed-span form. -/
theorem isPushout_of_isFlat_of_isPushout_schemeSpace
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f))
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b))
    {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
    (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
    (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ')
    (hπ : IsFlat B S hS π.hom)
    (hn : IsPullback n πY π (schemeSpaceMap b)) (hm : IsPullback m πZ' π (schemeSpaceMap a))
    (hl : IsPullback l πZ πY (schemeSpaceMap f)) (hk : k ≫ πZ' = πZ ≫ schemeSpaceMap i)
    (hlk : l ≫ n = k ≫ m) :
    IsPushout k l m n := by
  -- the span of algebraic spaces, a thickening and an affine morphism
  have hiS : IsThickeningHom B S hS (schemeSpaceMap i) :=
    FormalSpace.isThickeningHom_yonedaSpace_map B S hS i hi
  have hfS : IsAffineHom B S hS (schemeSpaceMap f).hom :=
    isAffineHom_yoneda_map_of_isAffineHom f hf
  -- the identity charts
  have := containsIdentities_inverseImage (@AlgebraicGeometry.Surjective.{u})
    (BigFppfOver.toScheme B S hS)
  have := containsIdentities_inverseImage (@AlgebraicGeometry.Etale.{u})
    (BigFppfOver.toScheme B S hS)
  obtain ⟨A⟩ := C1573.nonempty_thickeningAffineAtlas_of_isPullback B S hS hiS hfS
    (𝟙 (yoneda.obj Y)) (𝟙 (yoneda.obj Z)) (𝟙 (yoneda.obj Z')) i f
    (MorphismProperty.presheaf_of_isIso _ (𝟙 _)) (MorphismProperty.presheaf_of_isIso _ (𝟙 _))
    (MorphismProperty.presheaf_of_isIso _ (𝟙 _)) .of_id_fst .of_id_snd
  -- the pushout of algebraic spaces the atlas produces, and its chart
  obtain ⟨E, aY, bY, qm, hEpush, hqm, hqmS, hqmE, haX', hbY⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hiS
  -- `Y'` is a pushout of algebraic spaces, Stacks 07SY
  have hY'push : IsPushout (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap a)
      (schemeSpaceMap b) :=
    isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS i f a b hi hpush
  let e : E ≅ schemeSpace Y' := hEpush.isoIsPushout _ _ hY'push
  let eP : E.1 ≅ (schemeSpace Y').1 :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) e.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) e.inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = (schemeSpaceMap a).hom :=
    congrArg (fun φ => φ.hom) (hEpush.inl_isoIsPushout_hom _ _ hY'push)
  have hinr : bY.hom ≫ eP.hom = (schemeSpaceMap b).hom :=
    congrArg (fun φ => φ.hom) (hEpush.inr_isoIsPushout_hom _ _ hY'push)
  have hqm' : IsPullback (yoneda.map A.s) (yoneda.map A.t) (qm ≫ eP.hom) (qm ≫ eP.hom) :=
    hqm.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simp)
  have hback : (schemeSpaceMap i).hom ≫ (schemeSpaceMap a).hom =
      (schemeSpaceMap f).hom ≫ (schemeSpaceMap b).hom :=
    congrArg (fun φ => φ.hom) hY'push.w
  exact isPushout_of_isFlat_of_thickeningAffineAtlas B S hS A hqm'
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE)
    (haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinl.trans (Category.id_comp _).symm))
    (hbY.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinr.trans (Category.id_comp _).symm))
    hback hπ (AlgebraicSpaces.isPullback_hom B S hS hm) (AlgebraicSpaces.isPullback_hom B S hS hn)
    (AlgebraicSpaces.isPullback_hom B S hS hl) (congrArg (fun φ => φ.hom) hk)
    (congrArg (fun φ => φ.hom) hlk)

end AlgebraicGeometry.Space

end
