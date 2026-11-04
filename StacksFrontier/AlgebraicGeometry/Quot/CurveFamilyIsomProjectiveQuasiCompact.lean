/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveCurveIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverPointVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# `Isom_V(Y, X) ⟶ V` for families of curves which are H-projective schemes over a Noetherian
affine base

Let `Y` and `X` be families of curves over a Noetherian affine `V` whose total spaces are
schemes `Z₁` and `Z₂`, H-projective over `V`. Then `Isom_V(Y, X)` is `Isom_V(Z₁, Z₂)`
(Stacks 05Y4, along the identity of `V`), the structure morphisms `Zᵢ ⟶ V` are flat and locally of
finite presentation, and the fibres of `Z₁ ⟶ V` over the spectra of fields have dimension at most
one (the fibre of a family of curves over a one-point base is a family of curves, whose total
space has dimension at most one). So
`AlgebraicGeometry.ProjectiveCurveIsomQuasiCompact.isQuasiCompact_isomSubfunctor` applies: the
morphism `Isom_V(Y, X) ⟶ V` is quasi-compact.

## Main results

* `AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_isProjectiveMorphism`.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] AlgebraicGeometry.schemeSpace

namespace AlgebraicGeometry.CurveFamily

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The fibres over the spectra of fields of a family of curves whose total space is a scheme
`Z ⟶ V` have dimension at most one. -/
theorem topologicalKrullDim_pullback_le_one (F : CurveFamily B hZ)
    {Z : BigFppfOver B integerBase hZ} (q : Z ⟶ F.base) (e : F.total.obj ≅ yoneda.obj Z)
    (he : F.toBase.hom = e.hom ≫ yoneda.map q) {T : BigFppfOver B integerBase hZ}
    (a : T ⟶ F.base) (hT : Subsingleton ((𝒯).obj T)) :
    topologicalKrullDim ((𝒯).obj (pullback a q)) ≤ 1 := by
  have he' : IsPullback e.inv (yoneda.map q) F.toBase.hom (𝟙 (yoneda.obj F.base)) :=
    IsPullback.of_horiz_isIso ⟨by simp [he]⟩
  have hV : IsPullback (yoneda.map (pullback.snd a q) ≫ e.inv) (yoneda.map (pullback.fst a q))
      F.toBase.hom (yoneda.map a) := by
    simpa using ((IsPullback.of_hasPullback a q).flip.map yoneda).paste_horiz he'
  let Y := C1590Private.curveFamilyOfIsPullback F a _ _
    (C1590Private.isPullback_homMk_of_isPullback a (pullback.fst a q) _ hV)
  have : Subsingleton ((𝒯).obj Y.base) := hT
  exact (Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ _).symm.le.trans
    (CurveFamily.dimension_total_le_one_of_subsingleton Y)

/-- The structure morphism of a family of curves whose total space is a scheme `Z ⟶ V` is flat
and locally of finite presentation. -/
theorem flat_and_locallyOfFinitePresentation (F : CurveFamily B hZ)
    {Z V : BigFppfOver B integerBase hZ} (q : Z ⟶ V) (h : V = F.base)
    (e : F.total.obj ≅ yoneda.obj Z) (he : e.inv ≫ F.toBase.hom = yoneda.map (q ≫ eqToHom h)) :
    Flat ((𝒯).map q) ∧ LocallyOfFinitePresentation ((𝒯).map q) := by
  subst h
  rw [eqToHom_refl, Category.comp_id] at he
  have hsq : IsPullback (ObjectProperty.homMk e.inv : schemeSpace Z ⟶ F.total)
      (schemeSpaceMap q) F.toBase (schemeSpaceMap (𝟙 F.base)) :=
    C1590Private.isPullback_homMk_of_isPullback (𝟙 F.base) q e.inv
      (IsPullback.of_horiz_isIso ⟨by simp [he]⟩)
  have hflat := (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback hsq F.flat
  have hlfp := (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B integerBase
    hZ).of_isPullback hsq F.finitePresentation.1
  exact ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      Flat.isEtaleLocalOnSourceAndTarget _).1 hflat,
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _).1 hlfp⟩

/-- **`Isom_V(Y, X) ⟶ V` is quasi-compact for families of curves which are H-projective schemes
over a Noetherian affine base.** -/
theorem isQuasiCompact_isomFunctorProjection_of_isProjectiveMorphism (F G : CurveFamily B hZ)
    (hb : G.base = F.base) (haff : IsAffine ((𝒯).obj F.base))
    (hnoeth : IsNoetherian ((𝒯).obj F.base)) (Z₁ Z₂ : BigFppfOver B integerBase hZ)
    (q₁ : Z₁ ⟶ F.base) (q₂ : Z₂ ⟶ F.base) (e₁ : F.total.obj ≅ yoneda.obj Z₁)
    (e₂ : G.total.obj ≅ yoneda.obj Z₂) (he₁ : F.toBase.hom = e₁.hom ≫ yoneda.map q₁)
    (he₂ : G.toBase.hom ≫ yoneda.map (eqToHom hb) = e₂.hom ≫ yoneda.map q₂)
    (hq₁ : IsProjectiveMorphism ((𝒯).map q₁)) (hq₂ : IsProjectiveMorphism ((𝒯).map q₂)) :
    Space.IsQuasiCompact B integerBase hZ
      (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))) := by
  obtain ⟨hflat₁, hlfp₁⟩ := flat_and_locallyOfFinitePresentation F q₁ rfl e₁ (by
    rw [he₁, Iso.inv_hom_id_assoc, eqToHom_refl, Category.comp_id])
  obtain ⟨hflat₂, hlfp₂⟩ := flat_and_locallyOfFinitePresentation G q₂ hb.symm e₂ (by
    rw [← cancel_mono (yoneda.map (eqToHom hb)), Category.assoc, he₂, Iso.inv_hom_id_assoc,
      ← CategoryTheory.Functor.map_comp, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id])
  have hqc := ProjectiveCurveIsomQuasiCompact.isQuasiCompact_isomSubfunctor (B := B) q₁ q₂ haff
    hnoeth hq₁ hq₂ hflat₁ hflat₂ hlfp₁ hlfp₂
    (fun a hT => topologicalKrullDim_pullback_le_one F q₁ e₁ he₁ a hT)
  have ha : IsPullback e₁.inv (yoneda.map q₁) F.toBase.hom (𝟙 (yoneda.obj F.base)) :=
    IsPullback.of_horiz_isIso ⟨by simp [he₁]⟩
  have hc : IsPullback e₂.inv (yoneda.map q₂) (G.toBase.hom ≫ yoneda.map (eqToHom hb))
      (𝟙 (yoneda.obj F.base)) :=
    IsPullback.of_horiz_isIso ⟨by simp [he₂]⟩
  obtain ⟨g, hg⟩ := Space.exists_isPullback_isomSubfunctor_of_isPullback F.toBase.hom
    (G.toBase.hom ≫ yoneda.map (eqToHom hb)) (𝟙 _) (yoneda.map q₁) (yoneda.map q₂) e₁.inv e₂.inv
    ha hc F.total.property G.total.property (schemeSpace F.base).property
    (isAlgebraicSpace_yoneda B integerBase hZ Z₁) (isAlgebraicSpace_yoneda B integerBase hZ Z₂)
    (isAlgebraicSpace_yoneda B integerBase hZ F.base)
  have : IsIso (𝟙 (schemeSpace F.base).obj) := IsIso.id _
  have hgi : IsIso g := hg.isIso_fst_of_isIso
  exact @Space.isQuasiCompact_of_arrowIso B integerBase hZ _ _ _ _ _ _ g (𝟙 _) hgi
    (IsIso.id _) hg.w hqc

end AlgebraicGeometry.CurveFamily

end
