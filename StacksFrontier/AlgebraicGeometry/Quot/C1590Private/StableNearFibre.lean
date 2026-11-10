module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableContractionTarget
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen

/-!
# Stability near a stable fibre

Let `Y ⟶ S` be a family of curves and `s` a point of `S` such that every fibre of `Y` at a
field-valued point over `s` is a stable curve. Then the families of curves mapping to `Y` over an
open neighbourhood of `s` are stable. This uses the openness of the stable locus (the openness of
Stacks 0E76), which is the hypothesis `h0E76`. That openness is proved unconditionally as
`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_unconditional`, which is not yet in this
library.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsStableCurveOver`: a stable curve over a field, presented by a
  scheme: proper of dimension one with `H⁰ = k`, at-worst-nodal, of genus at least two, without
  rational tails or rational bridges.

## Main results

* `AlgebraicGeometry.C1590Private.exists_presentation_of_fieldValuedPoint`: the fibre of a family
  of curves at a field-valued point is presented by a scheme.
* `AlgebraicGeometry.C1590Private.exists_isOpen_isStable_of_fibre`.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

/-- **A stable curve over a field**, presented by a scheme `W` with structure morphism `g`: `g` is
proper, `W` has dimension one, `H⁰(W, 𝒪_W) = k`, `W` has at-worst-nodal singularities, genus at
least two, and neither rational tails nor rational bridges. -/
def IsStableCurveOver (k : Type u) [Field k] {W : Scheme.{u}} (g : W ⟶ Spec (.of k)) : Prop :=
  IsProper g ∧ topologicalKrullDim W = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ∧
    (letI : W.Over (Spec (.of k)) := ⟨g⟩; Stacks.Curves.HasAtWorstNodalSingularities k W) ∧
    HasGenusTwoNoRationalTailNoRationalBridge k g

/-- **The target of a stable contraction of a curve of genus at least two is a stable curve.** -/
theorem IsStableContraction.isStableCurveOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} [IsProper f]
    (h : Stacks.Curves.StableModel.IsStableContraction f gY c)
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : 2 ≤ genus f) : IsStableCurveOver k gY := by
  have : IsProper gY := h.isProper
  have hc : IsIso c.appTop :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
      h.isIso_unitToPushforwardObjUnit ⊤
  have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ≫ c.appTop) := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, h.comp_eq]
    infer_instance
  exact ⟨h.isProper, h.topologicalKrullDim_eq, IsIso.of_isIso_comp_right _ c.appTop,
    h.hasAtWorstNodalSingularities,
    IsStableContraction.hasGenusTwoNoRationalTailNoRationalBridge h hdim hg⟩

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre of a family of curves at a field-valued point is presented by a scheme.** The base
change of the family to the field is a family of curves over a field, whose total space is a
scheme (`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`). -/
theorem exists_presentation_of_fieldValuedPoint (Y : CurveFamily B hZ)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj) :
    ∃ (W : BigFppfOver B integerBase hZ) (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ Y.total.obj),
      IsPullback r (yoneda.map w) Y.toBase.hom (yonedaEquiv.symm Q.value) := by
  rw [yonedaEquiv_symm_value]
  let t : Q.siteObject ⟶ Y.base := Q.value
  have h := IsPullback.of_hasPullback Y.toBase (schemeSpaceMap t)
  let F := curveFamilyOfIsPullback Y t _ _ h
  have hrep := F.isRepresentable_total_of_base_eq (K := Q.carrier) rfl
  rw [curveFamilyOfIsPullback_total] at hrep
  let X₀ := (pullback Y.toBase (schemeSpaceMap t)).obj.reprX
  let ι : schemeSpace X₀ ≅ pullback Y.toBase (schemeSpaceMap t) :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (pullback Y.toBase (schemeSpaceMap t)).obj.reprW
  obtain ⟨w, hw⟩ : ∃ w : X₀ ⟶ Q.siteObject,
      schemeSpaceMap w = ι.hom ≫ pullback.snd Y.toBase (schemeSpaceMap t) :=
    ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage _,
      (schemeSpaceFunctorFullyFaithful _ _).map_preimage _⟩
  have h₁ : IsPullback ι.hom (schemeSpaceMap w) (pullback.snd Y.toBase (schemeSpaceMap t))
      (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [hw, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz h
  rw [Category.id_comp] at h₂
  exact ⟨X₀, w, (ι.hom ≫ pullback.fst Y.toBase (schemeSpaceMap t)).hom,
    AlgebraicSpaces.isPullback_hom B integerBase hZ h₂⟩

/-- The fibres of a family of curves at the field-valued points over a point `s` of the base are
stable curves. -/
def HasStableFibresAt (Y : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y.base) : Prop :=
  ∀ Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj,
    (∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = s) →
    ∀ ⦃W : BigFppfOver B integerBase hZ⦄ (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ Y.total.obj),
      IsPullback r (yoneda.map w) Y.toBase.hom (yonedaEquiv.symm Q.value) →
        IsStableCurveOver Q.carrier ((BigFppfOver.toScheme B integerBase hZ).map w)

/-- **The base change of a family of curves to a field-valued point over `s` is stable**, when
the fibres over `s` are stable curves. -/
theorem isStableCurveFamily_curveFamilyOfIsPullback_of_hasStableFibresAt (Y : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y.base) (hY : HasStableFibresAt Y s)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj)
    (hQs : ∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = s)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ Y.total.obj)
    (hr : IsPullback r (yoneda.map w) Y.toBase.hom
      (yoneda.map (show Q.siteObject ⟶ Y.base from Q.value))) :
    IsStableCurveFamily B hZ
      (curveFamilyOfIsPullback Y Q.value _ _ (isPullback_homMk_of_isPullback _ w r hr)) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨hprop, hdim, hH0, hnodal, -⟩ := hY Q hQs w r (by rwa [yonedaEquiv_symm_value])
  have : LocallyOfFinitePresentation (T.map w) :=
    Y.locallyOfFinitePresentation_toScheme_map_of_isPullback
      (isPullback_homMk_of_isPullback _ w r hr)
  have : Nonempty (T.obj W) :=
    (connectedSpace_of_isIso_globalSections Q.carrier (T.map w)).toNonempty
  refine ⟨⟨?_, ?_⟩, fun p => ?_⟩
  · change Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ (yoneda.map w)
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget w).2 ?_
    exact (isAtWorstNodalOfRelativeDimensionOne_iff_of_field Q.carrier (T.map w)).2
      ⟨equidimensional_of_isIso_globalSections_of_dimension_one Q.carrier (T.map w) hdim, hdim,
        hnodal⟩
  · intro Y' g'
    have : PreservesLimitsOfShape WalkingCospan T :=
      Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
    exact bijective_globalFunctionsMap_fiberProduct_snd w
      (fun a pr m hsq' => bijective_appTop_of_isPullback (T.map w) (hsq'.map T)) Y' g'
  · let pv : p.siteObject ⟶ Q.siteObject := p.value
    let t : Q.siteObject ⟶ Y.base := Q.value
    let Q' : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj :=
      { carrier := p.carrier
        contained := p.contained
        toBase := p.toBase
        value := pv ≫ t }
    have hQ's : ∀ x, T.map Q'.value x = s := fun x => by
      change T.map (pv ≫ t) x = s
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hQs _
    have hV := IsPullback.of_hasPullback w pv
    refine ⟨pullback w pv, pullback.snd w pv, yoneda.map (pullback.fst w pv), ?_, ?_⟩
    · rw [yonedaEquiv_symm_value]
      exact hV.map yoneda
    · have hY' : IsPullback (yoneda.map (pullback.fst w pv) ≫ r) (yoneda.map (pullback.snd w pv))
          Y.toBase.hom (yonedaEquiv.symm Q'.value) := by
        change IsPullback _ _ _ (yoneda.map (pv ≫ t))
        rw [Functor.map_comp]
        exact (hV.map yoneda).paste_horiz hr
      exact (hY Q' hQ's (pullback.snd w pv) _ hY').2.2.2.2

attribute [local instance] Space.pointTopology in
/-- **Stability near a stable fibre.** If the stable locus is open (`h0E76`) and the fibres of `Y`
over the point `s` are stable curves, then there is an open neighbourhood `N` of `s` such that
every family of curves mapping to `Y` over a morphism of bases landing in `N` is stable. -/
theorem exists_isOpen_isStable_of_fibre
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (Y : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    (hY : HasStableFibresAt Y s) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj Y.base).Opens, s ∈ N ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ Y),
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ N →
          IsStableCurveFamily B hZ F := by
  let T := BigFppfOver.toScheme B integerBase hZ
  -- the residue field point
  have hκ : B.Contains (Spec ((T.obj Y.base).residueField s)) :=
    BigFppfSite.residueField_spec_contains B Y.base.left.2 s
  let ρ :=
    BigFppfOver.siteMapOver B integerBase hZ Y.base hκ ((T.obj Y.base).fromSpecResidueField s)
  let Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj :=
    { carrier := (T.obj Y.base).residueField s
      contained := hκ
      toBase := (T.obj Y.base).fromSpecResidueField s ≫ Y.base.hom.hom
      value := ρ }
  have hQs : ∀ x, T.map Q.value x = s := fun x =>
    (T.obj Y.base).fromSpecResidueField_apply s x
  obtain ⟨W, w, r, hr⟩ := exists_presentation_of_fieldValuedPoint Y Q
  rw [yonedaEquiv_symm_value] at hr
  obtain ⟨Wo, hWo, hchar⟩ := h0E76 Y
  obtain ⟨t₀, ht₀⟩ := (hchar _ (curveFamilyOfIsPullbackHom Y Q.value _ _
    (isPullback_homMk_of_isPullback _ w r hr))).1
    (isStableCurveFamily_curveFamilyOfIsPullback_of_hasStableFibresAt Y s hY Q hQs w r hr)
  refine ⟨⟨Space.pointsToScheme B integerBase hZ Y.base ''
      Set.range (Space.pointsMap B integerBase hZ Wo.toFunctor Wo.ι),
    (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B integerBase hZ Y.base _).1
      (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
        (schemeSpace Y.base).2 Wo hWo)⟩, ?_, ?_⟩
  · have hfac := (Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace Y.base).2 (isAlgebraicSpace_yoneda B integerBase hZ Q.siteObject) Wo hWo
      (yoneda.map (show Q.siteObject ⟶ Y.base from Q.value))).1 ⟨t₀, ht₀⟩
    obtain ⟨x₀⟩ : Nonempty (Space.points B integerBase hZ (yoneda.obj Q.siteObject)) :=
      ⟨(Space.pointsEquivScheme B integerBase hZ Q.siteObject).symm
        (IsLocalRing.closedPoint _)⟩
    exact ⟨_, hfac ⟨x₀, rfl⟩,
      (Space.pointsToScheme_pointsMap_yoneda B integerBase hZ ρ x₀).trans (hQs _)⟩
  · intro F a ha
    refine (hchar F a).2 ((Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace Y.base).2 (isAlgebraicSpace_yoneda B integerBase hZ F.base) Wo hWo
      (schemeSpaceMap a.baseMap).hom).2 ?_)
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, hzy⟩ := ha ⟨Space.pointsToScheme B integerBase hZ F.base y, rfl⟩
    rw [← Space.pointsToScheme_pointsMap_yoneda] at hzy
    rwa [Space.injective_pointsToScheme B integerBase hZ Y.base hzy] at hz

end AlgebraicGeometry.C1590Private

end
