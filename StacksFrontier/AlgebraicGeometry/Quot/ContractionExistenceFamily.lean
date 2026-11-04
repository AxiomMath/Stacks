module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionExistenceComplete
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyCompleteLocalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingFamily
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# Contractions of families of curves over a complete local ring

Stacks 0E7C for families of curves (Stacks 0D4Z): over the spectrum of a complete Noetherian
local ring `Λ`, a family of curves `F` whose closed fibre `X₀` admits a contraction
`h₀ : X₀ ⟶ Y₀` (`𝒪_{Y₀} ≅ h₀,*𝒪_{X₀}`, `R¹h₀,*𝒪_{X₀} = 0`, `Y₀` proper) is the source of a
morphism `F ⟶ G` to a family of curves `G` over `Spec Λ` whose closed fibre is `h₀`.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_contraction_of_isAdicComplete`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- An étale-chart condition is unchanged by an isomorphism of the source. -/
theorem holdsOnEveryEtaleChart_iso_comp {S : Scheme.{u}} {hS : B.Contains S}
    (P : MorphismProperty Scheme.{u}) {F' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F' ≅ F)
    (f : F ⟶ G) (hf : Space.HoldsOnEveryEtaleChart B S hS P f) :
    Space.HoldsOnEveryEtaleChart B S hS P (e.hom ≫ f) := by
  let Et := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  intro U V j k l hj hk hcomm
  apply hf U V (j ≫ e.hom) k l ((Et.cancel_right_of_respectsIso j e.hom).2 hj) hk
  rw [hcomm, Category.assoc]

/-- A cartesian square of representable presheaves of morphisms of the site is a cartesian square
of the underlying schemes. -/
theorem isPullback_toScheme_of_isPullback_yoneda {P Q R W : BigFppfOver B integerBase hZ}
    {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ W} {d : R ⟶ W}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map a)
      ((BigFppfOver.toScheme B integerBase hZ).map b)
      ((BigFppfOver.toScheme B integerBase hZ).map c)
      ((BigFppfOver.toScheme B integerBase hZ).map d) := by
  have hU : IsPullback a b c d :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h.w)) h
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B _ hZ
  exact hU.map (BigFppfOver.toScheme B integerBase hZ)

/-- The structure morphism of a family read over its own base is the structure morphism. -/
theorem toBaseYonedaOfEq_rfl (F : CurveFamily B hZ) : F.toBaseYonedaOfEq rfl = F.toBase.hom := by
  simp [toBaseYonedaOfEq, ofBaseEq]
  rfl

open ContractionUniquenessComplete in
/-- **Stacks 0E7C over a complete Noetherian local ring, for families of curves.** Let `Λ` be a
complete Noetherian local ring with residue field `κ` and closed point `s`, and `F` a family of
curves over `Spec Λ` whose closed fibre is the scheme `X₀` (the cartesian square `ι`). Let
`h₀ : X₀ ⟶ Y₀` be a morphism over `κ` to a proper scheme with `𝒪_{Y₀} ≅ h₀,*𝒪_{X₀}` and
`R¹h₀,*𝒪_{X₀} = 0`. Then there are a family of curves `G` over `Spec Λ`, a morphism `h` from the
total space of `F` to that of `G` over `Spec Λ`, and an identification `j` of `Y₀` with the closed
fibre of `G` under which `h` restricts to `h₀`. -/
theorem exists_contraction_of_isAdicComplete
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (hΛ : B.Contains (Spec (.of Λ))) (hκ : B.Contains (Spec (.of (ResidueField Λ))))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hΛ)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of (ResidueField Λ)))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ hκ hΛ (closedPoint Λ))))
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ)))
    [IsProper pY₀] (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ (G : CurveFamily B hZ) (hG : G.base = integerSiteObject B hZ hΛ)
      (h : F.total.obj ⟶ G.total.obj), h ≫ G.toBaseYonedaOfEq hG = F.toBaseYonedaOfEq hF ∧
      ∃ j : yoneda.obj (integerSiteObject B hZ hY₀) ⟶ G.total.obj,
        IsPullback j (yoneda.map (integerSiteMap B hZ hY₀ hκ pY₀)) (G.toBaseYonedaOfEq hG)
          (yoneda.map (integerSiteMap B hZ hκ hΛ (closedPoint Λ))) ∧
        ι ≫ h = yoneda.map (integerSiteMap B hZ hX₀ hY₀ h₀) ≫ j := by
  obtain ⟨X, hX, fX, hprojX, eX, heX⟩ := exists_iso_schemeSpace_of_isAdicComplete Λ hΛ F hF
  have : IsProper fX := isProper_of_isProjectiveMorphism fX hprojX
  have sq : IsPullback (ι ≫ eX.hom) (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀))
      (yoneda.map (integerSiteMap B hZ hX hΛ fX))
      (yoneda.map (integerSiteMap B hZ hκ hΛ (closedPoint Λ))) :=
    hι.of_iso (Iso.refl _) eX (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, heX]) (by simp)
  let ιXs : integerSiteObject B hZ hX₀ ⟶ integerSiteObject B hZ hX := yoneda.preimage (ι ≫ eX.hom)
  have hιXs : yoneda.map ιXs = ι ≫ eX.hom := yoneda.map_preimage _
  rw [← hιXs] at sq
  let ιX : X₀ ⟶ X := (BigFppfOver.toScheme B integerBase hZ).map ιXs
  have hιX : IsPullback ιX pX₀ fX (closedPoint Λ) := isPullback_toScheme_of_isPullback_yoneda sq
  have hdimX₀ : topologicalKrullDim X₀ ≤ 1 := by
    set σ := integerSiteMap B hZ hκ hΛ (closedPoint Λ)
    have sq0 := (F.isPullback_pullbackHom_yoneda hF σ)
    let e0 : yoneda.obj (integerSiteObject B hZ hX₀) ≅ ((F.ofBaseEq hF).pullback σ).total.obj :=
      hι.isoIsPullback _ _ sq0
    obtain ⟨X0', hX0'p, hdim0, ⟨φ⟩⟩ :=
      exists_iso_curveFamilyOfScheme_of_base_eq hκ ((F.ofBaseEq hF).pullback σ) rfl
    have := hX0'p
    let eTot : ((F.ofBaseEq hF).pullback σ).total ≅
        (curveFamilyOfScheme X0' B hZ hκ hdim0).total :=
      { hom := φ.hom.totalMap
        inv := φ.inv.totalMap
        hom_inv_id := by rw [← comp_totalMap, φ.hom_inv_id, id_totalMap]
        inv_hom_id := by rw [← comp_totalMap, φ.inv_hom_id, id_totalMap] }
    let e1 : yoneda.obj (integerSiteObject B hZ hX₀) ≅ yoneda.obj (integerSiteObject B hZ
        (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X0'.hom hκ)) :=
      e0 ≪≫ (ObjectProperty.ι _).mapIso eTot
    let e2 := (BigFppfOver.toScheme B integerBase hZ).mapIso (Yoneda.fullyFaithful.preimageIso e1)
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e2).isHomeomorph).trans_le
      hdim0
  have : Flat fX := by
    have hflat : Space.HoldsOnEveryEtaleChart B integerBase hZ (@Flat.{u})
        (yoneda.map (integerSiteMap B hZ hX hΛ fX)) := by
      have : yoneda.map (integerSiteMap B hZ hX hΛ fX) = eX.inv ≫ F.toBaseYonedaOfEq hF := by
        rw [← heX, Iso.inv_hom_id_assoc]
      rw [this]
      exact holdsOnEveryEtaleChart_iso_comp _ eX.symm _ (F.ofBaseEq hF).flat
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      Flat.isEtaleLocalOnSourceAndTarget _).1 hflat
  obtain ⟨Y, fY, hprojY, hflatY, h, hh, j, hj, hιh⟩ :=
    ContractionExistenceComplete.exists_contraction_of_specialFibre_of_isAdicComplete'
      inferInstance fX pX₀ hιX hdimX₀ h₀ pY₀ hh₀ h0 hR
  have : IsProper fY := isProper_of_isProjectiveMorphism fY hprojY
  have := hflatY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have : LocallyOfFinitePresentation fY := inferInstance
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fY hΛ
  have hfib : ∀ y, fY.fiberDimension y ≤ 1 := by
    have hfp : FinitePresentation fY := ⟨inferInstance, inferInstance, inferInstance⟩
    refine fiberDimension_le_of_fiberDimension_closedPoint_le fY hfp ?_
    set pt₀ : Spec (.of (ResidueField Λ)) := IsLocalRing.closedPoint (ResidueField Λ)
    have e2 : pY₀.fiberDimension pt₀ = fY.fiberDimension
        ((ContractionUniquenessComplete.closedPoint Λ) pt₀) :=
      congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hj) pt₀
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (residue Λ))) :=
      inferInstanceAs (IsLocalHom (residue Λ))
    have hpt : (ContractionUniquenessComplete.closedPoint Λ) pt₀ =
        (IsLocalRing.closedPoint Λ : Spec (.of Λ)) :=
      Spec_closedPoint
    rw [hpt] at e2
    refine e2.symm.trans_le ?_
    refine ((IsHomeomorph.topologicalKrullDim_eq _ (pY₀.fiberHomeo pt₀).isHomeomorph).trans_le
      (Topology.IsInducing.topologicalKrullDim_le Topology.IsInducing.subtypeVal)).trans ?_
    have : IsProper pX₀ := MorphismProperty.of_isPullback (P := @IsProper) hιX
      (inferInstanceAs (IsProper fX))
    have : IsProper (h₀ ≫ pY₀) := by rw [hh₀]; exact (inferInstance : IsProper pX₀)
    have : IsProper h₀ := IsProper.of_comp h₀ pY₀
    exact ((ContractionExistenceComplete.topologicalKrullDim_le_of_isIso_unitToPushforwardUnit
      h₀ h0).trans hdimX₀)
  let G := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hΛ fY) hflatY
    (inferInstanceAs (IsProper fY)) (inferInstanceAs (LocallyOfFinitePresentation fY))
    fun x => (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hfib _)
  have eG : G.toBaseYonedaOfEq rfl = yoneda.map (integerSiteMap B hZ hY hΛ fY) :=
    toBaseYonedaOfEq_rfl G
  have key1 : (eX.hom ≫ yoneda.map (integerSiteMap B hZ hX hY h)) ≫
      yoneda.map (integerSiteMap B hZ hY hΛ fY) = F.toBaseYonedaOfEq hF := by
    rw [Category.assoc, ← Functor.map_comp, ← heX, integerSiteMap_comp, hh]
  have key3 : (ι ≫ eX.hom) ≫ yoneda.map (integerSiteMap B hZ hX hY h) =
      yoneda.map (integerSiteMap B hZ hX₀ hY₀ h₀) ≫ yoneda.map (integerSiteMap B hZ hY₀ hY j) := by
    rw [← hιXs, ← Functor.map_comp, ← Functor.map_comp, integerSiteMap_comp, ← hιh,
      ← integerSiteMap_comp, integerSiteMap_toScheme_map]
  exact ⟨G, rfl, eX.hom ≫ yoneda.map (integerSiteMap B hZ hX hY h),
    (congrArg (fun x => (eX.hom ≫ yoneda.map (integerSiteMap B hZ hX hY h)) ≫ x) eG).trans key1,
    yoneda.map (integerSiteMap B hZ hY₀ hY j),
    AlgebraicSpaces.isPullback_hom B integerBase hZ (isPullback_schemeSpaceMap_integerSiteMap hj),
    (Category.assoc ι eX.hom _).symm.trans key3⟩

end CurveFamily

end AlgebraicGeometry

end
