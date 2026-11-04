module

public import StacksFrontier.AlgebraicGeometry.Curves.StableLocus.StableCurveLocus
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.GeometricFibresDirectImage
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# A family of schemes with stable fibres of genus `g` is a point of `𝓜̄_g`

Let `p : X ⟶ S` be a proper, flat morphism of finite presentation between schemes of the big fppf
site whose fibre over every field-valued point of `S` is a stable curve of genus `g ≥ 2`
(`AlgebraicGeometry.IsStableCurveOfGenusOverField`). Then the family of curves it defines is
stable with fibres of genus `g` (`AlgebraicGeometry.IsStableCurveFamilyOfFibreGenus`), so it is an
object of `𝓜̄_g` over `S`.

The fibres are at-worst-nodal of dimension one, so `p` is at-worst-nodal of relative dimension one
(Stacks 0C59), which is the nodal condition of prestability on every étale chart. They are
geometrically connected, so `p_*𝒪_X = 𝒪_S` universally (Stacks 0E0L), which is the second
condition of prestability once it is tested on schemes. The fibre conditions of stability and of
genus are read off the fibres of `p` over the field-valued points.

## Main results

* `AlgebraicGeometry.isCurveFamilyOfSchemesWith_isStableCurveFamilyOfFibreGenus`.

## References

* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The family of a morphism of schemes with stable fibres of genus `g` lies in `𝓜̄_g`.** Let
`p : X ⟶ S` be proper, flat and of finite presentation, with `S` in the big fppf site, and suppose
that the fibre of `p` over every field-valued point `Spec K ⟶ S` is a stable curve of genus
`g ≥ 2`. Then `p` is a family of curves which is stable with every fibre of genus `g`. -/
theorem isCurveFamilyOfSchemesWith_isStableCurveFamilyOfFibreGenus {g : ℕ} (hg : 2 ≤ g)
    {X S : Scheme.{u}} (p : X ⟶ S) (hS : B.Contains S) [IsProper p] [Flat p]
    [LocallyOfFinitePresentation p]
    (hst : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (q : V ⟶ X) (fV : V ⟶ Spec (CommRingCat.of K)) [IsProper fV], IsPullback q fV p y →
      IsStableCurveOfGenusOverField K fV g) :
    IsCurveFamilyOfSchemesWith B hZ (IsStableCurveFamilyOfFibreGenus B hZ g) p hS := by
  have hnod : IsAtWorstNodalOfRelativeDimensionOne p := by
    refine (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff p).mp
      ⟨inferInstance, inferInstance, fun s _ => ?_⟩
    obtain ⟨hnodal, hdim, hH0, -, -⟩ := @hst (S.residueField s) _ (p.fiber s)
      (S.fromSpecResidueField s) (p.fiberι s) (p.fiberToSpecResidueField s)
      (MorphismProperty.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback p (S.fromSpecResidueField s)) inferInstance)
      (IsPullback.of_hasPullback p _)
    have : ConnectedSpace (p.fiber s) :=
      @connectedSpace_of_isIso_globalSections (S.residueField s) _ (p.fiber s) _ hH0
    have : IsLocallyNoetherian (p.fiber s) :=
      LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField s)
    have : CompactSpace (p.fiber s) :=
      QuasiCompact.compactSpace_of_compactSpace (p.fiberToSpecResidueField s)
    have : IsNoetherian (p.fiber s) := ⟨⟩
    exact ⟨equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim, hdim, hnodal⟩
  have hgc : GeometricallyConnected p := by
    refine ⟨fun K _ y Z q fZ sq => ?_⟩
    have : IsProper fZ := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    obtain ⟨-, -, hH0, -, -⟩ := hst K Z y q fZ sq
    exact @connectedSpace_of_isIso_globalSections K _ Z _ hH0
  have := hgc
  have hfib : ∀ x, topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) ≤ 1 := by
    intro x
    obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff p).mpr hnod
    obtain ⟨heq, hdim, -⟩ := h (p x) ⟨p.asFiber x⟩
    have hLFT : LocallyOfFiniteType (p.fiberToSpecResidueField (p x)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback p _)
        inferInstance
    exact (@Stacks.Curves.topologicalKrullDimAt_eq_one_of_equidimensional _ _ _
      (p.fiberToSpecResidueField (p x)) hLFT heq hdim _).le
  refine ⟨inferInstance, inferInstance, inferInstance, hfib, ?_⟩
  have hX : B.Contains X := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS
  have : Flat ((BigFppfOver.toScheme B integerBase hZ).map (integerSiteMap B hZ hX hS p)) :=
    ‹Flat p›
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map (integerSiteMap B hZ hX hS p)) :=
    ‹IsProper p›
  have : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B integerBase hZ).map (integerSiteMap B hZ hX hS p)) :=
    ‹LocallyOfFinitePresentation p›
  set F := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS) hS p) inferInstance
    inferInstance inferInstance hfib with hF
  have : GeometricallyReduced p :=
    geometricallyReduced_of_isAtWorstNodalOfRelativeDimensionOne p hnod
  -- prestability
  have hnodF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
      (integerSiteMap B hZ hX hS p)).2 hnod
  have hH0F : HasUniversallyBijectiveGlobalFunctions B hZ F := by
    refine CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_forall_schemeSpace fun T t => ?_
    obtain ⟨T, hT, rfl⟩ : ∃ (T' : Scheme.{u}) (hT : B.Contains T'),
        T = integerSiteObject B hZ hT := by
      obtain ⟨⟨T', hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
      exact ⟨T', hT, congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))⟩
    obtain ⟨t₀, rfl⟩ : ∃ t₀ : integerSiteObject B hZ hT ⟶ F.base, schemeSpaceMap t₀ = t :=
      ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage t,
        (schemeSpaceFunctorFullyFaithful _ _).map_preimage t⟩
    set φ : T ⟶ S := (BigFppfOver.toScheme B integerBase hZ).map t₀ with hφ
    have ht₀ : integerSiteMap B hZ hT hS φ = t₀ := integerSiteMap_toScheme_map (hT' := hS) t₀
    have hP : B.Contains (pullback p φ) :=
      Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd p φ) hT
    have hsq := isPullback_schemeSpaceMap_integerSiteMap (B := B) (hZ := hZ) (hP := hP)
      (hQ := hX) (hR := hT) (hW := hS) (IsPullback.of_hasPullback p φ)
    rw [ht₀] at hsq
    let e := (IsPullback.of_hasPullback F.toBase (schemeSpaceMap t₀)).isoIsPullback _ _ hsq
    set ψ := integerSiteMap B hZ hP hT (pullback.snd p φ)
    have he : e.hom ≫ schemeSpaceMap ψ = pullback.snd _ _ :=
      IsPullback.isoIsPullback_hom_snd _ _ _ _
    rw [← he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
    refine Function.Bijective.comp (CurveFamily.globalFunctionsMap_bijective_of_iso e) ?_
    have hc' : IsIso (pullback.snd p φ).c :=
      (Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.isIso_c_and_isIso_c_of_isPullback p).2
        (IsPullback.of_hasPullback p φ)
    have hΓ := (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff _).1 hc' ⊤
    refine (Function.Bijective.of_comp_iff' (Space.globalFunctionsYonedaRingEquiv B integerBase hZ
      (integerSiteObject B hZ hP)).bijective _).1 ?_
    refine Eq.mp (congrArg Function.Bijective (funext fun s => ?_))
      (hΓ.comp (Space.globalFunctionsYonedaRingEquiv B integerBase hZ
        (integerSiteObject B hZ hT)).bijective)
    exact (Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap B integerBase hZ ψ s).symm
  -- the fibre over a field-valued point is a stable curve of genus `g`
  have key : ∀ q : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ q.siteObject)
        (r : yoneda.obj V ⟶ F.total.obj),
        IsPullback r (yoneda.map v) F.toBase.hom (yonedaEquiv.symm q.value) ∧
        HasGenusTwoNoRationalTailNoRationalBridge q.carrier
          ((BigFppfOver.toScheme B integerBase hZ).map v) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g := by
    intro q
    obtain ⟨V, v, r, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ F q
    have hsq' : IsPullback r.hom (yoneda.map v) F.toBase.hom (yonedaEquiv.symm q.value) :=
      AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
    have hval : yonedaEquiv.symm q.value = yoneda.map q.value :=
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
    have hsq'' := hsq'
    rw [hval] at hsq''
    have hsch := isPullback_toScheme_of_isPullback_yoneda
      (c := integerSiteMap B hZ hX hS p) hsq''
    have hPv : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
      MorphismProperty.of_isPullback (P := @IsProper) hsch inferInstance
    have hstab := hst q.carrier _ _ _ _ hsch
    exact ⟨V, v, r.hom, hsq', hstab.hasGenusTwoNoRationalTailNoRationalBridge hg⟩
  refine ⟨⟨⟨hnodF, hH0F⟩, fun q => ?_⟩, fun q => ?_⟩
  · obtain ⟨V, v, r, hr, hV, -⟩ := key q
    exact ⟨V, v, r, hr, hV⟩
  · obtain ⟨V, v, r, hr, -, hV⟩ := key q
    exact ⟨V, v, r, hr, hV⟩

end AlgebraicGeometry

end
