module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingComplexAmplitude
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableFibresOpenOfInvertibleDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.SingleDegreeFreeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology

/-!
# The relative dualizing sheaf of an at-worst-nodal family is invertible

Let `f : X → S` be a family of curves over an affine base which is at-worst-nodal of relative
dimension one, and `ω^•_{X/S} = a(𝒪_S)` its relative dualizing complex. Then
`ω^•_{X/S} ≅ ω_{X/S}[1]` with `ω_{X/S} = H^{-1}(ω^•_{X/S})` an invertible `𝒪_X`-module: this is
Stacks 0E6P (for at-worst-nodal families) and the invertibility clause of Stacks 0E6R.

## Main results

* `CurveFamily.isFreeOfRankInDegree_smallEtaleDerivedModulePullback_affineDualizingComplex`: the
  derived fibres of `ω^•_{X/S}` at field-valued points are `𝒪[1]`.
* `AlgebraicGeometry.CurveFamily.isFiniteLocallyFreeOfIntRankInDegree_affineDualizingComplex`:
  `ω^•_{X/S}` is an invertible module placed in degree `-1`.
* `AlgebraicGeometry.CurveFamily.isInvertible_homology_affineDualizingComplex`: `ω_{X/S}` is
  invertible.
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocusWithin_hasStableFibres`: within prestable
  families, having stable fibres is an open condition (Stacks 0E74, condition (o) within the
  prestable families).

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- The sheafification instances of the small étale sites are put first, since instance search
-- otherwise gets stuck on the universe constraints of the general ones.
open scoped Stacks.StandardDerivedModel

attribute [local instance 5000] SheafOfModules.instAbelian
  AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective
  AlgebraicGeometry.Space.SmallEtale.instHasSheafifyOver
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijectiveOver

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An invertible module on an algebraic space is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    (hL : IsInvertibleModule Z L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank.{u, u, u + 1} L 1 := by
  have h₁ := (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).1 hL
  have h₂ := (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfIntRank_natCast_iff L 1).2
    (RingedSite.isFiniteLocallyFreeOfRank_sheafOfModules (smallEtaleRingedSite B S hS Z.1 Z.2)
      L h₁)
  rwa [Nat.cast_one] at h₂

/-- **A module of rank one placed in one degree has an invertible cohomology sheaf there.** If
`E ≅ M[-n]` with `M` finite locally free of rank one, then `H^n(E) ≅ M` is invertible. -/
theorem isInvertibleModule_homology_of_isFiniteLocallyFreeOfIntRankInDegree
    (Z : AlgebraicSpaces B S hS) (E : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (n : ℤ)
    (h : IsFiniteLocallyFreeOfIntRankInDegree B S hS Z E n 1) :
    IsInvertibleModule Z ((DerivedCategory.homologyFunctor _ n).obj E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  have hM₁ := (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfIntRank_natCast_iff M 1).1
    (by rwa [Nat.cast_one])
  have hR := RingedSite.isFiniteLocallyFreeOfRank_of_sheafOfModules
    (smallEtaleRingedSite B S hS Z.1 Z.2) M 1 hM₁
  have : IsInvertibleModule Z M := (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one M).2 hR
  let e' : M ≅ (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) n).obj E :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app M).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso e.symm
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ e'

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The derived fibres of the relative dualizing complex are `𝒪[1]`.** For an at-worst-nodal
family of curves `X → S` over an affine base and a field-valued point `t : Spec k → X`, the
derived pullback `Lt^* ω^•_{X/S}` is the structure sheaf placed in degree `-1`. -/
theorem isFreeOfRankInDegree_smallEtaleDerivedModulePullback_affineDualizingComplex
    (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom)
    (t : Space.FieldValuedPoint B integerBase hZ G.total.obj) :
    Space.IsFreeOfRankInDegree
      ((Space.smallEtaleDerivedModulePullback B integerBase hZ t.toSpace).obj
        (affineDualizingComplex G hA).obj) (-1) 1 := by
  let p := t.map B integerBase hZ G.total.obj G.toBase.hom
  obtain ⟨V, v, q, h⟩ := exists_isPullback_fieldPointPresentation G p
  have hw : yonedaEquiv.symm t.value ≫ G.toBase.hom = 𝟙 _ ≫ yonedaEquiv.symm p.value := by
    rw [Category.id_comp]
    exact yonedaEquiv_symm_naturality_right _ _ _
  let t' : schemeSpace t.siteObject ⟶ schemeSpace V :=
    ObjectProperty.homMk (h.lift (yonedaEquiv.symm t.value) (𝟙 _) hw)
  let qs : schemeSpace V ⟶ G.total := ObjectProperty.homMk q
  have ht : t.toSpace = t' ≫ qs := ObjectProperty.hom_ext _ (h.lift_fst _ _ hw).symm
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    isProper_of_isPullback_fieldValuedPoint (isPullback_schemeSpace_of_isPullback_yoneda h)
  let EV := (Space.smallEtaleDerivedModulePullback B integerBase hZ qs).obj
    (affineDualizingComplex G hA).obj
  obtain ⟨eV⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero EV (-1)
    fun n hn => isZero_homology_smallEtaleDerivedModulePullback_affineDualizingComplex G hA hG p
      V v q h n hn
  let M := (DerivedCategory.homologyFunctor
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) (-1)).obj EV
  have sq := isPullback_fieldPointPresentation h
  have hP := isAffineSpace_fieldPoint (G := G) p
  obtain ⟨e, -⟩ := (affineRelativeDualizingComplex G hA).isAffineBaseChangePair
    (schemeSpaceMap v) _ _ sq hP
  have hqc : M.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ (-1)).mapIso e).symm
      (((Space.affineBaseChangeRightAdjoint B.contains_terminal sq G.finitePresentation hP).obj
        (Space.derivedStructureSheaf B integerBase hZ _ _)).property (-1))
  let Φ := Space.representedQuasicoherentSchemeEquivalence B integerBase hZ V
  let Mq : Space.QuasicoherentSheaves.{u, u} B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V) := ⟨M, hqc⟩
  let M₀ := Φ.inverse.obj Mq
  let eM : (Φ.functor.obj M₀).obj ≅ M := (ObjectProperty.ι _).mapIso (Φ.counitIso.app Mq)
  obtain ⟨e'⟩ := nonempty_homology_derivedPullback_affineDualizingComplex_iso G hA p V v q h (-1)
  let e₀ : M₀.obj ≅ Stacks.Duality.dualizingSheafOverField
      ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    (Space.restrictToChart_selfChart_representedQuasicoherentIso B integerBase hZ V M₀.obj
        M₀.property).symm ≪≫
      Space.restrictToChartIsoRestrictToChartScheme B integerBase hZ
        (isAlgebraicSpace_yoneda B integerBase hZ V) (Φ.functor.obj M₀).obj
        (Space.idEtaleChart B integerBase hZ V) ≪≫
      (Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
        (isAlgebraicSpace_yoneda B integerBase hZ V) (Space.idEtaleChart B integerBase hZ V)).mapIso
        eM ≪≫ e'
  let w : t.siteObject ⟶ V := Yoneda.fullyFaithful.preimage t'.hom
  have : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj V) :=
    ⟨(BigFppfOver.toScheme B integerBase hZ).map w (IsLocalRing.closedPoint t.carrier)⟩
  have hω := (isInvertible_dualizingSheafOverField_of_isAtWorstNodal hG h).1
  have : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B integerBase hZ).obj V).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _) M₀.obj :=
    have : Stacks.SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B integerBase hZ).obj V).presheaf
        (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _)
        (Stacks.Duality.dualizingSheafOverField ((BigFppfOver.toScheme B integerBase hZ).map v)) :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hω
    Stacks.SheafOfModules.isInvertible_of_iso _ _ e₀.symm
  have hM₀ : Space.IsInvertibleModule (schemeSpace V) (Φ.functor.obj M₀).obj :=
    Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B integerBase hZ V M₀.obj inferInstance
  have hM : Space.IsInvertibleModule (schemeSpace V) M :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ eM
  have hflat := Space.isFlat_of_isFiniteLocallyFreeOfIntRank B integerBase hZ M
    (Space.isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule _ M hM)
  obtain ⟨e₁⟩ := Space.nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso t' M (-1)
    hflat
  have hpinv : Space.IsInvertibleModule (schemeSpace t.siteObject)
      (((Space.smallEtaleRingedToposHom B integerBase hZ t').toModulesHom.pullbackModules).obj
        M) := by
    rw [Space.pullbackModules_eq_modulePullback]
    exact Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Space.isInvertible_modulePullback_obj B integerBase hZ t' M hM.toAlgebraicGeometry)
  obtain ⟨eu⟩ := Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top B integerBase hZ
    t.siteObject (R := CommRingCat.of t.carrier) rfl (IsLocalRing.closedPoint t.carrier)
    (forall_eq_top_of_mem_of_isLocalRing _) _ _ hpinv
  refine ⟨1, Nat.cast_one, ⟨?_⟩⟩
  rw [ht]
  exact ((Space.smallEtaleDerivedPullbackCompIsoOfTwoIso B integerBase hZ t' qs).app _).symm ≪≫
    (Space.smallEtaleDerivedModulePullback B integerBase hZ t').mapIso eV ≪≫ e₁ ≪≫
    (DerivedCategory.singleFunctor _ (-1)).mapIso
      (eu ≪≫ (Stacks.SheafOfModules.Invertible.freeUniqueIso _).symm)

/-- **Stacks 0E6P for at-worst-nodal families over an affine base:** the relative dualizing
complex `ω^•_{X/S}` is a finite locally free module of rank one placed in degree `-1`. -/
theorem isFiniteLocallyFreeOfIntRankInDegree_affineDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom) :
    Space.IsFiniteLocallyFreeOfIntRankInDegree B integerBase hZ G.total
      (affineDualizingComplex G hA).obj (-1) 1 := by
  have hqc := Space.isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B integerBase hZ
    G.toBase G.finitePresentation.2.1 (isAffineSpace_schemeSpace_base G hA)
  have hpc := (Space.isPerfectRelativeToCanonical_affineRightAdjoint B.contains_terminal G.toBase
    G.proper G.flat G.finitePresentation (isAffineSpace_schemeSpace_base G hA)).1
  exact Space.isFiniteLocallyFreeOfIntRankInDegree_of_forall_fieldValuedPoint G.total hqc _ hpc
    (-1) 1 fun t =>
      isFreeOfRankInDegree_smallEtaleDerivedModulePullback_affineDualizingComplex G hA hG t

/-- **The relative dualizing sheaf of an at-worst-nodal family over an affine base is
invertible** (Stacks 0E6R): `ω_{X/S} = H^{-1}(ω^•_{X/S})` is an invertible `𝒪_X`-module. -/
theorem isInvertible_homology_affineDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ G.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ G.total.1 G.total.2).O)).property
      ((DerivedCategory.homologyFunctor
        (Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2) (-1)).obj
          (G.affineDualizingComplex hA).obj) :=
  Space.isInvertibleModule_homology_of_isFiniteLocallyFreeOfIntRankInDegree G.total _ (-1)
    (isFiniteLocallyFreeOfIntRankInDegree_affineDualizingComplex G hA hG)

/-- **Condition (o) for stable fibres within prestable families** (Stacks 0E74, within the
prestable families): the prestable families of curves whose fibres are stable form an open
locus within the prestable families. -/
theorem isOpenCurvesLocusWithin_hasStableFibres :
    IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ) :=
  isOpenCurvesLocusWithin_hasStableFibres_of_isInvertible_affineDualizingSheaf
    fun G hA hG => isInvertible_homology_affineDualizingComplex G hA hG

end AlgebraicGeometry.CurveFamily

end
