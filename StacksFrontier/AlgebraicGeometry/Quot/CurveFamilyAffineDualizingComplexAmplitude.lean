module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingComplexNodalFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AmplitudeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEquivalenceHomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexAffinePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove

/-!
# The relative dualizing complex of an at-worst-nodal family lies in degrees `≤ -1`

Let `f : X → S` be a family of curves over an affine base which is at-worst-nodal of relative
dimension one, and `ω^•_{X/S} = a(𝒪_S)` its relative dualizing complex. Then `ω^•_{X/S}` has no
cohomology above degree `-1`: this is the upper half of the first assertion of Stacks 0E6P
("`ω^•_{X/S}` is … `ω_{X/S}[1]`").

The proof is the one of the source: `ω^•_{X/S}` is `S`-perfect (Stacks 0E5V), in particular
pseudo-coherent, so its amplitude is detected at the field-valued points of `X`
(`AlgebraicGeometry.Space.isLE_of_isPseudoCoherent_of_forall_fieldValuedPoint_isLE`). A field
point `Spec k → X` factors through the fibre `X_k`, which is a scheme `V`
(`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), and the derived pullback of
`ω^•_{X/S}` to `V` is the dualizing complex `ω_V^•` of the nodal curve `V` (Section 0E6N), whose
cohomology is concentrated in degree `-1`
(`AlgebraicGeometry.CurveFamily.isZero_homology_derivedPullback_affineDualizingComplex`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isPullback_fieldPointPresentation`: every fibre over a
  field-valued point is presented by a scheme.
* `CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_affineDualizingComplex`:
  the derived pullback of `ω^•_{X/S}` to a fibre is concentrated in degree `-1`.
* `AlgebraicGeometry.CurveFamily.isLE_affineDualizingComplex`: `ω^•_{X/S} ∈ D^{≤ -1}`.

## Implementation notes

Unregistered helpers towards Stacks 0E6P for at-worst-nodal families.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
* [Stacks Project, Tag 0E5V](https://stacks.math.columbia.edu/tag/0E5V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.CurveFamily

-- The same choice of models as `AlgebraicGeometry.CurveFamily.affineDualizingComplex`; the scoped
-- standard model leaves universe constraints of the module categories on small étale sites stuck.
attribute [local instance low] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective



variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Every fibre of a family of curves over a field-valued point is presented by a scheme.** For
a field-valued point `Spec K → S` of the base, the fibre `X ×_S Spec K` is a scheme `V`
(`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), giving a cartesian square
`V → X` over `Spec K → S`. -/
theorem exists_isPullback_fieldPointPresentation (G : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ G.total.obj),
      IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value) := by
  let g : p.siteObject ⟶ G.base := p.value
  let F := G.baseChange g
  have hrep : F.total.obj.IsRepresentable :=
    F.isRepresentable_total_of_base_eq (K := p.carrier) rfl
  let V := F.total.obj.reprX
  let w : yoneda.obj V ≅ F.total.obj := F.total.obj.reprW
  have hp : yonedaEquiv.symm p.value = yoneda.map g :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map g).symm
  let v : V ⟶ p.siteObject :=
    Yoneda.fullyFaithful.preimage (w.hom ≫ pullback.snd G.toBase.hom (schemeSpaceMap g).hom)
  refine ⟨V, v, w.hom ≫ pullback.fst G.toBase.hom (schemeSpaceMap g).hom, ?_⟩
  have hv : yoneda.map v = w.hom ≫ pullback.snd G.toBase.hom (schemeSpaceMap g).hom :=
    Yoneda.fullyFaithful.map_preimage _
  rw [hp]
  refine IsPullback.of_iso_pullback ⟨?_⟩ w rfl hv.symm
  exact (Category.assoc _ _ _).trans ((congrArg (w.hom ≫ ·) pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map g) hv.symm)))

/-- **The derived pullback of the relative dualizing complex to a fibre is concentrated in degree
`-1`** (Section 0E6N), on the small étale site of the scheme `V` presenting the fibre: the
cohomology sheaves of `Lq^* ω^•_{X/S}` lie in `D_QCoh` and vanish on the Zariski site of `V`
outside degree `-1`
(`AlgebraicGeometry.CurveFamily.isZero_homology_derivedPullback_affineDualizingComplex`), so they
vanish (`AlgebraicGeometry.Space.isZero_homology_of_isZero_restrictToChartScheme_homology`). -/
theorem isZero_homology_smallEtaleDerivedModulePullback_affineDualizingComplex
    (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ G.total.obj)
    (h : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) (n : ℤ)
    (hn : n ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).obj
        ((Space.smallEtaleDerivedModulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ G.total)).obj
            (affineDualizingComplex G hA).obj)) := by
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    isProper_of_isPullback_fieldValuedPoint (isPullback_schemeSpace_of_isPullback_yoneda h)
  have sq := isPullback_fieldPointPresentation h
  have hP := isAffineSpace_fieldPoint (G := G) p
  obtain ⟨e, -⟩ := (affineRelativeDualizingComplex G hA).isAffineBaseChangePair
    (schemeSpaceMap v) _ _ sq hP
  have hz := isZero_homology_derivedPullback_affineDualizingComplex G hA hG p V v q h n hn
  refine (Space.isZero_homology_of_isZero_restrictToChartScheme_homology B integerBase hZ V _ n
    (hz.of_iso ?_)).of_iso ((DerivedCategory.homologyFunctor
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).mapIso e)
  exact (Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V) (Space.idEtaleChart B integerBase hZ V)).mapIso
    ((DerivedCategory.homologyFunctor
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).mapIso e.symm)

/-- **The relative dualizing complex of an at-worst-nodal family of curves over an affine base
has no cohomology above degree `-1`** (the upper half of Stacks 0E6P: `ω^•_{X/S} = ω_{X/S}[1]`).
-/
theorem isLE_affineDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom) :
    (affineDualizingComplex G hA).obj.IsLE (-1) := by
  have hqc := Space.isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B integerBase hZ
    G.toBase G.finitePresentation.2.1 (isAffineSpace_schemeSpace_base G hA)
  have hpc := (Space.isPerfectRelativeToCanonical_affineRightAdjoint B.contains_terminal G.toBase
    G.proper G.flat G.finitePresentation (isAffineSpace_schemeSpace_base G hA)).1
  refine Space.isLE_of_isPseudoCoherent_of_forall_fieldValuedPoint_isLE G.total hqc _ hpc (-1)
    fun t => ?_
  -- the field point `t` lies over the field point `p` of the base, and factors through the fibre
  let p := t.map B integerBase hZ G.total.obj G.toBase.hom
  obtain ⟨V, v, q, h⟩ := exists_isPullback_fieldPointPresentation G p
  have hw : yonedaEquiv.symm t.value ≫ G.toBase.hom = 𝟙 _ ≫ yonedaEquiv.symm p.value := by
    rw [Category.id_comp]
    exact yonedaEquiv_symm_naturality_right _ _ _
  let t' : schemeSpace t.siteObject ⟶ schemeSpace V :=
    ObjectProperty.homMk (h.lift (yonedaEquiv.symm t.value) (𝟙 _) hw)
  let qs : schemeSpace V ⟶ G.total := ObjectProperty.homMk q
  have ht : t.toSpace = t' ≫ qs := by
    apply ObjectProperty.hom_ext
    exact (h.lift_fst _ _ hw).symm
  have hLE : ((Space.smallEtaleDerivedModulePullback B integerBase hZ qs).obj
      (affineDualizingComplex G hA).obj).IsLE (-1) := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    exact isZero_homology_smallEtaleDerivedModulePullback_affineDualizingComplex G hA hG p V v q h
      n (by omega)
  have h₂ := Space.isLE_smallEtaleDerivedModulePullback_obj_of_isLE t'
    ((Space.smallEtaleDerivedModulePullback B integerBase hZ qs).obj
      (affineDualizingComplex G hA).obj) (-1)
  rw [ht, DerivedCategory.isLE_iff]
  intro n hn
  exact ((DerivedCategory.isLE_iff _ _).1 h₂ n hn).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((Space.smallEtaleDerivedPullbackCompIsoOfTwoIso B integerBase hZ t' qs).app _).symm)

end AlgebraicGeometry.CurveFamily

end
