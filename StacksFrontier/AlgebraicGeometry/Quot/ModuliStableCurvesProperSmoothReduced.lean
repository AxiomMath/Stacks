module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedLocallyFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDM
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesProperSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesPolarizationOfModules
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.CurveFacts
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Main
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaAlgebraicStacks

/-!
# `𝓜̄_g` is a proper smooth Deligne–Mumford stack (Stacks 0E9C)

Let `g ≥ 2`. The algebraic stack `𝓜̄_g` is a Deligne–Mumford stack, proper and smooth over
`Spec(ℤ)`. Moreover, the locus `𝓜_g` parametrizing smooth curves is a dense open substack.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_hom_curveFamilyOfScheme_baseMap_eq`: a family of curves
  over `Spec K` receives a morphism of families, over a given identification of its base, from
  the family of a proper scheme over `K`.
* `isCurve_smooth_isProjective_of_isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme`: such a
  scheme in `𝓜_g` is a smooth projective curve with `H⁰ = K` and of genus `g`.
* `AlgebraicGeometry.hasStableReductionCurveFamilies_of_two_le`: for `g ≥ 2`, every family of
  curves of `𝓜_g` over the fraction field of a discrete valuation ring acquires stable reduction
  after a finite separable extension (Stacks 0E98, part (1), in families).
* `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of_isSeparated`: if `𝓜̄_g`
  is separated over `Spec(ℤ)` and stable reduction holds in families, then `𝓜̄_g` is a proper
  smooth Deligne–Mumford stack in which `𝓜_g` is a dense open substack.
* `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth`: `𝓜̄_g` is a proper smooth
  Deligne–Mumford stack over `Spec(ℤ)` in which `𝓜_g` is a dense open substack.

## References

* [Stacks Project, Tag 0E9C](https://stacks.math.columbia.edu/tag/0E9C)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0E98](https://stacks.math.columbia.edu/tag/0E98)
* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A morphism of families of curves of proper schemes over a field, over an automorphism of
the base.** Let `X` and `X'` be proper schemes of dimension at most one over a field `K`, let `β`
be an automorphism of `Spec K` (over the integers) and `i : X' ≅ X` an isomorphism of schemes with
`i ≫ X.hom = X'.hom ≫ β`. Then there is a morphism of families of curves from the family of `X'`
to that of `X` lying over `β`: the square formed by `i`, the two structure morphisms and `β` is
cartesian, its horizontal sides being isomorphisms. -/
theorem exists_hom_curveFamilyOfScheme_of_iso {K : Type u} [Field K] {B : BigFppfSite.{u}}
    {hZ : B.Contains integerBase} (hK : B.Contains (Spec (.of K))) (X X' : Over (Spec (.of K)))
    [IsProper X.hom] [IsProper X'.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (hdim' : topologicalKrullDim X'.left ≤ 1)
    (β : integerSiteObject B hZ hK ≅ integerSiteObject B hZ hK) (i : X'.left ≅ X.left)
    (w : i.hom ≫ X.hom = X'.hom ≫ (BigFppfOver.toScheme B integerBase hZ).map β.hom) :
    ∃ θ : curveFamilyOfScheme X' B hZ hK hdim' ⟶ curveFamilyOfScheme X B hZ hK hdim,
      θ.baseMap = β.hom := by
  have hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  have hX' : B.Contains X'.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X'.hom hK
  let ι : integerSiteObject B hZ hX' ≅ integerSiteObject B hZ hX :=
    { hom := integerSiteMap B hZ hX' hX i.hom
      inv := integerSiteMap B hZ hX hX' i.inv
      hom_inv_id := Over.OverMorphism.ext (ObjectProperty.hom_ext _ i.hom_inv_id)
      inv_hom_id := Over.OverMorphism.ext (ObjectProperty.hom_ext _ i.inv_hom_id) }
  have hw : integerSiteMap B hZ hX' hX i.hom ≫ integerSiteMap B hZ hX hK X.hom =
      integerSiteMap B hZ hX' hK X'.hom ≫ β.hom :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ w)
  refine ⟨(CurveFamily.isoMk β ((schemeSpaceFunctor B integerBase hZ).mapIso ι) ?_).hom, rfl⟩
  show schemeSpaceMap (integerSiteMap B hZ hX' hX i.hom) ≫
      schemeSpaceMap (integerSiteMap B hZ hX hK X.hom) =
    schemeSpaceMap (integerSiteMap B hZ hX' hK X'.hom) ≫ schemeSpaceMap β.hom
  rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hw]

/-- **A family of curves over `Spec K` is the family of a proper curve, over a given
identification of its base.** Let `F` be a family of curves and `eK` an identification of its base
with `Spec K`, `K` a field. There are a proper scheme `X` of dimension at most one over `K` and a
morphism of families from the family of `X` to `F` lying over `eK`. -/
theorem CurveFamily.exists_hom_curveFamilyOfScheme_baseMap_eq {K : Type u} [Field K]
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (hK : B.Contains (Spec (.of K)))
    (F : CurveFamily B hZ) (eK : integerSiteObject B hZ hK ≅ F.base) :
    ∃ (X : Over (Spec (.of K))) (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1)
      (ψ : curveFamilyOfScheme X B hZ hK hdim ⟶ F), ψ.baseMap = eK.hom := by
  have hid : ∀ U : BigFppfOver B integerBase hZ, schemeSpaceMap (𝟙 U) = 𝟙 (schemeSpace U) :=
    fun U => (schemeSpaceFunctor B integerBase hZ).map_id U
  have : IsIso (schemeSpaceMap eK.hom) :=
    inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso eK).hom)
  have hcommF : 𝟙 F.total ≫ F.toBase = (F.toBase ≫ schemeSpaceMap eK.inv) ≫
      schemeSpaceMap eK.hom := by
    rw [Category.id_comp, Category.assoc, ← schemeSpaceMap_comp, Iso.inv_hom_id, hid,
      Category.comp_id]
  have : IsIso (𝟙 F.total) := IsIso.id _
  have sqF := IsPullback.of_horiz_isIso ⟨hcommF⟩
  obtain ⟨X, hXp, hdim, ⟨φ⟩⟩ := CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq hK
    (F.ofIsPullback B hZ eK.hom (𝟙 F.total) _ sqF) rfl
  have := hXp
  let β : integerSiteObject B hZ hK ≅ integerSiteObject B hZ hK :=
    { hom := φ.hom.baseMap
      inv := φ.inv.baseMap
      hom_inv_id := congrArg CurveFamily.Hom.baseMap φ.hom_inv_id
      inv_hom_id := congrArg CurveFamily.Hom.baseMap φ.inv_hom_id }
  let s : Spec (.of K) ⟶ Spec (.of K) := (BigFppfOver.toScheme B integerBase hZ).map β.inv
  have : IsIso β.inv := Iso.isIso_inv β
  have : IsIso s := Functor.map_isIso _ _
  let t : Spec (.of K) ⟶ Spec (.of K) := (BigFppfOver.toScheme B integerBase hZ).map β.hom
  have hst : s ≫ t = 𝟙 (Spec (.of K)) :=
    ((BigFppfOver.toScheme B integerBase hZ).mapIso β).inv_hom_id
  have : IsProper (Over.mk (X.hom ≫ s)).hom := inferInstanceAs (IsProper (X.hom ≫ s))
  have hw : 𝟙 X.left ≫ X.hom = (X.hom ≫ s) ≫ t := by
    rw [Category.id_comp, Category.assoc, hst, Category.comp_id]
  obtain ⟨θ, hθ⟩ := exists_hom_curveFamilyOfScheme_of_iso hK X (Over.mk (X.hom ≫ s)) hdim hdim β
    (Iso.refl X.left) hw
  refine ⟨Over.mk (X.hom ≫ s), inferInstance, hdim,
    θ ≫ φ.inv ≫ F.homOfIsPullback B hZ eK.hom (𝟙 F.total) _ sqF, ?_⟩
  show θ.baseMap ≫ β.inv ≫ eK.hom = eK.hom
  rw [hθ]
  exact β.hom_inv_id_assoc eK.hom

open Stacks in
/-- **A family of a proper scheme over a field in `𝓜_g` is a smooth projective curve of genus
`g`.** Let `X` be a proper scheme of dimension at most one over a field `K` whose family of
curves lies in `𝓜_g`. Then `X` is a smooth projective curve over `K` with `H⁰(X, 𝒪_X) = K` and of
genus `g`. -/
theorem isCurve_smooth_isProjective_of_isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme
    {K : Type u} [Field K] {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {g : ℕ}
    (h : IsSmoothH0FamilyOfFibreGenus B hZ g (curveFamilyOfScheme X B hZ hK hdim)) :
    IsCurve K X.hom ∧ Smooth X.hom ∧ IsProjective X.hom ∧
      IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) ∧ genus X.hom = g := by
  obtain ⟨hsm, hd1, hH0, hgen⟩ :=
    (isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme_iff g hK X hdim).1 h
  have := hsm
  have : GeometricallyIntegral X.hom :=
    ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral K X.hom
      (isGeometricallyNormal_of_smooth X.hom)).out 1 4).1 hH0
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  exact ⟨{ topologicalKrullDim_eq_one := hd1 }, hsm,
    (HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
      X.hom hd1.le).isProjective, hH0, hgen⟩

variable {B hZ} in
open CategoryTheory.Limits Stacks.Models in
/-- **Stable reduction in the families of `𝓜_g` and `𝓜̄_g`** (Stacks 0E98, part (1)). Let
`g ≥ 2`. Every family of curves `F` of `𝓜_g` over the fraction field `K` of a discrete valuation
ring `A` acquires stable reduction after a finite separable extension of `K`: there are an
extension of discrete valuation rings `A ⊂ A'` inducing a finite separable extension `K'/K`, a
stable family of curves over `Spec A'`, and a family over `Spec K'` mapping to it and to `F` by
morphisms of families over the given maps of bases. -/
theorem hasStableReductionCurveFamilies_of_two_le {g : ℕ} (hg : 2 ≤ g) :
    HasStableReductionCurveFamilies B hZ g := by
  intro A _ _ _ K _ _ _ hA hK tA F e hF
  let eK : integerSiteObject B hZ hK ≅ F.base :=
    schemeOverIntegersLeftIso (siteObject B integerBase hZ hK
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ tA)) ≪≫ e.symm
  obtain ⟨X, _, hdim, ψ, hψ⟩ := CurveFamily.exists_hom_curveFamilyOfScheme_baseMap_eq hK F eK
  obtain ⟨hcurve, hsm, hproj, hH0, hgen⟩ :=
    isCurve_smooth_isProjective_of_isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme hK X hdim
      (CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom ψ
        ((isSmoothH0FamilyOfFibreGenus_iff g F).2 ⟨hF.1.2, hF.1.1, hF.2⟩))
  obtain ⟨⟨K', _, _, _, _, hfd, hsep, R', _, _, _, _, _, _, _, hloc, hR', Y, p, hst, ⟨E⟩⟩, -⟩ :=
    stableReduction A K X.hom hproj (by rw [hgen]; exact hg) B hZ hA
  rw [hgen] at hst
  obtain ⟨hflat, hprop, hlfp, hfib, hstab⟩ := hst
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hR'
  have hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  let ιR : Spec (.of K') ⟶ Spec (.of R') := Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  let ιK : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : IsFinite ιK := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hfd
  have hK' : B.Contains (Spec (.of K')) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ιK hK
  have hP : B.Contains (pullback p ιR) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd p ιR) hK'
  have sqY := isPullback_schemeSpaceMap_integerSiteMap (B := B) (hZ := hZ) (hP := hP) (hQ := hY)
    (hR := hK') (hW := hR') (IsPullback.of_hasPullback p ιR)
  have sqC : IsPullback (E.hom.left ≫ pullback.fst X.hom ιK) (pullback.snd p ιR) X.hom ιK := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback X.hom ιK)
      ((Over.forget _).mapIso E).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [← Over.comp_left_assoc]
    · simpa using (Over.w E.inv).symm
    · simp
    · simp
  have sqCY := isPullback_schemeSpaceMap_integerSiteMap (B := B) (hZ := hZ) (hP := hP) (hQ := hX)
    (hR := hK') (hW := hK) sqC
  have hfrac : (algebraMap R' K').comp (algebraMap A R') =
      (algebraMap K K').comp (algebraMap A K) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have halg : (algebraMap K K').toAlgebra = ‹Algebra K K'› := Algebra.algebra_ext _ _ fun _ => rfl
  let stable : CurveFamily B hZ :=
    curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR' p) hflat hprop hlfp hfib
  let generic : CurveFamily B hZ :=
    stable.ofIsPullback B hZ (integerSiteMap B hZ hK' hR' ιR) _ _ sqY
  let χ : generic ⟶ curveFamilyOfScheme X B hZ hK hdim :=
    ⟨integerSiteMap B hZ hK' hK ιK, _, sqCY⟩
  have hgiven : (χ ≫ ψ).baseMap ≫ e.hom =
      integerSiteMap B hZ hK' hK ιK ≫ (schemeOverIntegersLeftIso (siteObject B integerBase hZ hK
        (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ tA))).hom := by
    show (integerSiteMap B hZ hK' hK ιK ≫ ψ.baseMap) ≫ e.hom = _
    simp [hψ, eK]
  exact ⟨{
    A' := R'
    K' := K'
    ringMap := algebraMap A R'
    fieldMap := algebraMap K K'
    isLocalHom := hloc
    fraction_comm := hfrac
    finite := RingHom.finite_algebraMap.2 hfd
    separable := by
      rw [halg]
      exact hsep
    ring_mem := hR'
    field_mem := hK'
    stable := stable
    isStable := hstab
    stableBase := schemeOverIntegersLeftIso (siteObject B integerBase hZ hR'
      (Spec.map (CommRingCat.ofHom (algebraMap A R')) ≫ tA))
    generic := generic
    genericBase := schemeOverIntegersLeftIso (siteObject B integerBase hZ hK'
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A R')) ≫ tA))
    toStable := stable.homOfIsPullback B hZ _ _ _ sqY
    toStable_base := by
      simp only [Over.comp_left, schemeOverIntegersLeftIso]
      rfl
    toGiven := χ ≫ ψ
    toGiven_base := by
      rw [hgiven]
      simp only [schemeOverIntegersLeftIso]
      rfl }⟩

/-- Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g` be the open substacks of the algebraic stack of curves
cut out by being stable of genus `g` and by being smooth of relative dimension one with
`f_*𝒪_X = 𝒪_S` universally and of genus `g`. If `𝓜̄_g` is separated over `Spec(ℤ)` (Stacks 0E9A),
and stable reduction holds for families of curves (Stacks 0E98 (1)), then `𝓜̄_g` is a
Deligne–Mumford stack, proper and smooth over `Spec(ℤ)`, and `𝓜_g` is an open substack of `𝓜̄_g`
whose points are dense in `|𝓜̄_g|`. -/
theorem moduliStableCurves_isDeligneMumford_proper_smooth_of_isSeparated (g : ℕ)
    (hg : 2 ≤ g)
    (hsep : Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
            (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ))))
    (hred : HasStableReductionCurveFamilies B hZ g) :
    Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
        (curvesSmallOpenSubstack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
            (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
            g)).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ))) ∧
      IsSmoothOverIntegers B hZ (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
          (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g) ∧
      ∃ hle : (curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
            (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) hg)).property ≤
          (curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)).property,
        @Dense _ (Stack.pointTopology B integerBase hZ
            (curvesSmallOpenSubstack B hZ
              (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
              (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
                (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
                g)).toAlgebraicStack.val)
          (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
            (Stack.OpenSubstack.homOfLE B integerBase hZ
              (curvesSmallOpenSubstack B hZ
                (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
                (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ
                  (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) hg))
              (curvesSmallOpenSubstack B hZ
                (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
                (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
                  (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g))
                hle))) := by
  obtain ⟨-, -, -, -, -, -, hDM⟩ :=
    curvesSmall.exists_curvesDM_and_le_and_isDeligneMumfordStack_of_isOpenCurvesLocus
      (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ) g
      (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
      (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
        (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)
  exact moduliStableCurves_isDeligneMumford_proper_smooth_of_stableLocus B hZ
    (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ) g hg
    (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
    (isQuasiSeparated_and_isLocallyOfFinitePresentation_curvesAlgebraicStack.{u, w} B hZ)
    hDM hsep
    (fun _ _ _ hY hYqc hYqs f' hsep' hft' =>
      Stack.AlgebraicStacks.hasChowCover B hY hYqc hYqs f' hsep' hft')
    hred

/-- Let `g ≥ 2`. The algebraic stack `𝓜̄_g` is a Deligne–Mumford stack, proper and smooth over
`Spec(ℤ)`. Moreover, the locus `𝓜_g` parametrizing smooth curves is a dense open substack.

Here `𝓜̄_g` is the open substack of the algebraic stack of curves (Stacks 0D5A) cut out by the
stable families of genus `g` (Stacks 0E78), and `𝓜_g` the one cut out by the families smooth of
relative dimension one with `f_*𝒪_X = 𝒪_S` universally and of genus `g` (Stacks 0E83); the
conjuncts are: `𝓜̄_g` is Deligne–Mumford, `𝓜̄_g → Spec(ℤ)` is proper, it is smooth, and `𝓜_g`
is contained in `𝓜̄_g` (so it is an open substack of `𝓜̄_g`) with points dense in `|𝓜̄_g|`. -/
@[stacks 0E9C "g ≥ 2 (hg); 𝓜̄_g is Deligne–Mumford, proper and smooth over Spec(ℤ), and 𝓜_g is \
an open substack of 𝓜̄_g whose points are dense in |𝓜̄_g|; nothing is assumed"]
theorem moduliStableCurves_isDeligneMumford_proper_smooth (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsDeligneMumfordStack.{u, u + 1} B integerBase hZ
        (curvesSmallOpenSubstack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
            (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
            g)).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ))) ∧
      IsSmoothOverIntegers B hZ
        (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
          (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g) ∧
      ∃ hle : (curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
            (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) hg)).property ≤
          (curvesSmallOpenSubstack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
              (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g)).property,
        @Dense _ (Stack.pointTopology B integerBase hZ
            (curvesSmallOpenSubstack B hZ
              (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
              (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
                (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
                g)).toAlgebraicStack.val)
          (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
            (Stack.OpenSubstack.homOfLE B integerBase hZ
              (curvesSmallOpenSubstack B hZ
                (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
                (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ
                  (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) hg))
              (curvesSmallOpenSubstack B hZ
                (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, u + 1} B hZ)
                (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ
                  (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) g))
                hle))) :=
  moduliStableCurves_isDeligneMumford_proper_smooth_of_isSeparated.{u, u + 1} B hZ g hg
    (isSeparated_moduliStableCurvesOfGenus_unconditional B hZ g hg)
    (hasStableReductionCurveFamilies_of_two_le hg)

end AlgebraicGeometry

end
