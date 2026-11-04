module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemesFibres
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.UniversalFormsStrataImmersion
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.TricanonicalEquations
public import StacksFrontier.AlgebraicGeometry.Stacks.CompactPointsOfSchemeObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory

/-!
# The moduli stack of stable curves of genus `g` is quasi-compact (Stacks 0E9B)

Let `g ≥ 2`. The space of points of `𝓜̄_g` (Stacks 04Y8), with its canonical topology
(Stacks 04XL), is quasi-compact: this is the definition of a quasi-compact algebraic stack
(Stacks 04YB, `AlgebraicGeometry.Stack.IsQuasiCompactStack`).

Stable curves of genus `g` are bounded. By the tricanonical embedding (Stacks 0E8X) and the
regularity of their ideal sheaves (Stacks 08AG), every stable curve of genus `g` over a field `K`
is `Proj (K[T₀, …, T_{5g-6}] ⧸ (s_1, …, s_M))` for forms `s_j` of a degree `m` depending only on
`g` (`AlgebraicGeometry.exists_iso_proj_formsGrading_of_isAmple_dualizingSheafOverField`), hence a
fibre of one of finitely many proper flat families `Zᵢ ⟶ Tᵢ` over Noetherian schemes
(`Stacks.UniversalForms.exists_flat_families_of_forms_isImmersion`). The locus `Wᵢ ⊆ Tᵢ` of
points with stable fibre of genus `g` is open
(`AlgebraicGeometry.exists_opens_forall_mem_iff_isStableCurveOfGenusOverField`: the openness of
`𝓜̄_g` in the stack of curves, Stacks 0E76 and 0E78, for these families), hence quasi-compact,
and the restricted families are objects of `𝓜̄_g` over `Wᵢ`
(`AlgebraicGeometry.isCurveFamilyOfSchemesWith_isStableCurveFamilyOfFibreGenus`). Every point of
`𝓜̄_g` maps to one of them, so the space of points is the union of finitely many compact images
(`AlgebraicGeometry.Stack.compactSpace_points_of_forall_exists_hom`).

## Main definitions

* `AlgebraicGeometry.moduliStableCurvesOfGenusSmall`: the model of `𝓜̄_g` with hom types in the
  universe of the schemes, on which the topology of Stacks 04XL is defined.

## Main results

* `AlgebraicGeometry.compactSpace_points_moduliStableCurvesOfGenusSmall`: **Stacks 0E9B**.

## References

* [Stacks Project, Tag 0E9B](https://stacks.math.columbia.edu/tag/0E9B)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 0E8X](https://stacks.math.columbia.edu/tag/0E8X)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The total category of `𝓜̄_g` is locally small at the universe of the schemes, being a full
subcategory of the category of families of curves. -/
theorem locallySmall_moduliStableCurvesOfGenus (g : ℕ) :
    LocallySmall.{u} (moduliStableCurvesOfGenus B hZ g).val.obj :=
  let := locallySmall_curveFamily B hZ
  inferInstanceAs (LocallySmall.{u}
    (ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g)))

/-- **The small model of `𝓜̄_g`**: the moduli stack of stable curves of genus `g` of Stacks 0E77,
`AlgebraicGeometry.moduliStableCurvesOfGenus`, with its hom types brought down to the universe of
the schemes, as a category fibred in groupoids over the big fppf site of `Spec(ℤ)`. It is
equivalent over the site to `𝓜̄_g`. -/
noncomputable def moduliStableCurvesOfGenusSmall (g : ℕ) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  letI := locallySmall_moduliStableCurvesOfGenus B hZ g
  ⟨(moduliStableCurvesOfGenus B hZ g).val.shrinkHoms.{u},
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
      (BasedCategory.shrinkHomsEquivalenceOver (moduliStableCurvesOfGenus B hZ g).val).symm
      (moduliStableCurvesOfGenus B hZ g).property⟩

variable {B hZ} in
/-- **A point of `𝓜̄_g` is a stable curve of genus `g` over a field.** The family of curves of a
field-valued point of the small model of `𝓜̄_g` maps to the family of a proper scheme `X` over the
field of the point which is a stable curve of genus `g`, in the sense of part (2) of
Stacks 0E78. -/
theorem exists_hom_curveFamilyOfScheme_of_fieldValuedPoint {g : ℕ} (hg : 2 ≤ g)
    (p : Stack.FieldValuedPoint B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g).val) :
    ∃ (hK : B.Contains (Spec (.of p.carrier))) (X : Over (Spec (.of p.carrier)))
      (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1),
      IsStableCurveOfGenusOverField p.carrier X.hom g ∧
        Nonempty ((ShrinkHoms.fromShrinkHoms p.obj).obj ⟶ curveFamilyOfScheme X B hZ hK hdim) := by
  have hK : B.Contains (Spec (.of p.carrier)) := by
    have hb : ((BigFppfOver.toScheme B integerBase hZ).obj p.base).size < B.cutoff := p.base.left.2
    rwa [Scheme.size_congr p.isSpec] at hb
  let F₀ := (ShrinkHoms.fromShrinkHoms p.obj).obj
  have hF₀ : IsStableCurveFamilyOfFibreGenus B hZ g F₀ := (ShrinkHoms.fromShrinkHoms p.obj).property
  have hb : F₀.base = p.base := p.over
  let e₀ : B.obj hK ≅ p.base.left := B.inclusion.preimageIso p.isSpec.symm
  let θ : integerSiteObject B hZ hK ≅ p.base :=
    Over.isoMk e₀ (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let θ' : integerSiteObject B hZ hK ⟶ F₀.base := θ.hom ≫ eqToHom hb.symm
  obtain ⟨F₁, φ, hφ⟩ := (curvesFiberedCategory B hZ).2.exists_lift θ' F₀ rfl
  have := hφ
  have hF₁base : F₁.base = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq (curvesFiberedCategory B hZ).val.p θ' φ
  have hF₁ := CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ φ hF₀
  obtain ⟨X, hXp, hdim, ⟨e⟩⟩ := CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq hK F₁ hF₁base
  have hiso : IsIso ((curvesFiberedCategory B hZ).val.p.map φ) := by
    rw [IsHomLift.fac' (curvesFiberedCategory B hZ).val.p θ' φ]
    infer_instance
  obtain ⟨χ, -, -⟩ := (curvesFiberedCategory B hZ).2.unique_lift φ (𝟙 F₀)
    (inv ((curvesFiberedCategory B hZ).val.p.map φ)) (by simp)
  have hXst := CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ e.inv hF₁
  have hbb := (isStableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff hg hK X hdim).mp hXst
  have hc := ((factors_moduliStableCurvesOfGenus_over_field_iff (B := B) (hZ := hZ) hg hK X
    hdim).2).mp hbb
  exact ⟨hK, X, hXp, hdim, hc, ⟨χ ≫ e.hom⟩⟩

/-- Let `g ≥ 2`. The moduli stack `𝓜̄_g` of stable curves of genus `g` is
quasi-compact: the space of points of its small model
`AlgebraicGeometry.moduliStableCurvesOfGenusSmall` (Stacks 04XG), with the topology of
Stacks 04XL, is compact. This is quasi-compactness of an algebraic stack in the sense of
Stacks 04YB (`AlgebraicGeometry.Stack.IsQuasiCompactStack`, which is this `CompactSpace`). -/
@[stacks 0E9B]
theorem compactSpace_points_moduliStableCurvesOfGenusSmall (g : ℕ) (hg : 2 ≤ g) :
    @CompactSpace (Stack.points B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g).val
      (moduliStableCurvesOfGenusSmall B hZ g).property)
      (Stack.pointTopology B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g)) := by
  obtain ⟨m, hm⟩ := exists_iso_proj_formsGrading_of_isAmple_dualizingSheafOverField.{u} g hg
  obtain ⟨t, T, Z, π, himm, hT, hfl, hpr, hbd⟩ :=
    Stacks.UniversalForms.exists_flat_families_of_forms_isImmersion.{u} (5 * g - 6)
      ((5 * g - 6 + 1 + m - 1).choose m) m
  have hCoeff : B.Contains (Spec (.of (Stacks.UniversalForms.CoeffRing.{u} (5 * g - 6)
      ((5 * g - 6 + 1 + m - 1).choose m) m))) := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ)
        (Stacks.UniversalForms.CoeffRing.{u} (5 * g - 6) ((5 * g - 6 + 1 + m - 1).choose m) m)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (Stacks.UniversalForms.CoeffRing.{u} (5 * g - 6)
        ((5 * g - 6 + 1 + m - 1).choose m) m)))) hZ
  have hTc : ∀ i, B.Contains (T i) := fun i => by
    obtain ⟨j, hj⟩ := himm i
    exact Space.contains_of_isImmersion B hCoeff j
  have : ∀ i, LocallyOfFinitePresentation (π i) := fun i =>
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hWex : ∀ i, ∃ W : (T i).Opens, ∀ (K : Type u) [Field K] (V : Scheme.{u})
      (y : Spec (CommRingCat.of K) ⟶ T i) (q : V ⟶ Z i) (fV : V ⟶ Spec (CommRingCat.of K))
      [IsProper fV], IsPullback q fV (π i) y →
      (y (IsLocalRing.closedPoint K) ∈ W ↔ IsStableCurveOfGenusOverField K fV g) := fun i => by
    exact exists_opens_forall_mem_iff_isStableCurveOfGenusOverField (π i) g
  choose W hW using hWex
  have hWc : ∀ i, B.Contains (W i).toScheme := fun i =>
    Scheme.size_lt_of_isOpenImmersion (W i).ι (hTc i)
  have hst : ∀ i, IsCurveFamilyOfSchemesWith B hZ (IsStableCurveFamilyOfFibreGenus B hZ g)
      (π i ∣_ W i) (hWc i) := fun i => by
    refine isCurveFamilyOfSchemesWith_isStableCurveFamilyOfFibreGenus hg (π i ∣_ W i) (hWc i)
      fun K _ V y q fV _ sq => ?_
    have hpaste := sq.paste_horiz (isPullback_morphismRestrict (π i) (W i)).flip
    exact (hW i K V (y ≫ (W i).ι) (q ≫ (π i ⁻¹ᵁ W i).ι) fV hpaste).mp
      (y (IsLocalRing.closedPoint K)).2
  choose hflatW hproperW hlfpW hfibW hPW using hst
  let G : ∀ i, CurveFamily B hZ := fun i => curveFamilyOfFiberDimensionLE B hZ
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (π i ∣_ W i)
      (hWc i)) (hWc i) (π i ∣_ W i)) (hflatW i) (hproperW i) (hlfpW i) (hfibW i)
  let x : ∀ i, (moduliStableCurvesOfGenusSmall B hZ g).val.p.Fiber
      (integerSiteObject B hZ (hWc i)) :=
    fun i => ⟨ShrinkHoms.toShrinkHoms (⟨G i, hPW i⟩ :
      ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g)), rfl⟩
  have hcpt : ∀ i, CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj
      (integerSiteObject B hZ (hWc i))) := fun i => by
    have := hT i
    show CompactSpace (W i).toScheme
    exact isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  refine Stack.compactSpace_points_of_forall_exists_hom B integerBase hZ
    (moduliStableCurvesOfGenusSmall B hZ g) (fun i => integerSiteObject B hZ (hWc i)) x
    fun p => ?_
  obtain ⟨hK, X, hXp, hdim, hc, ⟨χ⟩⟩ := exists_hom_curveFamilyOfScheme_of_fieldValuedPoint hg p
  have hc' := hc
  obtain ⟨hnodal, hdim1, hH0, hgen, hamp⟩ := hc'
  let : X.left.Over (Spec (.of p.carrier)) := ⟨X.hom⟩
  have : IsProper (X.left ↘ Spec (.of p.carrier)) := hXp
  have : IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ (X.left ↘ Spec (.of p.carrier)).appTop) :=
    hH0
  obtain ⟨s, hs, eP, heP⟩ := hm p.carrier X.left hdim1 hgen hnodal hamp
  obtain ⟨i, xpt, q, hq⟩ := hbd p.carrier s hs
  have sqX : IsPullback (eP.hom ≫ q) X.hom (π i) xpt := by
    have h1 : IsPullback eP.hom X.hom (Stacks.UniversalForms.formsToSpec p.carrier s hs)
        (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact heP⟩
    simpa using h1.paste_horiz hq
  have hmem := (hW i p.carrier X.left xpt (eP.hom ≫ q) X.hom sqX).mpr hc
  obtain ⟨y', q', -, -, sq'⟩ := exists_isPullback_restrict_of_mem (π i) (W i) sqX hmem
  have hXc : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  have hZWc : B.Contains (π i ⁻¹ᵁ W i).toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (π i ∣_ W i) (hWc i)
  let ψ : curveFamilyOfScheme X B hZ hK hdim ⟶ G i :=
    { baseMap := integerSiteMap B hZ hK (hWc i) y'
      totalMap := schemeSpaceMap (integerSiteMap B hZ hXc hZWc q')
      cartesian := isPullback_schemeSpaceMap_integerSiteMap sq' }
  have := locallySmall_moduliStableCurvesOfGenus B hZ g
  let φ' : (ShrinkHoms.fromShrinkHoms p.obj : (moduliStableCurvesOfGenus B hZ g).val.obj) ⟶
      (⟨G i, hPW i⟩ : (moduliStableCurvesOfGenus B hZ g).val.obj) :=
    ObjectProperty.homMk (χ ≫ ψ)
  exact ⟨i, ⟨(ShrinkHoms.functor.{u} (moduliStableCurvesOfGenus B hZ g).val.obj).map φ'⟩⟩

end AlgebraicGeometry

end
