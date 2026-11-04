module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPointsTopology
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesGenericFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyStructureSheafCohomology

/-!
# `|𝓜_g|` is open and dense in `|𝓜̄_g|` (Stacks 0E87)

Let `g ≥ 2`. Stacks 0E87 says that the inclusion `|𝓜_g| ⊂ |𝓜̄_g|` of the points of the moduli
stack of smooth proper curves of genus `g` (Stacks 0E83) into those of the moduli stack of stable
curves of genus `g` (Stacks 0E78) is that of an open dense subset. Both are read in the space
`|Curves|` of points of the stack of curves (`AlgebraicGeometry.CurvesPoints`), as the sets of
points represented by a field-valued point whose family of curves lies in the substack
(`AlgebraicGeometry.curvesPointSet`).

* **Inclusion.** A point of `|𝓜_g|` is classified by a proper curve `X` over a field whose family
  of curves is in `𝓜_g`, and for `g ≥ 2` such a family is stable of genus `g`
  (`AlgebraicGeometry.isStableCurveFamilyOfGenus_curveFamilyOfScheme_of_isSmoothH0Family`).
* **Openness.** `|𝓜_g| = |Curves^{smooth}| ∩ |𝓜̄_g|`, and `|Curves^{smooth}|` is open, smoothness
  satisfying condition (o) of Stacks 0E0E.
* **Density.** A point of `|𝓜̄_g|` is classified by a stable curve `X` of genus `g` over a field
  `k`. Its smoothing `Y ⟶ Spec k⟦t⟧` (Stacks 0E7Y) has generic fibre in `𝓜_g`
  (`AlgebraicGeometry.isSmoothH0Family_and_hasGenus_genericFibre`), and the point of the generic
  fibre specializes to the point of `X` in `|Curves|`.

## Main results

* `AlgebraicGeometry.curvesPointSet_isSmoothH0FamilyOfGenus_subset`: `|𝓜_g| ⊆ |𝓜̄_g|`.
* `AlgebraicGeometry.curvesPointSet_isSmoothH0FamilyOfGenus_eq`:
  `|𝓜_g| = |Curves^{smooth}| ∩ |𝓜̄_g|`.
* `AlgebraicGeometry.mem_closure_curvesPointSet_isSmoothH0FamilyOfGenus`: `|𝓜̄_g|` lies in the
  closure of `|𝓜_g|`.
* `AlgebraicGeometry.curvesPointSet_moduliSmoothOfGenus_isOpen_dense_in_stableOfGenus`: for
  `g ≥ 2`, `|𝓜_g|` is an open dense subset of `|𝓜̄_g|`.

## Implementation notes

The source deduces density from Stacks 0E86, the density of `|Curves^{smooth}|` in
`|Curves^{lci+}|`, using that `𝓜̄_g` is an open substack of `Curves^{lci+}`. Here the openness of
`𝓜̄_g` is not used: the smoothing of a stable curve of genus `g` produced in the proof of
Stacks 0E86 has its generic fibre in `𝓜_g` directly, by the local constancy of the Euler
characteristic and of the number of geometric connected components of the fibres.

## References

* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### Field-valued points of the stack of curves classified by schemes -/

/-- **Stacks 0FD1 over a field.** A proper scheme over a field `k` with `Γ(X, 𝒪_X) = k` is
geometrically connected over `k`. -/
theorem geometricallyConnected_of_isIso_appTop {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso f.appTop] : GeometricallyConnected f := by
  have hgc : GeometricallyConnected X.toSpecΓ := by
    open Stacks.AlgebraicGeometry.ProperGeomConnected in
    exact geometricallyConnected_toSpecΓ_of_isProper_over_field k _ f
  have hresp : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h1 : GeometricallyConnected (X.toSpecΓ ≫ Spec.map f.appTop) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected _
      (Spec.map f.appTop)).mpr hgc
  rw [← Scheme.toSpecΓ_naturality] at h1
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
    f (Spec (.of k)).toSpecΓ).mp h1

/-- The field-valued point of the small model of the stack of curves given by a family of curves
over the spectrum of a field of the site. -/
def curvesFieldPoint {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hK) :
    Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val where
  carrier := K
  base := integerSiteObject B hZ hK
  isSpec := Iso.refl _
  obj := (curvesSmallEquivalenceOver B hZ).hom.functor.obj F
  «over» := (Functor.congr_obj (curvesSmallEquivalenceOver B hZ).hom.w F).trans hF

/-- The family of curves of `AlgebraicGeometry.curvesFieldPoint` is the family it is built from,
up to isomorphism. -/
def curvesSmallFamilyCurvesFieldPointIso {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hK) :
    (curvesSmallFamily B hZ).obj (curvesFieldPoint hK F hF).obj ≅ F :=
  ((curvesSmallEquivalenceOver B hZ).unitIso.app F).symm

/-- **Every point of `|Curves|` is classified by a proper curve over a field.** For a
field-valued point `p` of the stack of curves there are a field `K` of the site, a proper scheme
`X` of dimension at most one over `K` and a morphism from the family of curves of `X` to the
family of `p` over an isomorphism of bases; the field-valued point of the family of `X`
represents the same point as `p`. -/
theorem exists_curveFamilyOfScheme_hom
    (p : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val) :
    ∃ (K : Type u) (_ : Field K) (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K)))
      (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1)
      (φ : curveFamilyOfScheme X B hZ hK hdim ⟶ (curvesSmallFamily B hZ).obj p.obj),
      IsIso φ.baseMap ∧
        Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property
          (curvesFieldPoint hK (curveFamilyOfScheme X B hZ hK hdim) rfl) =
        Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property p := by
  have hK := Stack.contains_spectrum_fieldValuedPoint B integerBase hZ p
  have hspec : Stack.spectrumSiteObject B integerBase hZ p = integerSiteObject B hZ hK :=
    congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let F₀ : CurveFamily B hZ := (curvesSmallFamily B hZ).obj p.obj
  let βi : integerSiteObject B hZ hK ≅ F₀.base :=
    eqToIso hspec.symm ≪≫ Stack.spectrumSiteObjectIso B integerBase hZ p ≪≫ eqToIso p.over.symm
  let β : integerSiteObject B hZ hK ⟶ F₀.base := βi.hom
  have : IsIso β := inferInstanceAs (IsIso βi.hom)
  obtain ⟨F, ψ, hψ⟩ := (curvesFiberedCategory B hZ).property.exists_lift β F₀ rfl
  have hF : F.base = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq (curvesFiberedCategory B hZ).val.p β ψ
  obtain ⟨X, _, hdim, ⟨e⟩⟩ := CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq hK F hF
  have hψb : IsIso ψ.baseMap := by
    have h := IsHomLift.fac' (curvesFiberedCategory B hZ).val.p β ψ
    change ψ.baseMap = _ at h
    rw [h]
    exact (eqToIso hF ≪≫ βi ≪≫ eqToIso rfl).isIso_hom
  have heb : IsIso e.inv.baseMap :=
    ⟨e.hom.baseMap, congrArg CurveFamily.Hom.baseMap e.inv_hom_id,
      congrArg CurveFamily.Hom.baseMap e.hom_inv_id⟩
  refine ⟨p.carrier, inferInstance, hK, X, inferInstance, hdim, e.inv ≫ ψ, ?_, ?_⟩
  · show IsIso (e.inv.baseMap ≫ ψ.baseMap)
    infer_instance
  · refine (Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ _ _).2
      ⟨curvesFieldPoint hK (curveFamilyOfScheme X B hZ hK hdim) rfl, ⟨𝟙 _⟩, ⟨?_⟩⟩
    exact (curvesSmallEquivalenceOver B hZ).hom.functor.map (e.inv ≫ ψ) ≫
      (curvesSmallEquivalenceOver B hZ).counitIso.hom.app p.obj

/-- A morphism of families of curves, read in the small model, lies over its morphism of base
schemes. -/
theorem isHomLift_curvesSmallEquivalenceOver_map {F G : CurveFamily B hZ} (m : F ⟶ G) :
    (curvesSmall B hZ).val.p.IsHomLift m.baseMap
      ((curvesSmallEquivalenceOver B hZ).hom.functor.map m) := by
  have hw : (curvesSmallEquivalenceOver B hZ).hom.functor ⋙ (curvesSmall B hZ).val.p =
      curvesProjectionOver B hZ := (curvesSmallEquivalenceOver B hZ).hom.w
  exact IsHomLift.of_fac' _ _ _ (Functor.congr_obj hw F) (Functor.congr_obj hw G)
    (Functor.congr_hom hw m)

/-- Over the family of curves of a proper flat morphism of schemes, `f_*𝒪 = 𝒪` universally makes
the morphism an isomorphism on global functions. -/
theorem bijective_appTop_of_hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (h : HasUniversallyBijectiveGlobalFunctions B hZ
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim)) :
    Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop := by
  have h₁ := HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap B hZ h
  exact (Space.bijective_globalFunctionsMap_schemeSpaceMap_iff g).1 h₁

/-! ### The inclusion `|𝓜_g| ⊂ |𝓜̄_g|` -/

/-- The property of families of curves cutting out `𝓜_g`: smooth of relative dimension one,
`f_*𝒪_X = 𝒪_S` universally, and `R¹f_*𝒪_X` locally free of rank `g` (Stacks 0E83). -/
abbrev IsSmoothH0FamilyOfGenus (g : ℕ) : ObjectProperty (CurveFamily B hZ) :=
  fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g

/-- The genus of a family of curves passes along a morphism of families whose base map is an
isomorphism. -/
private theorem hasGenus_of_hom_of_isIso_baseMap {F G : CurveFamily B hZ} (φ : F ⟶ G)
    [IsIso φ.baseMap] {g : ℕ} (h : CurveFamily.HasGenus B hZ G g) :
    CurveFamily.HasGenus B hZ F g :=
  CurveFamily.hasGenus_of_hom_of_isEtale φ
    (Space.isEtale_of_isIso B integerBase hZ (yoneda.map φ.baseMap)) h

/-- **`|𝓜_g| ⊆ |𝓜̄_g|` for `g ≥ 2`.** A point of `|𝓜_g|` is classified by a smooth proper curve
over a field in `𝓜_g`, which is stable of genus `g`. -/
theorem curvesPointSet_isSmoothH0FamilyOfGenus_subset {g : ℕ} (hg : 2 ≤ g) :
    curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g) ⊆
      curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g) := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨K, _, hK, X, _, hdim, φ, hφ, hcls⟩ := exists_curveFamilyOfScheme_hom p
  have hQ := isStableCurveFamilyOfGenus_curveFamilyOfScheme_of_isSmoothH0Family hK X hdim hg
    (CurveFamily.isSmoothH0Family_of_hom B hZ φ hp.1)
    (hasGenus_of_hom_of_isIso_baseMap φ hp.2)
  let e := curvesSmallFamilyCurvesFieldPointIso hK (curveFamilyOfScheme X B hZ hK hdim) rfl
  exact ⟨curvesFieldPoint hK _ rfl, ⟨CurveFamily.isStableCurveFamily_of_hom e.hom hQ.1,
    CurveFamily.hasGenus_of_iso e hQ.2⟩, hcls⟩

/-- **`|𝓜_g| = |Curves^{smooth}| ∩ |𝓜̄_g|` for `g ≥ 2`.** -/
theorem curvesPointSet_isSmoothH0FamilyOfGenus_eq {g : ℕ} (hg : 2 ≤ g) :
    curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g) =
      curvesPointSet B hZ (IsSmoothFamily B hZ) ∩
        curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g) := by
  refine Set.Subset.antisymm (Set.subset_inter (curvesPointSet_mono fun F hF => hF.1.1.1)
    (curvesPointSet_isSmoothH0FamilyOfGenus_subset hg)) ?_
  rintro x ⟨hs, ⟨q, hq, rfl⟩⟩
  have hsq := (pointClass_mem_curvesPointSet_iff (isOpenCurvesLocus_isSmoothFamily B hZ) q).1 hs
  exact ⟨q, isSmoothH0Family_and_hasGenus_of_isStableCurveFamilyOfGenus B hZ hsq hq, rfl⟩

/-! ### Density -/

/-- **Every point of `|𝓜̄_g|`, `g ≥ 2`, lies in the closure of `|𝓜_g|`.** It is classified by a
stable curve `X` of genus `g` over a field `k`; a smoothing `Y ⟶ Spec k⟦t⟧` of `X` (Stacks 0E7Y)
has generic fibre in `𝓜_g`, and the point of the generic fibre specializes to that of `X`. -/
theorem mem_closure_curvesPointSet_isSmoothH0FamilyOfGenus {g : ℕ} (hg : 2 ≤ g)
    {x : CurvesPoints B hZ} (hx : x ∈ curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g)) :
    x ∈ closure (curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g)) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨k, _, hk, X, _, hdim, φ, hφ, hcls⟩ := exists_curveFamilyOfScheme_hom p
  rw [← hcls]
  have hQ : IsStableCurveFamilyOfGenus B hZ g (curveFamilyOfScheme X B hZ hk hdim) :=
    ⟨CurveFamily.isStableCurveFamily_of_hom φ hp.1,
      hasGenus_of_hom_of_isIso_baseMap φ hp.2⟩
  have hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  have hnodal : IsAtWorstNodalOfRelativeDimensionOne X.hom :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
      (integerSiteMap B hZ hX hk X.hom)).1 (by exact hQ.1.1.1)
  obtain ⟨hlci, hfin⟩ := (isLciPlusFamily_curveFamilyOfScheme_iff B hZ k hk X hdim).1
    (isAtWorstNodal_le_lciPlus B hZ _ hQ.1.1.1)
  have hb := bijective_appTop_of_hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism
    (integerSiteMap B hZ hX hk X.hom) (inferInstanceAs (Flat X.hom))
    (inferInstanceAs (IsProper X.hom))
    (inferInstanceAs (LocallyOfFinitePresentation X.hom))
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ _
      (inferInstanceAs (QuasiCompact X.hom)))
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).2 (inferInstanceAs (IsSeparated X.hom)))
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (QuasiSeparated X.hom))) hdim (by exact hQ.1.1.2)
  have : IsIso X.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := inferInstance
  have : GeometricallyConnected X.hom := geometricallyConnected_of_isIso_appTop X.hom
  have : GeometricallyReduced X.hom :=
    Stacks.AlgebraicGeometry.NodalFamilyCohomology.geometricallyReduced_of_isAtWorstNodal X.hom
      hnodal
  have hgX : genus X.hom = g := genus_eq_of_hasGenus_curveFamilyOfScheme hk X hdim hQ.2
  have hsyn : Syntomic X.hom :=
    (syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism X.hom).2 ⟨inferInstance, hlci⟩
  obtain ⟨Y, f, hflat, hproj, hsm, e, he⟩ :=
    Deformation.Examples.Smoothing.exists_flat_isProjective_smoothing_of_isProper k X.hom hsyn hdim
      hfin
  have : IsProper f := IsProjective.isProper hproj
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := inferInstance
  have := hsm
  have hV : B.Contains (Spec (.of (PowerSeries k))) := BigFppfSite.contains_spec_powerSeries B hk
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hV
  let s := PowerSeriesFamily.specialPoint k
  let y₀ := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hV f) hflat
    (inferInstanceAs (IsProper f)) (inferInstanceAs (LocallyOfFinitePresentation f))
    (fun x => topologicalKrullDimAt_fiber_le_one_of_specialFibre X.hom hdim f e he x)
  have hcart₂ : IsPullback (e.hom ≫ pullback.fst f s) X.hom f s :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he,
      Category.assoc]⟩ e rfl he
  let m₂ : curveFamilyOfScheme X B hZ hk hdim ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hk hV s
      totalMap := schemeSpaceMap (integerSiteMap B hZ hX hY (e.hom ≫ pullback.fst f s))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap hcart₂ }
  let η := PowerSeriesFamily.genericPoint k
  have hK := BigFppfSite.residueField_spec_contains B hV η
  have hYη : B.Contains (f.fiber η) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (f.fiberToSpecResidueField η) hK
  have hdimη : topologicalKrullDim (f.fiber η) ≤ 1 :=
    (fiberDimension_le_one_of_specialFibre X.hom hdim f e he η).trans (by simp)
  have hpη : IsProper (f.fiberToSpecResidueField η) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f _) ‹IsProper f›
  let x₁ := curveFamilyOfProperFlatMorphism B hZ
    (integerSiteMap B hZ hYη hK (f.fiberToSpecResidueField η))
    (inferInstanceAs (Flat (f.fiberToSpecResidueField η))) hpη
    (inferInstanceAs (LocallyOfFinitePresentation (f.fiberToSpecResidueField η))) hdimη
  let m₁ : x₁ ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hK hV ((Spec (.of (PowerSeries k))).fromSpecResidueField η)
      totalMap := schemeSpaceMap (integerSiteMap B hZ hYη hY (f.fiberι η))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap (IsPullback.of_hasPullback f _) }
  have hPx₁ : IsSmoothH0FamilyOfGenus g x₁ := by
    rw [← hgX]
    exact isSmoothH0Family_and_hasGenus_genericFibre f X.hom hcart₂ hdim (hgX ▸ hg) hYη hK _
      hpη _ hdimη
  let q₁ := curvesFieldPoint hK x₁ rfl
  let q₂ := curvesFieldPoint hk (curveFamilyOfScheme X B hZ hk hdim) rfl
  have hspec := @pointClass_specializes_of_isHomLift B hZ _ _
    (Functor.congr_obj (curvesSmallEquivalenceOver B hZ).hom.w y₀) q₁ q₂ m₁.baseMap m₂.baseMap
    ((curvesSmallEquivalenceOver B hZ).hom.functor.map m₁)
    ((curvesSmallEquivalenceOver B hZ).hom.functor.map m₂)
    (isHomLift_curvesSmallEquivalenceOver_map m₁) (isHomLift_curvesSmallEquivalenceOver_map m₂) ?_
  · have hmem : Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property q₁ ∈
        curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g) := by
      let e₁ := curvesSmallFamilyCurvesFieldPointIso hK x₁ rfl
      exact ⟨q₁, ⟨CurveFamily.isSmoothH0Family_of_hom B hZ e₁.hom hPx₁.1,
        CurveFamily.hasGenus_of_iso e₁ hPx₁.2⟩, rfl⟩
    exact closure_mono (Set.singleton_subset_iff.2 hmem) (specializes_iff_mem_closure.1 hspec)
  · have h₁ : Space.schemePoint B integerBase hZ ((curvesFiberedCategory B hZ).val.p.obj y₀)
        (spacePointOfHom q₁ m₁.baseMap) = η :=
      (Spec (.of (PowerSeries k))).fromSpecResidueField_apply η _
    rw [h₁]
    exact (PrimeSpectrum.le_iff_specializes η _).1 bot_le

/-! ### Stacks 0E87 -/

variable (B hZ) in
/-- Let `g ≥ 2`. The inclusion `|𝓜_g| ⊂ |𝓜̄_g|` is that of an open dense
subset.

`𝓜_g` is the substack of the stack of curves of families `f : X → S` which are smooth of relative
dimension one with `f_*𝒪_X = 𝒪_S` universally and `R¹f_*𝒪_X` locally free of rank `g`
(Stacks 0E83), and `𝓜̄_g` that of stable families with `R¹f_*𝒪_X` locally free of rank `g`
(Stacks 0E78); `|𝓜_g|` and `|𝓜̄_g|` are their images in `|Curves|`, with the topology of
Stacks 04Y8, and `|𝓜̄_g|` carries the subspace topology. -/
@[stacks 0E87]
theorem curvesPointSet_moduliSmoothOfGenus_isOpen_dense_in_stableOfGenus
    (g : ℕ) (hg : 2 ≤ g) :
    curvesPointSet B hZ (fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) ⊆
        curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g) ∧
      IsOpen (Subtype.val ⁻¹' curvesPointSet B hZ
          (fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) :
        Set (curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g))) ∧
      Dense (Subtype.val ⁻¹' curvesPointSet B hZ
          (fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) :
        Set (curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g))) := by
  have hsub := curvesPointSet_isSmoothH0FamilyOfGenus_subset (B := B) (hZ := hZ) hg
  refine ⟨hsub, ?_, fun x => ?_⟩
  · have heq : (Subtype.val ⁻¹' curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g) :
          Set (curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g))) =
        Subtype.val ⁻¹' curvesPointSet B hZ (IsSmoothFamily B hZ) := by
      ext x
      rw [Set.mem_preimage, Set.mem_preimage, curvesPointSet_isSmoothH0FamilyOfGenus_eq hg]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    show IsOpen (Subtype.val ⁻¹' curvesPointSet B hZ (IsSmoothH0FamilyOfGenus g) :
      Set (curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g)))
    rw [heq]
    exact (isOpen_curvesPointSet (isOpenCurvesLocus_isSmoothFamily B hZ)).preimage
      continuous_subtype_val
  · rw [closure_subtype, Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]
    exact mem_closure_curvesPointSet_isSmoothH0FamilyOfGenus hg x.2

end AlgebraicGeometry

end
