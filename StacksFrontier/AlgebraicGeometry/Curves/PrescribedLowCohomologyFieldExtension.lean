module

public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember
import StacksFrontier.AlgebraicGeometry.Morphisms.Open.OverField
import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Stacks Tag 0B9Y

Let `k` be a separably closed field, `X` a smooth proper curve of genus `g` over `k`, `K/k` a
field extension, `X_K` the base change and `p : X_K ⟶ X` its projection. Stacks Tag 0B9Y says
that every invertible sheaf `𝓛` on `X_K` has a twist `𝓛 ⊗ p^*𝓛₀` by an invertible sheaf from `X`
with `dim_K H⁰ = 1` and `H¹ = 0`. This file proves this for the fibre product `X_K`, on Picard
classes and on sheaves, together with its variant for a class of degree `0` on `X_K` twisted by
the pullback of a fixed class of degree `g` on `X`.

## Main results

* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_picardRepresentative_pullback`: over an
  arbitrary field `k`, every Picard class `c` on `X_K` has a twist `c + p^*c₀` by a class from `X`
  with `H¹ = 0` and `H⁰ ≠ 0`.
* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_add_schemePullbackClass`: twisting by the
  pullback of the ideal sheaf of a suitable `k`-rational point lowers `dim_K H⁰` by one and keeps
  `H¹ = 0`.
* `AlgebraicGeometry.exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one`: every
  Picard class `c` on `X_K` has a twist `c + p^*c₀` with `dim_K H⁰ = 1` and `H¹ = 0`.
* `exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one_of_isSepClosed`: every
  invertible `𝓛` on `X_K` has a twist `𝓛 ⊗ p^*𝓛₀` with `dim_K H⁰ = 1` and `H¹ = 0`.
* `AlgebraicGeometry.exists_invertibleCurveDegreeHom_eq_zero_finrank_cohomologyOverField_eq_one`:
  for `c` of degree `0` on `X_K` and `θ` of degree `g` on `X`, a class `c₀` of degree `0` on `X`
  with `dim_K H⁰(c + p^*c₀ + p^*θ) = 1` and `H¹(c + p^*c₀ + p^*θ) = 0`.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 0383](https://stacks.math.columbia.edu/tag/0383)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.RingedSpace (structureIsSheaf)
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ComponentDegrees
  (discreteTopology_of_isProper_of_topologicalKrullDim_le_zero)
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

local notation3 "𝔞" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation3 "𝔛" => Limits.pullback (C := Scheme) f 𝔞
local notation3 "𝔣" => pullback.snd f 𝔞
local notation3 "𝔭" => pullback.fst f 𝔞

/-- The base change `X_K` of a curve over `k` has dimension at most one
([Stacks, Tag 0BY9], dimension clause). -/
theorem topologicalKrullDim_pullback_le_one [IsCurve k f] :
    topologicalKrullDim (pullback (C := Scheme.{u}) f 𝔞) ≤ 1 := by
  rw [topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback f 𝔞)]
  exact (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

/-- **The base change of a smooth geometrically irreducible scheme over a field is integral.** -/
theorem isIntegral_pullback_of_smooth [Smooth f] [GeometricallyIrreducible f] :
    IsIntegral (pullback (C := Scheme.{u}) f 𝔞) := by
  have : UniversallyOpen f := universallyOpen_of_field k f
  have : IsReduced (pullback (C := Scheme.{u}) f 𝔞) :=
    isReduced_of_smooth_of_isAffine (pullback.snd f _)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The base change of a smooth geometrically irreducible curve is a curve.** -/
theorem isCurve_pullback_snd [IsCurve k f] [Smooth f] [GeometricallyIrreducible f] :
    IsCurve K (pullback.snd f 𝔞) := by
  have := isIntegral_pullback_of_smooth k K f
  refine (isCurve_iff K _).2 ⟨{}, ?_⟩
  rw [topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback f 𝔞)]
  exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)

/-- **A smooth proper geometrically irreducible scheme over a field has `dim_k H⁰(X, 𝒪) = 1`.** -/
theorem finrank_cohomologyOverField_zero_unit_eq_one [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 := by
  have := isIntegral_pullback_of_smooth k (AlgebraicClosure k) f
  have hunit : (Scheme.Modules.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit (pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).ringCatSheaf :=
    Scheme.Modules.pullbackUnitIso _
  refine (finrank_cohomologyOverField_baseChange_field k (AlgebraicClosure k) _ _ f
    (IsPullback.of_hasPullback f _) _ 0).symm.trans ?_
  refine (finrank_cohomologyOverField_eq_of_iso (AlgebraicClosure k) _ hunit 0).trans ?_
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  exact finrank_globalSections_eq_one (AlgebraicClosure k) _

/-- On the base change `X_K` of a smooth proper geometrically irreducible scheme,
`dim_K H⁰(X_K, 𝒪) = 1`. -/
theorem finrank_cohomologyOverField_zero_unit_pullback_eq_one [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] :
    Module.finrank K (cohomologyOverField K (pullback.snd f 𝔞)
      (SheafOfModules.unit (pullback (C := Scheme.{u}) f 𝔞).ringCatSheaf) 0) = 1 :=
  finrank_cohomologyOverField_zero_unit_eq_one K (pullback.snd f 𝔞)

/-- **Riemann–Roch on the base change, on Picard classes.** For a smooth proper geometrically
irreducible curve `X` over a field `k` and a field extension `K/k`, every Picard class `m` on
`X_K` satisfies `dim_K H⁰(X_K, m) - dim_K H¹(X_K, m) = deg(m) + 1 - g`, with `g` the genus of
`X`. -/
theorem finrank_zero_sub_finrank_one_picardRepresentative_pullback [IsProper f]
    [IsCurve k f] [Smooth f] [GeometricallyIrreducible f]
    (m : Stacks.Picard.ofScheme (pullback (C := Scheme.{u}) f 𝔞)) :
    (Module.finrank K (cohomologyOverField K (pullback.snd f 𝔞)
        (Stacks.Picard.picardRepresentative
          (pullback (C := Scheme.{u}) f 𝔞).toRingedSpace m).obj 0) : ℤ)
      - (Module.finrank K (cohomologyOverField K (pullback.snd f 𝔞)
        (Stacks.Picard.picardRepresentative
          (pullback (C := Scheme.{u}) f 𝔞).toRingedSpace m).obj 1) : ℤ) =
      invertibleCurveDegreeHom K (pullback.snd f 𝔞) (topologicalKrullDim_pullback_le_one k K f) m
        + 1 - (genus f : ℤ) := by
  have h := finrank_cohomologyOverField_zero_sub_one_eq K (pullback.snd f 𝔞)
    (topologicalKrullDim_pullback_le_one k K f)
    (Stacks.Picard.picardRepresentative (pullback (C := Scheme.{u}) f 𝔞).toRingedSpace m).obj
    (Stacks.Picard.picardRepresentative (pullback (C := Scheme.{u}) f 𝔞).toRingedSpace m).property
  rw [finrank_cohomologyOverField_zero_unit_pullback_eq_one k K f,
    genus_baseChange k K _ _ f (IsPullback.of_hasPullback f 𝔞)] at h
  exact h

/-- `AlgebraicGeometry.HasPrescribedLowCohomology` is invariant under isomorphism. -/
theorem HasPrescribedLowCohomology.of_iso {K : Type u} [Field K] {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of K)} {M N : X'.Modules} (e : M ≅ N) {t : ℕ}
    (h : HasPrescribedLowCohomology K f' M t) : HasPrescribedLowCohomology K f' N t where
  isZero_one := h.isZero_one.of_iso (cohomologyOverFieldIso K f' e 1).symm
  finiteDimensional_zero :=
    have := h.finiteDimensional_zero
    LinearEquiv.finiteDimensional (cohomologyOverFieldIso K f' e 0).toLinearEquiv
  finrank_zero := (finrank_cohomologyOverField_eq_of_iso K f' e 0).symm.trans h.finrank_zero

/-- A zero module over a field has finrank `0`. -/
private theorem finrank_eq_zero_of_isZero {R : Type u} [Field R] {M : ModuleCat.{u} R}
    (h : IsZero M) : Module.finrank R M = 0 :=
  have := ModuleCat.subsingleton_of_isZero h
  Module.finrank_zero_of_subsingleton

/-- An invertible module on a scheme whose class is `c` is isomorphic to the chosen
representative of `c`. -/
private theorem nonempty_iso_picardRepresentative_of_picardClass_eq {Y : Scheme.{u}}
    {N : Y.Modules} (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureIsSheaf Y.toRingedSpace) N) {c : Stacks.Picard.ofScheme Y}
    (h : Stacks.SheafOfModules.picardClass Y.presheaf (structureIsSheaf Y.toRingedSpace) N hN =
      c) :
    Nonempty (N ≅ (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj) :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ hN
    (Stacks.Picard.picardRepresentative Y.toRingedSpace _).property).1
    (h.trans (Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace _).symm)

/-- **The start of the induction of Stacks Tag 0B9Y.** For every Picard class `c` on the base
change `X_K` of a smooth proper geometrically irreducible curve over a field, some twist
`c + p^*c₀` by a class from `X` has vanishing `H¹` and nonzero `H⁰`. -/
theorem exists_hasPrescribedLowCohomology_picardRepresentative_pullback
    [IsProper f] [IsCurve k f] [Smooth f] [GeometricallyIrreducible f]
    (c : Stacks.Picard.ofScheme (pullback (C := Scheme.{u}) f 𝔞)) :
    ∃ (c₀ : Stacks.Picard.ofScheme X) (t : ℕ), HasPrescribedLowCohomology K (pullback.snd f 𝔞)
      (Stacks.Picard.picardRepresentative (pullback (C := Scheme.{u}) f 𝔞).toRingedSpace
        (c + Stacks.Picard.schemePullbackClass (pullback.fst f 𝔞) c₀)).obj (t + 1) := by
  have := isCurve_pullback_snd k K f
  have hdimK : topologicalKrullDim 𝔛 ≤ 1 := topologicalKrullDim_pullback_le_one k K f
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  obtain ⟨N, hN, hN1⟩ := exists_invertible_isZero_cohomologyOverField_one K 𝔣
  have _ : IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have _ : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨A, hA, hample⟩ := Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A := hA
  have hdegA : 0 < invertibleCurveDegree k f hdim A :=
    (isAmple_iff_invertibleCurveDegree_pos k f hdim A).1 hample
  set a := Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) A hA
  have hdega : invertibleCurveDegreeHom k f hdim a = invertibleCurveDegree k f hdim A :=
    invertibleCurveDegreeHom_picardClass k f hdim A hA
  have hNa : SheafOfModules.IsInvertible (𝔛).presheaf (𝔛).ringCatSheaf.property N := hN
  set j : ℕ := (invertibleCurveDegree K 𝔣 hdimK N).natAbs +
    (invertibleCurveDegreeHom K 𝔣 hdimK c).natAbs + genus f + 1 with hj
  refine ⟨j • a, ?_⟩
  set m := c + Stacks.Picard.schemePullbackClass (pullback.fst f 𝔞) (j • a) with hm
  have hdegm : invertibleCurveDegreeHom K 𝔣 hdimK m =
      invertibleCurveDegreeHom K 𝔣 hdimK c + j * invertibleCurveDegree k f hdim A := by
    rw [hm, map_add, invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
      (IsPullback.of_hasPullback f 𝔞) hdim hdimK, map_nsmul, hdega, nsmul_eq_mul]
  have hrr := finrank_zero_sub_finrank_one_picardRepresentative_pullback k K f m
  set M := (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).obj with hMdef
  have hM : SheafOfModules.IsInvertible (𝔛).presheaf (𝔛).ringCatSheaf.property M :=
    (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).property
  have hNs : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf (𝔛).ringCatSheaf.property N :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  have hMa : SheafOfModules.IsInvertible (𝔛).sheaf.obj (𝔛).ringCatSheaf.property
      (M ⊗ tensorPowerModule N (-1) : (𝔛).Modules) :=
    @isInvertible_tensorSheaf_tensorPowerModule_neg_one 𝔛 M N hM hNa
  have hdegMN : @invertibleCurveDegree K _ 𝔛 𝔣 _ hdimK
      (M ⊗ tensorPowerModule N (-1) : (𝔛).Modules) hMa =
      invertibleCurveDegree K 𝔣 hdimK M - invertibleCurveDegree K 𝔣 hdimK N :=
    @invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one K _ 𝔛 𝔣 _ _ hdimK N M hNa hM
  have hrrMN := finrank_cohomologyOverField_zero_sub_one_eq K 𝔣 hdimK
    (M ⊗ tensorPowerModule N (-1) : (𝔛).Modules) hMa
  rw [finrank_cohomologyOverField_zero_unit_pullback_eq_one k K f,
    genus_baseChange k K _ _ f (IsPullback.of_hasPullback f 𝔞)] at hrrMN
  have hdegM : invertibleCurveDegree K 𝔣 hdimK M = invertibleCurveDegreeHom K 𝔣 hdimK m := rfl
  have hjA : (j : ℤ) ≤ j * invertibleCurveDegree k f hdim A :=
    le_mul_of_one_le_right (by positivity) hdegA
  have hsec : 0 < Module.finrank K
      (cohomologyOverField K 𝔣 (M ⊗ tensorPowerModule N (-1) : (𝔛).Modules) 0) := by
    rw [hdegMN, hdegM, hdegm] at hrrMN
    omega
  have hvan : IsZero (cohomologyOverField K 𝔣 M 1) :=
    @isZero_cohomologyOverField_one_of_tensorInverse_section K _ 𝔛 𝔣 _ _ hdimK N M hNs hNa hMa
      hN1 hsec
  rw [finrank_eq_zero_of_isZero hvan, hdegm] at hrr
  have hpos : 0 < Module.finrank K (cohomologyOverField K 𝔣 M 0) := by omega
  exact ⟨Module.finrank K (cohomologyOverField K 𝔣 M 0) - 1,
    ⟨hvan, FiniteDimensional.of_finrank_pos hpos, by omega⟩⟩

/-- **A closed point with separable residue field over a separably closed field is
`k`-rational, read on global sections.** For a closed point `x` of a proper scheme over a
separably closed field `k` whose residue field is separable over `k`, the reduced closed
subscheme on `x` has `k` as its ring of global functions. -/
theorem isIso_globalSections_vanishingIdeal_of_isSeparable [IsSepClosed k] [IsProper f]
    {x : X} (hx : IsClosed ({x} : Set X))
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).subschemeι ≫ f).appTop) := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)
    with hD
  have _ : IsIntegral D.subscheme := isIntegral_subscheme_vanishingIdeal hx
  obtain ⟨z, hzx⟩ : ∃ z : D.subscheme, D.subschemeι z = x := by
    have hmem : x ∈ Set.range D.subschemeι := by
      rw [hD, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact Set.mem_singleton x
    exact hmem
  rw [← hzx] at hsep
  let φ : k →+* Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom
  let : Field Γ(D.subscheme, ⊤) := (isField_of_universallyClosed k (D.subschemeι ≫ f)).toField
  let ev : Γ(D.subscheme, ⊤) →+* D.subscheme.residueField z := (D.subscheme.Γevaluation z).hom
  let : Algebra k (D.subscheme.residueField z) := (ev.comp φ).toAlgebra
  let : Algebra k (X.residueField (D.subschemeι z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (D.subschemeι z)).hom.toAlgebra
  have _ : IsIso (D.subschemeι.residueFieldMap z) :=
    residueFieldMap_isIso_of_isClosedImmersion D.subschemeι z
  let e : X.residueField (D.subschemeι z) ≃ₐ[k] D.subscheme.residueField z :=
    { (asIso (D.subschemeι.residueFieldMap z)).commRingCatIsoToRingEquiv with
      commutes' := fun c => by
        show (D.subschemeι.residueFieldMap z).hom
            ((X.Γevaluation (D.subschemeι z)).hom (f.appTop.hom
              ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
          (D.subscheme.Γevaluation z).hom (((D.subschemeι ≫ f).appTop).hom
            ((Scheme.ΓSpecIso (.of k)).inv.hom c))
        rw [Scheme.Γevaluation_naturality_apply, Scheme.Hom.comp_appTop]
        rfl }
  have _ : Algebra.IsSeparable k (D.subscheme.residueField z) :=
    AlgEquiv.Algebra.isSeparable e
  have hsurj : Function.Surjective (ev.comp φ) :=
    IsSepClosed.algebraMap_surjective k (D.subscheme.residueField z)
  have hbij : Function.Bijective φ := by
    refine ⟨φ.injective, fun a => ?_⟩
    obtain ⟨c, hc⟩ := hsurj (ev a)
    exact ⟨c, ev.injective hc⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

/-- **The `k`-rational point base-changes to a `K`-rational point, read on global sections.** For
a closed point `x` with separable residue field of a proper scheme over a separably closed field
`k`, the inverse image in `X_K` of the reduced closed subscheme on `x` has `K` as its ring of
global functions. -/
theorem isIso_globalSections_comap_vanishingIdeal [IsSepClosed k] [IsProper f]
    {x : X} (hx : IsClosed ({x} : Set X))
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (((Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap 𝔭).subschemeι ≫ 𝔣).appTop) := by
  have _ := isIso_globalSections_vanishingIdeal_of_isSeparable k f hx hsep
  exact isIso_globalSections_baseChange k K _ _ _
    ((Stacks.Bertini.isPullback_subschemeι_comap _ 𝔭).flip.paste_vert
      (IsPullback.of_hasPullback f 𝔞))

/-- **`H⁰(X_K, i_*i^*𝓛) = H⁰(x_K, i^*𝓛)` has dimension `1`.** For a closed point `x` with
separable residue field of a proper curve over a separably closed field `k` whose reduced closed
subscheme pulls back to an effective Cartier divisor of `X_K`, the restriction of an invertible
module on `X_K` to that divisor has one-dimensional `H⁰` over `K`. -/
theorem finrank_cohomologyOverField_zero_pullback_comap_vanishingIdeal_eq_one [IsSepClosed k]
    [IsProper f] [IsCurve k f] {x : X} (hx : IsClosed ({x} : Set X))
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x))
    [Stacks.Divisors.IsEffectiveCartierDivisor ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap 𝔭)]
    (M : (𝔛).Modules)
    [hM : SheafOfModules.IsInvertible (𝔛).sheaf.obj (𝔛).ringCatSheaf.property M] :
    Module.finrank K (cohomologyOverField K
      (((Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap 𝔭).subschemeι ≫ 𝔣)
      ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap 𝔭).subschemeι).obj M) 0) = 1 := by
  set C := (Scheme.IdealSheafData.vanishingIdeal
    (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap 𝔭 with hC
  have hdisc : DiscreteTopology (C.subscheme : Type u) :=
    discreteTopology_of_isProper_of_topologicalKrullDim_le_zero K (C.subschemeι ≫ 𝔣)
      (topologicalKrullDim_divisorSubscheme_le_zero (topologicalKrullDim_pullback_le_one k K f) C)
  have hMpre : SheafOfModules.IsInvertible (𝔛).presheaf (𝔛).ringCatSheaf.2 M := hM
  have hpull : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj M) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι M hMpre
  have _ : Stacks.SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj M) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨e⟩ : Nonempty ((Scheme.Modules.pullback C.subschemeι).obj M ≅
      SheafOfModules.unit C.subscheme.ringCatSheaf) :=
    Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology C.subscheme
      ((Scheme.Modules.pullback C.subschemeι).obj M)
  rw [finrank_cohomologyOverField_eq_of_iso K (C.subschemeι ≫ 𝔣) e 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K (C.subschemeι ≫ 𝔣)]
  let : Algebra K Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (C.subschemeι ≫ 𝔣).appTop).hom.toAlgebra
  have hiso := isIso_globalSections_comap_vanishingIdeal k K f hx hsep
  have hbij : Function.Bijective (algebraMap K Γ(C.subscheme, ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  rw [← (AlgEquiv.ofBijective (Algebra.ofId K Γ(C.subscheme, ⊤)) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **One step of the descending induction of Stacks Tag 0B9Y.** Let `m` be a Picard class on the
base change `X_K` with vanishing `H¹` and `dim_K H⁰ = t + 2`. Then twisting by the pullback of
the ideal sheaf of a suitable `k`-rational point of `X` gives a class with vanishing `H¹` and
`dim_K H⁰ = t + 1`. -/
theorem exists_hasPrescribedLowCohomology_add_schemePullbackClass [IsSepClosed k] [IsProper f]
    [IsCurve k f] [Smooth f] [GeometricallyIrreducible f]
    (m : Stacks.Picard.ofScheme 𝔛) (t : ℕ)
    (h : HasPrescribedLowCohomology K 𝔣
      (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).obj (t + 2)) :
    ∃ e : Stacks.Picard.ofScheme X, HasPrescribedLowCohomology K 𝔣
      (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
        (m + Stacks.Picard.schemePullbackClass 𝔭 e)).obj (t + 1) := by
  have := isCurve_pullback_snd k K f
  set M := (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).obj with hMdef
  have hM : SheafOfModules.IsInvertible (𝔛).sheaf.obj (𝔛).ringCatSheaf.property M :=
    (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).property
  have hMp : SheafOfModules.IsInvertible (𝔛).presheaf (𝔛).ringCatSheaf.2 M := hM
  have hMr : Stacks.SheafOfModules.IsInvertible (𝔛).toRingedSpace.presheaf
      (structureSheafRing (𝔛).toRingedSpace).property M :=
    (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace m).property
  have hpos : 0 < Module.finrank K (cohomologyOverField K 𝔣 M 0) := by
    rw [h.finrank_zero]; omega
  have _ := h.finiteDimensional_zero
  have _ : Nontrivial (cohomologyOverField K 𝔣 M 0 : Type u) := Module.finrank_pos_iff.mp hpos
  have _ : Nontrivial Γ(M, ⊤) := (cohomologyOverFieldZeroEquivSections K 𝔣 M).symm.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(M, ⊤))
  have hbridge : Stacks.SheafOfModules.nonvanishingLocus (X := (𝔛).toRingedSpace) M
      (Stacks.SheafOfModules.sectionsOfTop M s) = Stacks.Ample.nonvanishingLocus M s :=
    nonvanishingLocus_sectionsOfTop_eq M s
  have hVo : IsOpen (Stacks.Ample.nonvanishingLocus M s) := by
    rw [← hbridge]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := (𝔛).toRingedSpace) M _
  have hVne : (Stacks.Ample.nonvanishingLocus M s).Nonempty :=
    hbridge ▸ nonempty_nonvanishingLocus_of_ne_zero M s hs
  have hUo : IsOpen (𝔭 '' Stacks.Ample.nonvanishingLocus M s) :=
    isOpenMap_pullback_fst_specMap_algebraMap k K f _ hVo
  obtain ⟨y, ⟨v, hvV, hvy⟩, hycl, -, hysep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth f).inter_open_nonempty _
      hUo (hVne.image _)
  have hyc : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hycl
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
    with hD
  have hDeff : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f hyc).out 1 4).mp
      (((isRegular_iff_regular_stalks X).mp (isRegular_of_smooth_over_field f)).2 y)
  have hpb : Stacks.Divisors.IsPullbackDefined 𝔭 D :=
    Stacks.Divisors.isPullbackDefined_of_flat 𝔭 D hDeff
  set C := D.comap 𝔭 with hC
  have hCeff : Stacks.Divisors.IsEffectiveCartierDivisor C := hpb
  obtain ⟨w, hSE⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist C M hM
  obtain ⟨z, hzv⟩ : ∃ z : C.subscheme, C.subschemeι z = v := by
    have hv : v ∈ Set.range C.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hC, Scheme.IdealSheafData.support_comap]
      show 𝔭 v ∈ (D.support : Set X)
      rw [hD, Scheme.IdealSheafData.coe_support_vanishingIdeal, hvy]
      exact Set.mem_singleton y
    exact hv
  have hright : Module.finrank K (cohomologyOverField K 𝔣
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj M)) 0) = 1 := by
    rw [← (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion K C.subschemeι 𝔣
      ((Scheme.Modules.pullback C.subschemeι).obj M) 0).toLinearEquiv.finrank_eq]
    exact @finrank_cohomologyOverField_zero_pullback_comap_vanishingIdeal_eq_one k K _ _ _ X f _ _
      _ y hyc hysep hCeff M hM
  have ha : cohomologyOverFieldMap K 𝔣
      ((modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app M) 0
      ((cohomologyOverFieldZeroEquivSections K 𝔣 M).symm s) ≠ 0 := by
    intro hc
    refine app_top_unit_ne_zero_of_mem_nonvanishingLocus C.subschemeι M s z (hzv ▸ hvV) ?_
    have key := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap K 𝔣
      ((modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app M)
      ((cohomologyOverFieldZeroEquivSections K 𝔣 M).symm s)
    exact ((congrArg (fun t => (Scheme.Modules.Hom.app
            ((modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app M) ⊤) t)
          (Equiv.apply_symm_apply (cohomologyOverFieldZeroEquivSections K 𝔣 M) s).symm).trans
        (key.symm.trans
          ((congrArg (cohomologyOverFieldZeroEquivSections K 𝔣
              ((Scheme.Modules.pushforward C.subschemeι).obj
                ((Scheme.Modules.pullback C.subschemeι).obj M))) hc).trans
            (cohomologyOverFieldZeroEquivSections_zero K 𝔣 _))))
  have hstep := hasPrescribedLowCohomology_of_shortExact K 𝔣 hSE (t + 1) h hright ha
  have hDr : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Divisors.Eta.idealSheaf D) :=
    Stacks.Divisors.isInvertible_idealSheaf' D
  refine ⟨Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
    (Stacks.Divisors.Eta.idealSheaf D) hDr, ?_⟩
  have hCr : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf
      (structureSheafRing (𝔛).toRingedSpace).property (Stacks.Divisors.Eta.idealSheaf C) :=
    Stacks.Divisors.isInvertible_idealSheaf' C
  have hpull : Stacks.Picard.schemePullbackClass 𝔭
      (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
        (Stacks.Divisors.Eta.idealSheaf D) hDr) =
      Stacks.SheafOfModules.picardClass (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace)
        (Stacks.Divisors.Eta.idealSheaf C) hCr := by
    refine (Stacks.Picard.pullbackClass_classOf _ _ hDr).trans ?_
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨Stacks.Divisors.pullbackIdealSheafComapIso 𝔭 D hpb⟩
  have hCM : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf
      (structureSheafRing (𝔛).toRingedSpace).property
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (𝔛).sheaf).flip.obj M).obj
        (Stacks.Divisors.idealSheafOfModules C)) :=
    Stacks.SheafOfModules.tensorProduct_isInvertible (𝔛).presheaf
      (structureSheafRing (𝔛).toRingedSpace).property
      (Stacks.Divisors.idealSheafOfModules C) M
  have hcls : Stacks.SheafOfModules.picardClass (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (𝔛).sheaf).flip.obj M).obj
        (Stacks.Divisors.idealSheafOfModules C)) hCM =
      m + Stacks.Picard.schemePullbackClass 𝔭
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
          (Stacks.Divisors.Eta.idealSheaf D) hDr) := by
    rw [hpull, add_comm, ← Stacks.Picard.classOf_picardRepresentative (𝔛).toRingedSpace m]
    exact (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hCr hMr hCM).symm
  obtain ⟨e⟩ := nonempty_iso_picardRepresentative_of_picardClass_eq hCM hcls
  exact hstep.of_iso e

/-- **The descending induction of Stacks Tag 0B9Y, on Picard classes.** If a twist `c + p^*c₀`
of a Picard class `c` on `X_K` by a class from `X` has vanishing `H¹` and `dim_K H⁰ = t + 1`,
then some twist `c + p^*c₁` has vanishing `H¹` and `dim_K H⁰ = 1`. -/
theorem exists_hasPrescribedLowCohomology_one_of_add_schemePullbackClass [IsSepClosed k]
    [IsProper f] [IsCurve k f] [Smooth f] [GeometricallyIrreducible f]
    (c : Stacks.Picard.ofScheme 𝔛) (t : ℕ) (c₀ : Stacks.Picard.ofScheme X)
    (h : HasPrescribedLowCohomology K 𝔣 (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
      (c + Stacks.Picard.schemePullbackClass 𝔭 c₀)).obj (t + 1)) :
    ∃ c₁ : Stacks.Picard.ofScheme X, HasPrescribedLowCohomology K 𝔣
      (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
        (c + Stacks.Picard.schemePullbackClass 𝔭 c₁)).obj 1 := by
  induction t generalizing c₀ with
  | zero => exact ⟨c₀, h⟩
  | succ t ih =>
      obtain ⟨e, he⟩ := exists_hasPrescribedLowCohomology_add_schemePullbackClass k K f
        (c + Stacks.Picard.schemePullbackClass 𝔭 c₀) t h
      have hcl : c + Stacks.Picard.schemePullbackClass 𝔭 c₀ + Stacks.Picard.schemePullbackClass 𝔭 e
          = c + Stacks.Picard.schemePullbackClass 𝔭 (c₀ + e) := by
        rw [add_assoc]
        exact congrArg (c + ·) (Stacks.Picard.pullbackClass_add _ _ _).symm
      exact ih (c₀ + e) (hcl ▸ he)

/-- Let `k` be a separably closed field, `X` a smooth proper curve over `k`, `K/k` a field
extension and `p : X_K ⟶ X` the projection of the base change. For every Picard class `c` on
`X_K` (the class of an invertible `𝓛`) there is a Picard class `c₀` on `X` (the class of an
invertible `𝓛₀`) such that the class `c + p^*c₀` (that of `𝓛 ⊗ 𝓛₀|_{X_K}`) has

`dim_K H⁰(X_K, c + p^*c₀) = 1` and `H¹(X_K, c + p^*c₀) = 0`. -/
@[stacks 0B9Y "on Picard classes: the class c of the invertible sheaf L on X_K and the class \
c₀ of L₀ on X, with c + p^*c₀ the class of L ⊗ L₀|_{X_K}; H¹ = 0 is stated as vanishing, which \
gives dim_K H¹ = 0. Properness of X is used in place of projectivity"]
theorem exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one
    [IsSepClosed k] [IsProper f] [IsCurve k f] [Smooth f] (c : Stacks.Picard.ofScheme 𝔛) :
    ∃ c₀ : Stacks.Picard.ofScheme X,
      Module.finrank K (cohomologyOverField K 𝔣
        (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
          (c + Stacks.Picard.schemePullbackClass 𝔭 c₀)).obj 0) = 1 ∧
      IsZero (cohomologyOverField K 𝔣
        (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
          (c + Stacks.Picard.schemePullbackClass 𝔭 c₀)).obj 1) := by
  have := geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  obtain ⟨c₀, t, h⟩ := exists_hasPrescribedLowCohomology_picardRepresentative_pullback k K f c
  obtain ⟨c₁, h₁⟩ := exists_hasPrescribedLowCohomology_one_of_add_schemePullbackClass k K f c t c₀ h
  exact ⟨c₁, h₁.finrank_zero, h₁.isZero_one⟩

/-- Let `k` be a separably closed field, `X` a smooth proper curve over `k`, `K/k` a field
extension and `p : X_K ⟶ X` the projection of the base change. For every invertible
`𝒪_{X_K}`-module `𝓛` there is an invertible `𝒪_X`-module `𝓛₀` with

`dim_K H⁰(X_K, 𝓛 ⊗ p^*𝓛₀) = 1` and `dim_K H¹(X_K, 𝓛 ⊗ p^*𝓛₀) = 0`. -/
@[stacks 0B9Y "the source's statement on sheaves, with L ⊗ L₀|_{X_K} the twist \
baseChangeTwist p L L₀ = L ⊗ p^*L₀; properness of X is used in place of projectivity"]
theorem exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one_of_isSepClosed
    [IsSepClosed k] [IsProper f] [IsCurve k f] [Smooth f]
    (L : (𝔛).Modules) [hL : Stacks.Ample.IsInvertibleModule 𝔛 L] :
    ∃ L₀ : X.Modules, Stacks.Ample.IsInvertibleModule X L₀ ∧
      Module.finrank K (cohomologyOverField K 𝔣 (baseChangeTwist 𝔭 L L₀) 0) = 1 ∧
      Module.finrank K (cohomologyOverField K 𝔣 (baseChangeTwist 𝔭 L L₀) 1) = 0 := by
  have hLs : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf
      (structureIsSheaf (𝔛).toRingedSpace) L := hL
  obtain ⟨c₀, h0, h1⟩ := exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one k K f
    (Stacks.SheafOfModules.picardClass (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace) L hLs)
  set L₀ := Stacks.Picard.picardRepresentative X.toRingedSpace c₀ with hL₀
  have hpL₀ : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor (𝔭).toLRSHom.toShHom).obj L₀.obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of _ _ L₀.property
  have hT : Stacks.SheafOfModules.IsInvertible (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace)
      (baseChangeTwist 𝔭 L L₀.obj) :=
    @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _ hLs hpL₀
  have hcls : Stacks.SheafOfModules.picardClass (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace)
      (baseChangeTwist 𝔭 L L₀.obj) hT =
      Stacks.SheafOfModules.picardClass (𝔛).presheaf (structureIsSheaf (𝔛).toRingedSpace) L hLs +
        Stacks.Picard.schemePullbackClass 𝔭 c₀ :=
    (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hLs hpL₀ hT).symm
  obtain ⟨e⟩ := nonempty_iso_picardRepresentative_of_picardClass_eq hT hcls
  refine ⟨L₀.obj, L₀.property, ?_, ?_⟩
  · rw [finrank_cohomologyOverField_eq_of_iso K 𝔣 e 0]
    exact h0
  · rw [finrank_cohomologyOverField_eq_of_iso K 𝔣 e 1]
    exact finrank_eq_zero_of_isZero h1

/-- Let `X` be a smooth proper curve of genus `g` over a separably closed field `k`, let `K/k` be
a field extension and `p : X_K ⟶ X` the projection of the base change. For a Picard class `c` of
degree `0` on `X_K` and a Picard class `θ` of degree `g` on `X` there is a Picard class `c₀` of
degree `0` on `X` such that `ℳ = c + p^*c₀ + p^*θ` satisfies

`dim_K H⁰(X_K, ℳ) = 1` and `H¹(X_K, ℳ) = 0`. -/
theorem exists_invertibleCurveDegreeHom_eq_zero_finrank_cohomologyOverField_eq_one
    [IsSepClosed k] [IsProper f] [IsCurve k f] [Smooth f]
    (c : Stacks.Picard.ofScheme 𝔛)
    (hc : invertibleCurveDegreeHom K 𝔣 (topologicalKrullDim_pullback_le_one k K f) c = 0)
    (θ : Stacks.Picard.ofScheme X)
    (hθ : invertibleCurveDegreeHom k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
      θ = genus f) :
    ∃ c₀ : Stacks.Picard.ofScheme X,
      invertibleCurveDegreeHom k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
        c₀ = 0 ∧
      Module.finrank K (cohomologyOverField K 𝔣
        (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
          (c + Stacks.Picard.schemePullbackClass 𝔭 c₀ +
            Stacks.Picard.schemePullbackClass 𝔭 θ)).obj 0) = 1 ∧
      IsZero (cohomologyOverField K 𝔣
        (Stacks.Picard.picardRepresentative (𝔛).toRingedSpace
          (c + Stacks.Picard.schemePullbackClass 𝔭 c₀ +
            Stacks.Picard.schemePullbackClass 𝔭 θ)).obj 1) := by
  have := geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  set hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  obtain ⟨D, h0, h1⟩ :=
    exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one k K f c
  have hrr := finrank_zero_sub_finrank_one_picardRepresentative_pullback k K f
    (c + Stacks.Picard.schemePullbackClass 𝔭 D)
  rw [h0, finrank_eq_zero_of_isZero h1, map_add, hc,
    invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
    (IsPullback.of_hasPullback f 𝔞) hdim (topologicalKrullDim_pullback_le_one k K f)] at hrr
  have hsum : c + Stacks.Picard.schemePullbackClass 𝔭 (D - θ) +
      Stacks.Picard.schemePullbackClass 𝔭 θ = c + Stacks.Picard.schemePullbackClass 𝔭 D := by
    rw [add_assoc, ← Stacks.Picard.pullbackClass_add, sub_add_cancel]
  refine ⟨D - θ, ?_, hsum ▸ h0, hsum ▸ h1⟩
  rw [map_sub, hθ]
  push_cast at hrr
  omega

end AlgebraicGeometry
