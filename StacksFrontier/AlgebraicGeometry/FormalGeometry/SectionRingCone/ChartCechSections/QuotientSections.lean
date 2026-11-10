module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ChartCechSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ZeroSchemePowerCofinality
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections

/-!
# Sections of the ideal-power quotients along a zero scheme as Čech cocycles

Let `L` be an ample invertible module on `X` with section ring `A`, `t₁, …, t_r ∈ A₁` with affine
nonvanishing opens covering `X`, `s` a global section of `L` with image `f ∈ A₁` and zero scheme
`Z(s)`. For `m, n ≥ 0`, a global section of `L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}` lifts on each affine
chart `X_{t_j}` to a section of `L^{⊗ m}`, whose chart image, reduced modulo `f^{n+1}`, does not
depend on the lift (`Stacks.Algebraization.SectionRingCone.chartQuotientReduction_eq_zero_iff`).
These reductions form a degree-`m` Čech cocycle of `t` with coefficients in `A / f^{n+1} A`,
and the section is determined by it.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.quotCechSection` — the Čech cocycle of a section of the
  ideal-power quotient.

## Main results

* `Stacks.Algebraization.SectionRingCone.towerReduction_globalCechSection` — the cocycle of the
  reduction of a global section of `L^{⊗ m}` is the reduction of its cocycle.
* `Stacks.Algebraization.SectionRingCone.towerTransition_quotCechSection` — compatibility with
  the transition maps.
* `Stacks.Algebraization.SectionRingCone.quotCechSection_injective` — the cocycle determines
  the section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.LocalCohomology (powerQuotientShortComplex powerQuotientSESMap cechModMap cechModMap_mk)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (presheaf_map_homOfLE_comp)
open Deformation.Artin.SectionsSheaf (modulesHom_app_presheaf_map)

attribute [local instance] instVAddNatIntGradedLocalizedModule

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

universe u

namespace Stacks.Algebraization.SectionRingCone

/-- The map induced on a Čech localization, read on a localization at an equal element. -/
theorem cechModMap_localizedModuleAwayCongr {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M N : ModuleCat R} (g : M ⟶ N) (s : Finset (Fin r)) {g₀ : R} (h : g₀ = ∏ i ∈ s, f i)
    (z : LocalizedModule (Submonoid.powers g₀) M) :
    cechModMap f g s (localizedModuleAwayCongr h z) =
      localizedModuleAwayCongr h (LocalizedModule.map (Submonoid.powers g₀) g.hom z) := by
  subst h
  induction z using LocalizedModule.induction_on with
  | h x u =>
    change cechModMap f g s (LocalizedModule.mk x u) =
      LocalizedModule.map (Submonoid.powers _) g.hom (LocalizedModule.mk x u)
    rw [cechModMap_mk, LocalizedModule.map_mk]

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) {r : ℕ} (fam : Fin r → powSections L 1) (s : Γ(L, ⊤))

/-- The projection `A → A / f^{n+1} A`. -/
abbrev quotProj (n : ℕ) :=
  (powerQuotientShortComplex (sectionDegreeOne L s) (sectionRingModule (L := L)) (n + 1)).g

/-- The projection `L^{⊗ m} → L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}`. -/
abbrev quotPi (m n : ℕ) :=
  cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
    (AlgebraicGeometry.zeroScheme X L s) (n + 1) (natTensorPow L m)).ι

/-- The chart comparison is additive. -/
theorem chartMap_sub {d : ℕ} (hd : 0 < d) (a : powSections L d) (m : ℕ)
    (σ σ' : Γ(natTensorPow L m, nvOpen L a)) :
    chartMap L hL hd a m (σ - σ') = chartMap L hL hd a m σ - chartMap L hL hd a m σ' := by
  simp only [chartMap, map_sub, AddSubgroup.coe_sub]

/-- The reduced chart comparison is additive. -/
theorem chartQuotientReduction_sub {d : ℕ} (hd : 0 < d) (a : powSections L d) (m n : ℕ)
    (σ σ' : Γ(natTensorPow L m, nvOpen L a)) :
    chartQuotientReduction L hL hd a s m n (σ - σ') =
      chartQuotientReduction L hL hd a s m n σ - chartQuotientReduction L hL hd a s m n σ' := by
  unfold chartQuotientReduction
  rw [chartMap_sub]
  exact map_sub _ _ _

/-- **Two lifts of the same section of the quotient have the same reduced chart image**, on any
affine chart with a degree-one factor. -/
theorem chartQuotientReduction_eq_of_quotPi_eq {d : ℕ} (hd : 0 < d) (a : powSections L d)
    (t : powSections L 1) {k : ℕ} {c : sectionRing L} (hc : c ∈ grading L k) (hk : 1 + k = d)
    (hac : DirectSum.of (powSections L) 1 t * c = DirectSum.of (powSections L) d a)
    (haff : IsAffineOpen (nvOpen L a)) (m n : ℕ) [(natTensorPow L m).IsQuasicoherent]
    {σ σ' : Γ(natTensorPow L m, nvOpen L a)}
    (h : (quotPi L s m n).app (nvOpen L a) σ = (quotPi L s m n).app (nvOpen L a) σ') :
    chartQuotientReduction L hL hd a s m n σ = chartQuotientReduction L hL hd a s m n σ' := by
  rw [← sub_eq_zero, ← chartQuotientReduction_sub,
    chartQuotientReduction_eq_zero_iff L hL hd a t hc hk hac haff s m n, map_sub, h, sub_self]

/-- The reduced chart image determines the section of the quotient on the chart. -/
theorem quotPi_eq_of_chartQuotientReduction_eq {d : ℕ} (hd : 0 < d) (a : powSections L d)
    (t : powSections L 1) {k : ℕ} {c : sectionRing L} (hc : c ∈ grading L k) (hk : 1 + k = d)
    (hac : DirectSum.of (powSections L) 1 t * c = DirectSum.of (powSections L) d a)
    (haff : IsAffineOpen (nvOpen L a)) (m n : ℕ) [(natTensorPow L m).IsQuasicoherent]
    {σ σ' : Γ(natTensorPow L m, nvOpen L a)}
    (h : chartQuotientReduction L hL hd a s m n σ = chartQuotientReduction L hL hd a s m n σ') :
    (quotPi L s m n).app (nvOpen L a) σ = (quotPi L s m n).app (nvOpen L a) σ' := by
  rw [← sub_eq_zero, ← map_sub, ← chartQuotientReduction_eq_zero_iff L hL hd a t hc hk hac haff s
    m n, chartQuotientReduction_sub, h, sub_self]

/-- Reducing a singleton chart modulo `f^{n+1}` is the reduced chart comparison. -/
theorem cechModMap_singletonChart (m n : ℕ) (j : Fin r)
    (σ : Γ(natTensorPow L m, nvOpen L (fam j))) :
    cechModMap (famRing L fam) (quotProj L s n) {j} (singletonChart L hL fam j m σ) =
      localizedModuleAwayCongr (prod_singleton_famRing L fam j)
        (chartQuotientReduction L hL one_pos (fam j) s m n σ) :=
  cechModMap_localizedModuleAwayCongr _ _ _ _ _

/-- Reducing a pair chart modulo `f^{n+1}` is the reduced chart comparison. -/
theorem cechModMap_pairChart (m n : ℕ) {a b : Fin r} (hab : a ≠ b)
    (σ : Γ(natTensorPow L m, nvOpen L (Stacks.GradedSections.mul (fam a) (fam b)))) :
    cechModMap (famRing L fam) (quotProj L s n) {a, b} (pairChart L hL fam hab m σ) =
      localizedModuleAwayCongr (prod_pair_famRing L fam hab)
        (chartQuotientReduction L hL (by norm_num) (Stacks.GradedSections.mul (fam a) (fam b))
          s m n σ) :=
  cechModMap_localizedModuleAwayCongr _ _ _ _ _

variable (haff : ∀ j, IsAffineOpen (nvOpen L (fam j)))

omit [Ample.IsInvertibleModule X L] in
/-- The singleton chart `X_{t_j}` has the degree-one factor `t_j`. -/
theorem singleton_factor (j : Fin r) :
    DirectSum.of (powSections L) 1 (fam j) * 1 = DirectSum.of (powSections L) 1 (fam j) :=
  mul_one _

omit [Ample.IsInvertibleModule X L] in
/-- The pair chart `X_{t_a t_b}` has the degree-one factor `t_a`. -/
theorem pair_factor (a b : Fin r) :
    DirectSum.of (powSections L) 1 (fam a) * famRing L fam b =
      DirectSum.of (powSections L) (1 + 1) (Stacks.GradedSections.mul (fam a) (fam b)) :=
  (Stacks.SectionRingChartMap.of_mul_eq L (fam a) (fam b)).symm

section Quotient

variable (m : ℕ) [(natTensorPow L m).IsQuasicoherent]

include haff in
/-- The restriction to the affine chart `X_{t_j}` of a global section of the quotient of
`L^{⊗ m}` by the `(n + 1)`-st power of the ideal of the zero scheme of `s` lifts to a section of
`L^{⊗ m}` over `X_{t_j}`. -/
theorem exists_quotPi_app_eq (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) (j : Fin r) :
    ∃ σ : Γ(natTensorPow L m, nvOpen L (fam j)), (quotPi L s m n).app (nvOpen L (fam j)) σ =
      (Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
        (natTensorPow L m)).presheaf.map (homOfLE le_top).op y :=
  AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen (quotPi L s m n) (haff j) _

/-- The coordinates of the Čech cocycle of a section of the ideal-power quotient: the reduced
chart images of local lifts. -/
def quotCechCoords (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) (j : Fin r) :
    Cech.cechMod (famRing L fam) ((powerQuotientShortComplex (sectionDegreeOne L s)
      (sectionRingModule (L := L)) (n + 1)).X₃ : Type u) {j} :=
  cechModMap (famRing L fam) (quotProj L s n) {j}
    (singletonChart L hL fam j m (exists_quotPi_app_eq L fam s haff m n y j).choose)

/-- The coordinates of the cocycle of a quotient section do not depend on the lifts. -/
theorem quotCechCoords_eq (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) (j : Fin r) (σ : Γ(natTensorPow L m, nvOpen L (fam j)))
    (hσ : (quotPi L s m n).app (nvOpen L (fam j)) σ =
      (Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
        (natTensorPow L m)).presheaf.map (homOfLE le_top).op y) :
    quotCechCoords L hL fam s haff m n y j =
      cechModMap (famRing L fam) (quotProj L s n) {j} (singletonChart L hL fam j m σ) := by
  rw [quotCechCoords, cechModMap_singletonChart, cechModMap_singletonChart]
  congr 1
  exact chartQuotientReduction_eq_of_quotPi_eq L hL s one_pos (fam j) (fam j)
    SetLike.GradedOne.one_mem rfl (singleton_factor L fam j) (haff j) m n
    ((exists_quotPi_app_eq L fam s haff m n y j).choose_spec.trans hσ.symm)

/-- The coordinates of the cocycle of a quotient section are Čech compatible. -/
theorem quotCechCoords_mem_cechCompatible (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) :
    quotCechCoords L hL fam s haff m n y ∈
      Stacks.LocalCohomology.cechCompatible (famRing L fam)
        (powerQuotientShortComplex (sectionDegreeOne L s) (sectionRingModule (L := L))
          (n + 1)).X₃ := by
  refine mem_cechCompatible_of_pairs _ _ _ fun a b hab => ?_
  set σa := (exists_quotPi_app_eq L fam s haff m n y a).choose
  set σb := (exists_quotPi_app_eq L fam s haff m n y b).choose
  change Cech.cechι _ _ _ (cechModMap (famRing L fam) (quotProj L s n) {a}
      (singletonChart L hL fam a m σa)) =
    Cech.cechι _ _ _ (cechModMap (famRing L fam) (quotProj L s n) {b}
      (singletonChart L hL fam b m σb))
  have hred : chartQuotientReduction L hL (by norm_num) (Stacks.GradedSections.mul (fam a) (fam b))
      s m n ((natTensorPow L m).presheaf.map (homOfLE (nvOpen_mul_le_left L fam a b)).op σa) =
      chartQuotientReduction L hL (by norm_num) (Stacks.GradedSections.mul (fam a) (fam b))
      s m n ((natTensorPow L m).presheaf.map (homOfLE (nvOpen_mul_le_right L fam a b)).op σb) := by
    refine chartQuotientReduction_eq_of_quotPi_eq L hL s _ _ (fam a)
      (Stacks.ExternalGrading.of_mem_summand 1 (fam b)) rfl (pair_factor L fam a b)
      (isAffineOpen_nvOpen_mul L fam haff a b) m n ?_
    rw [modulesHom_app_presheaf_map, modulesHom_app_presheaf_map,
      (exists_quotPi_app_eq L fam s haff m n y a).choose_spec,
      (exists_quotPi_app_eq L fam s haff m n y b).choose_spec, presheaf_map_homOfLE_comp,
      presheaf_map_homOfLE_comp]
  refine (Stacks.LocalCohomology.cechι_cechModMap (famRing L fam) (quotProj L s n) _
    (singletonChart L hL fam a m σa)).trans ?_
  refine Eq.trans ?_ (Stacks.LocalCohomology.cechι_cechModMap (famRing L fam) (quotProj L s n) _
    (singletonChart L hL fam b m σb)).symm
  refine (congrArg (cechModMap (famRing L fam) (quotProj L s n) {a, b})
    (cechι_singletonChart_left L hL fam hab m σa)).trans ?_
  refine Eq.trans ?_ (congrArg (cechModMap (famRing L fam) (quotProj L s n) {a, b})
    (cechι_singletonChart_right L hL fam hab m σb)).symm
  refine (cechModMap_pairChart L hL fam s m n hab _).trans ?_
  refine Eq.trans ?_ (cechModMap_pairChart L hL fam s m n hab _).symm
  exact congrArg _ hred

/-- **The Čech cocycle of a section of `L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}`.** -/
def quotCechSection (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) :
    LinearMap.ker (Cech.cechD (famRing L fam) ((powerQuotientShortComplex (sectionDegreeOne L s)
      (sectionRingModule (L := L)) (n + 1)).X₃ : Type u) 1) :=
  (Stacks.LocalCohomology.kerCechDOneEquivCechCompatible (famRing L fam) _).symm
    ⟨quotCechCoords L hL fam s haff m n y, quotCechCoords_mem_cechCompatible L hL fam s haff m n y⟩

/-- The coordinates of the cocycle of a quotient section. -/
theorem cechTermOneEquiv_quotCechSection (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) (j : Fin r) :
    Stacks.LocalCohomology.cechTermOneEquiv (famRing L fam) _
        (quotCechSection L hL fam s haff m n y).1 j = quotCechCoords L hL fam s haff m n y j := by
  change Stacks.LocalCohomology.cechTermOneEquiv _ _
      ((Stacks.LocalCohomology.cechTermOneEquiv _ _).symm _) j = _
  rw [LinearEquiv.apply_symm_apply]

/-- The Čech cocycle of a section of the quotient has degree `m`. -/
theorem quotCechSection_mem_kerDegree (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 1)
      (natTensorPow L m), ⊤)) :
    quotCechSection L hL fam s haff m n y ∈ kerDegree (grading L) (famRing L fam)
      (powerQuotientShortComplex (sectionDegreeOne L s) (sectionRingModule (L := L)) (n + 1)).X₃
      (quotientTowerPiece (sectionRingModule (L := L))
        (integerGrading (S := sectionRing L) (grading L)) (sectionDegreeOne L s) (n + 1))
      (m : ℤ) := by
  refine (mem_gradedCechTerm_one_iff _ _ _ _ _ _).2 fun j => ?_
  change Stacks.LocalCohomology.cechTermOneEquiv _ _ (quotCechSection L hL fam s haff m n y).1 j ∈ _
  rw [cechTermOneEquiv_quotCechSection]
  exact cechModMap_mem_gradedPiece (𝒜 := grading L) (fam := famRing L fam)
    (hc := fun i => Stacks.ExternalGrading.of_mem_summand 1 (fam i))
    (P := sectionRingModule (L := L))
    (𝒢 := integerGrading (S := sectionRing L) (grading L))
    (𝒢' := quotientTowerPiece (sectionRingModule (L := L))
      (integerGrading (S := sectionRing L) (grading L)) (sectionDegreeOne L s) (n + 1))
    (g := quotProj L s n)
    (mem_quotientTowerPiece_g _ _ _ (n + 1)) {j} (singletonChart_mem L hL fam j m _)

/-- **The cocycle of the reduction is the reduction of the cocycle.** -/
theorem towerReduction_globalCechSection (n : ℕ) (σ : Γ(natTensorPow L m, ⊤)) :
    towerReduction (famRing L fam) (sectionRingModule (L := L)) (sectionDegreeOne L s) (n + 1)
        (globalCechSection L hL fam m σ) =
      quotCechSection L hL fam s haff m n ((quotPi L s m n).app ⊤ σ) := by
  refine kerCechDOne_ext _ _ fun j => ?_
  rw [cechTermOneEquiv_quotCechSection]
  refine Eq.trans ?_ (quotCechCoords_eq L hL fam s haff m n _ j _
    (modulesHom_app_presheaf_map (quotPi L s m n) (homOfLE le_top) σ)).symm
  exact (Stacks.LocalCohomology.cechTermOneEquiv_cechTermMap (famRing L fam) (quotProj L s n)
    _ j).trans (congrArg _ (cechTermOneEquiv_globalCechSection L hL fam m σ j))

/-- **Compatibility with the transition maps.** -/
theorem towerTransition_quotCechSection (n : ℕ)
    (y : Γ(Stacks.Algebraization.idealPowerQuotient (AlgebraicGeometry.zeroScheme X L s) (n + 2)
      (natTensorPow L m), ⊤)) :
    towerTransition (famRing L fam) (sectionRingModule (L := L)) (sectionDegreeOne L s)
        (Nat.le_succ (n + 1)) (quotCechSection L hL fam s haff m (n + 1) y) =
      quotCechSection L hL fam s haff m n
        ((idealPowerQuotientMap _ _ (idealSheafData_pow_le_pow _ (Nat.le_succ (n + 1)))
          (natTensorPow L m)).app ⊤ y) := by
  refine kerCechDOne_ext _ _ fun j => ?_
  set σ := (exists_quotPi_app_eq L fam s haff m (n + 1) y j).choose
  have hσ := (exists_quotPi_app_eq L fam s haff m (n + 1) y j).choose_spec
  rw [cechTermOneEquiv_quotCechSection]
  refine Eq.trans ?_ (quotCechCoords_eq L hL fam s haff m n _ j σ ?_).symm
  · refine (Stacks.LocalCohomology.cechTermOneEquiv_cechTermMap (famRing L fam) _ _ j).trans ?_
    refine (congrArg (cechModMap (famRing L fam) _ {j})
      (cechTermOneEquiv_quotCechSection L hL fam s haff m (n + 1) y j)).trans ?_
    refine (LinearMap.comp_apply _ _ _).symm.trans ?_
    rw [← Stacks.LocalCohomology.cechModMap_comp,
      Stacks.Algebraization.powerQuotient_g_comp_τ₃]
    rfl
  · have hπ := π_idealPowerQuotientMap (AlgebraicGeometry.zeroScheme X L s)
      (AlgebraicGeometry.zeroScheme X L s) (idealSheafData_pow_le_pow _ (Nat.le_succ (n + 1)))
      (natTensorPow L m)
    have h1 : (quotPi L s m n).app (nvOpen L (fam j)) σ =
        (idealPowerQuotientMap _ _ (idealSheafData_pow_le_pow _ (Nat.le_succ (n + 1)))
          (natTensorPow L m)).app (nvOpen L (fam j)) ((quotPi L s m (n + 1)).app _ σ) := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hπ]
    rw [h1, hσ, modulesHom_app_presheaf_map]

/-- **The cocycle determines the section of the quotient.** -/
theorem quotCechSection_injective (hcov : ⨆ j, nvOpen L (fam j) = ⊤) (n : ℕ) :
    Function.Injective (quotCechSection L hL fam s haff m n) := by
  intro y y' h
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨_, (Stacks.Algebraization.idealPowerQuotient
    (AlgebraicGeometry.zeroScheme X L s) (n + 1) (natTensorPow L m)).isSheaf⟩)
    (fun j => nvOpen L (fam j)) ⊤ (fun j => homOfLE le_top) hcov.ge y y' fun j => ?_
  have hj := congrArg (fun x => Stacks.LocalCohomology.cechTermOneEquiv (famRing L fam) _ x.1 j) h
  simp only [cechTermOneEquiv_quotCechSection] at hj
  set σ := (exists_quotPi_app_eq L fam s haff m n y j).choose
  set σ' := (exists_quotPi_app_eq L fam s haff m n y' j).choose
  rw [quotCechCoords, quotCechCoords, cechModMap_singletonChart, cechModMap_singletonChart] at hj
  have hred := (localizedModuleAwayCongr (prod_singleton_famRing L fam j)).injective hj
  have := quotPi_eq_of_chartQuotientReduction_eq L hL s one_pos (fam j) (fam j)
    SetLike.GradedOne.one_mem rfl (singleton_factor L fam j) (haff j) m n hred
  rw [(exists_quotPi_app_eq L fam s haff m n y j).choose_spec,
    (exists_quotPi_app_eq L fam s haff m n y' j).choose_spec] at this
  exact this

end Quotient

end Stacks.Algebraization.SectionRingCone

end
