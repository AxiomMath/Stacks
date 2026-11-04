module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ChartCechSections.ChartIdeal
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Consumers

/-!
# The charts of a degree-one cover and the Čech complex of the section ring

Let `L` be an ample invertible module on `X`, `A = Γ_*(X, L)`, and let `t₁, …, t_r ∈ A₁` be
degree-one sections whose nonvanishing opens `X_{t_j}` are affine and cover `X`. The extended
Čech complex `C^•(t; A)` of `Stacks.LocalCohomology` has the localizations `A_{t_j}` in degree one
and `A_{t_j t_k}` in degree two. This file identifies, for every `m ≥ 0`, the sections of
`L^{⊗ m}` over the charts with the degree-`m` parts of those localizations
(`singletonChart`, `pairChart`) and shows that restriction from `X_{t_j}` to `X_{t_j t_k}` is the
transition map of the Čech complex.

The localizations of the Čech complex are taken at the products `∏_{i ∈ s} t_i`, while the chart
identification of `Stacks.Algebraization.SectionRingCone.chartSectionsEquiv` is taken at a single
homogeneous element; `localizedModuleAwayCongr` moves between localizations at equal elements.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.singletonChart`, `pairChart` — the chart maps into the
  Čech terms.

## Main results

* `Stacks.Algebraization.SectionRingCone.cechι_singletonChart_left`, `cechι_singletonChart_right`
  — restriction is the Čech transition map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.SectionRingProjQuasicoherent (unitSec)

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

universe u

namespace Stacks.Algebraization.SectionRingCone

/-! ### Localizations at equal elements -/

section Congr

variable {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]

/-- The localizations of a module at the powers of two equal elements are the same. -/
def localizedModuleAwayCongr {g g' : R} (h : g = g') :
    LocalizedModule (Submonoid.powers g) P ≃ₗ[R] LocalizedModule (Submonoid.powers g') P := by
  subst h; exact LinearEquiv.refl R _

/-- `localizedModuleAwayCongr` on a fraction. -/
theorem localizedModuleAwayCongr_mk {g g' : R} (h : g = g') (x : P) (n : ℕ) :
    localizedModuleAwayCongr h (LocalizedModule.mk x (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)) =
      LocalizedModule.mk x (⟨g' ^ n, n, rfl⟩ : Submonoid.powers g') := by
  subst h; rfl

/-- `localizedModuleAwayCongr` commutes with the maps induced on localizations. -/
theorem localizedModuleAwayCongr_map {Q : Type*} [AddCommGroup Q] [Module R Q] {g g' : R}
    (h : g = g') (q : P →ₗ[R] Q) (z : LocalizedModule (Submonoid.powers g) P) :
    localizedModuleAwayCongr h (LocalizedModule.map (Submonoid.powers g) q z) =
      LocalizedModule.map (Submonoid.powers g') q (localizedModuleAwayCongr h z) := by
  subst h; rfl

/-- `localizedModuleAwayCongr` preserves the graded pieces. -/
theorem mem_gradedPiece_localizedModuleAwayCongr {σ' τ' : Type*} [SetLike σ' R] [SetLike τ' P]
    (𝒜 : ℕ → σ') (𝒢 : ℤ → τ') {g g' : R} (h : g = g') (e : ℤ)
    {z : LocalizedModule (Submonoid.powers g) P}
    (hz : z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒢 g e) :
    localizedModuleAwayCongr h z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒢 g' e := by
  subst h; exact hz

/-- `localizedModuleAwayCongr` reflects the graded pieces. -/
theorem mem_gradedPiece_of_localizedModuleAwayCongr {σ' τ' : Type*} [SetLike σ' R]
    [SetLike τ' P] (𝒜 : ℕ → σ') (𝒢 : ℤ → τ') {g g' : R} (h : g = g') (e : ℤ)
    {z : LocalizedModule (Submonoid.powers g) P}
    (hz : localizedModuleAwayCongr h z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒢 g' e) :
    z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒢 g e := by
  subst h; exact hz

end Congr

/-! ### The charts -/

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) {r : ℕ} (fam : Fin r → powSections L 1)

/-- The cover as elements of the section ring. -/
abbrev famRing : Fin r → sectionRing L := fun j => DirectSum.of (powSections L) 1 (fam j)

/-- The Čech denominator of a singleton. -/
theorem prod_singleton_famRing (j : Fin r) :
    DirectSum.of (powSections L) 1 (fam j) = ∏ i ∈ ({j} : Finset (Fin r)), famRing L fam i :=
  (Finset.prod_singleton _ _).symm

/-- The Čech denominator of a pair is the product of the two sections. -/
theorem prod_pair_famRing {a b : Fin r} (hab : a ≠ b) :
    DirectSum.of (powSections L) (1 + 1) (Stacks.GradedSections.mul (fam a) (fam b)) =
      ∏ i ∈ ({a, b} : Finset (Fin r)), famRing L fam i := by
  rw [Finset.prod_pair hab, Stacks.SectionRingChartMap.of_mul_eq]

/-- The chart of a product lies in the chart of the left factor. -/
theorem nvOpen_mul_le_left (a b : Fin r) :
    nvOpen L (Stacks.GradedSections.mul (fam a) (fam b)) ≤ nvOpen L (fam a) := by
  rw [Stacks.SectionRingChartMap.nvOpen_mul]; exact inf_le_left

/-- The chart of a product lies in the chart of the right factor. -/
theorem nvOpen_mul_le_right (a b : Fin r) :
    nvOpen L (Stacks.GradedSections.mul (fam a) (fam b)) ≤ nvOpen L (fam b) := by
  rw [Stacks.SectionRingChartMap.nvOpen_mul]; exact inf_le_right

/-- The chart over a product of two affine charts is affine. -/
theorem isAffineOpen_nvOpen_mul (haff : ∀ j, IsAffineOpen (nvOpen L (fam j))) (a b : Fin r) :
    IsAffineOpen (nvOpen L (Stacks.GradedSections.mul (fam a) (fam b))) := by
  rw [Stacks.SectionRingChartMap.nvOpen_mul]
  exact Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nvOpen L (fam b) (haff a)

/-- **The chart at `X_{t_j}`**: a section of `L^{⊗ m}` over `X_{t_j}` as an element of the
degree-one Čech term `A_{t_j}`. -/
def singletonChart (j : Fin r) (m : ℕ) (σ : Γ(natTensorPow L m, nvOpen L (fam j))) :
    Cech.cechMod (famRing L fam) (sectionRing L) {j} :=
  localizedModuleAwayCongr (prod_singleton_famRing L fam j) (chartMap L hL one_pos (fam j) m σ)

/-- **The chart at `X_{t_a t_b}`**: a section of `L^{⊗ m}` over `X_{t_a t_b}` as an element of
the degree-two Čech term `A_{t_a t_b}`. -/
def pairChart {a b : Fin r} (hab : a ≠ b) (m : ℕ)
    (σ : Γ(natTensorPow L m, nvOpen L (Stacks.GradedSections.mul (fam a) (fam b)))) :
    Cech.cechMod (famRing L fam) (sectionRing L) {a, b} :=
  localizedModuleAwayCongr (prod_pair_famRing L fam hab)
    (chartMap L hL (by norm_num) (Stacks.GradedSections.mul (fam a) (fam b)) m σ)

/-- The chart of a section of `L^{⊗ m}` has degree `m`. -/
theorem singletonChart_mem (j : Fin r) (m : ℕ) (σ : Γ(natTensorPow L m, nvOpen L (fam j))) :
    singletonChart L hL fam j m σ ∈ Stacks.GradedLocalization.gradedPiece (grading L)
      (integerGrading (S := sectionRing L) (grading L))
      (∏ i ∈ ({j} : Finset (Fin r)), famRing L fam i) (m : ℤ) :=
  mem_gradedPiece_localizedModuleAwayCongr _ _ _ _ (chartSectionsEquiv L hL one_pos (fam j) m σ).2

/-- The singleton chart map is injective. -/
theorem singletonChart_injective (j : Fin r) (m : ℕ) :
    Function.Injective (singletonChart L hL fam j m) :=
  (localizedModuleAwayCongr (prod_singleton_famRing L fam j)).injective.comp
    (chartMap_injective L hL one_pos (fam j) m)

/-- The pair chart map is injective. -/
theorem pairChart_injective {a b : Fin r} (hab : a ≠ b) (m : ℕ) :
    Function.Injective (pairChart L hL fam hab m) :=
  (localizedModuleAwayCongr (prod_pair_famRing L fam hab)).injective.comp
    (chartMap_injective L hL _ _ m)

/-- Every degree-`m` element of `A_{t_j}` comes from a section over `X_{t_j}`. -/
theorem exists_singletonChart_eq (j : Fin r) (m : ℕ)
    (z : Cech.cechMod (famRing L fam) (sectionRing L) {j})
    (hz : z ∈ Stacks.GradedLocalization.gradedPiece (grading L)
      (integerGrading (S := sectionRing L) (grading L))
      (∏ i ∈ ({j} : Finset (Fin r)), famRing L fam i) (m : ℤ)) :
    ∃ σ, singletonChart L hL fam j m σ = z := by
  set e := localizedModuleAwayCongr (P := sectionRing L) (prod_singleton_famRing L fam j)
  have hz' : e.symm z ∈ Stacks.GradedLocalization.gradedPiece (grading L)
      (integerGrading (S := sectionRing L) (grading L))
      (DirectSum.of (powSections L) 1 (fam j)) (m : ℤ) :=
    mem_gradedPiece_of_localizedModuleAwayCongr _ _ (prod_singleton_famRing L fam j) _
      (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  refine ⟨(chartSectionsEquiv L hL one_pos (fam j) m).symm ⟨_, hz'⟩, ?_⟩
  show e (chartMap L hL one_pos (fam j) m _) = z
  rw [chartMap, AddEquiv.apply_symm_apply]
  exact e.apply_symm_apply z

/-- The two-element set minus one of its elements. -/
theorem pair_sdiff_left {a b : Fin r} (hab : a ≠ b) :
    ({a, b} : Finset (Fin r)) \ {a} = {b} := by
  ext i; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact absurd h h'
    · exact h
  · rintro rfl; exact ⟨Or.inr rfl, fun h => hab h.symm⟩

/-- The two-element set minus its second element. -/
theorem pair_sdiff_right {a b : Fin r} (hab : a ≠ b) :
    ({a, b} : Finset (Fin r)) \ {b} = {a} := by
  rw [Finset.pair_comm]; exact pair_sdiff_left hab.symm

/-- A section of degree `m` in the chart `A_g` is a fraction `y / g ^ n`. -/
theorem exists_chartMap_eq_mk {d : ℕ} (hd : 0 < d) (a : powSections L d) (m : ℕ)
    (σ : Γ(natTensorPow L m, nvOpen L a)) :
    ∃ (n : ℕ) (y : sectionRing L), chartMap L hL hd a m σ =
      LocalizedModule.mk y (⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩ :
        Submonoid.powers (DirectSum.of (powSections L) d a)) := by
  obtain ⟨n, y, -, h⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff (grading L)
    (integerGrading (S := sectionRing L) (grading L))
    (Stacks.ExternalGrading.of_mem_summand d a) (m : ℤ) _).1
    (chartSectionsEquiv L hL hd a m σ).2
  exact ⟨n, y, h⟩

/-- Restriction from `X_{t_c}` to `X_{t_a t_b}` is the Čech transition map, for `{a, b} = {c, e}`
and `t_a t_b = t_c t_e`. -/
private theorem cechι_singletonChart_eq_pairChart {a b c e : Fin r} (hab : a ≠ b)
    (hc : ({c} : Finset (Fin r)) ⊆ {a, b}) (hdiff : ({a, b} : Finset (Fin r)) \ {c} = {e})
    (hq : DirectSum.of (powSections L) 1 (fam c) * DirectSum.of (powSections L) 1 (fam e) =
      DirectSum.of (powSections L) (1 + 1) (Stacks.GradedSections.mul (fam a) (fam b)))
    (i : nvOpen L (Stacks.GradedSections.mul (fam a) (fam b)) ⟶ nvOpen L (fam c)) (m : ℕ)
    (σ : Γ(natTensorPow L m, nvOpen L (fam c))) :
    Cech.cechι (famRing L fam) (sectionRing L) hc (singletonChart L hL fam c m σ) =
      pairChart L hL fam hab m ((natTensorPow L m).presheaf.map i.op σ) := by
  obtain ⟨n, y, hy⟩ := exists_chartMap_eq_mk L hL one_pos (fam c) m σ
  have hres := chartSectionsEquiv_restrict L hL one_pos (fam c) (d' := 1 + 1) (by norm_num)
    (Stacks.GradedSections.mul (fam a) (fam b)) (fam e) rfl hq i m σ n y hy
  rw [singletonChart, hy, localizedModuleAwayCongr_mk, Cech.cechι_mk_pow, pairChart, chartMap,
    hres, localizedModuleAwayCongr_mk, hdiff, Finset.prod_singleton, smul_eq_mul]

/-- **Restriction from `X_{t_a}` to `X_{t_a t_b}` is the Čech transition map.** -/
theorem cechι_singletonChart_left {a b : Fin r} (hab : a ≠ b) (m : ℕ)
    (σ : Γ(natTensorPow L m, nvOpen L (fam a))) :
    Cech.cechι (famRing L fam) (sectionRing L)
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_self a {b}))
        (singletonChart L hL fam a m σ) =
      pairChart L hL fam hab m ((natTensorPow L m).presheaf.map
        (homOfLE (nvOpen_mul_le_left L fam a b)).op σ) :=
  cechι_singletonChart_eq_pairChart L hL fam hab _ (pair_sdiff_left hab)
    (Stacks.SectionRingChartMap.of_mul_eq L (fam a) (fam b)).symm _ m σ

/-- **Restriction from `X_{t_b}` to `X_{t_a t_b}` is the Čech transition map.** -/
theorem cechι_singletonChart_right {a b : Fin r} (hab : a ≠ b) (m : ℕ)
    (σ : Γ(natTensorPow L m, nvOpen L (fam b))) :
    Cech.cechι (famRing L fam) (sectionRing L)
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
        (singletonChart L hL fam b m σ) =
      pairChart L hL fam hab m ((natTensorPow L m).presheaf.map
        (homOfLE (nvOpen_mul_le_right L fam a b)).op σ) :=
  cechι_singletonChart_eq_pairChart L hL fam hab _ (pair_sdiff_right hab)
    (by rw [Stacks.SectionRingChartMap.of_mul_eq, mul_comm]) _ m σ

end Stacks.Algebraization.SectionRingCone

end
