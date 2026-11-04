module

public import StacksFrontier.RingTheory.Cech.WeightedVariablesFormsVanishing
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationChart
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization

/-!
# The positive part of the localized forms, read on a chart

Let `A = R[x₁, …, x_m, y₁, …, y_n]`, graded by `deg yⱼ = 1`, and `g = ∏_{j ∈ t} yⱼ` for a
nonempty set `t` of indices. The localization `M_g` of the forms `M = Ω^a_{A/R}` is the module of
forms of `A_g`, and choosing `j ∈ t` identifies `A_g` with the Laurent algebra `A₍g₎[T;T⁻¹]`
(`Stacks.Truncation.Chart.laurentAlgEquiv`, `T ↦ yⱼ`). This file shows that under these
identifications **the positive part of `M_g`** — the sums of homogeneous elements of positive
weight, `Cech.WeightedVariables.posPart` — **is the space of forms of positive weight on
`A₍g₎[T;T⁻¹]`**, `PolynomialDeRham.Chart.posForms`. The first is the description of the Čech
complex used for the vanishing (`Cech.WeightedVariables.forms_exists_eq_cechD_of_posPart`), the
second is the description of the forms on the cone vanishing on the zero section
(`PolynomialDeRham.Chart.mem_posForms`).

## Main definitions

* `Cech.WeightedVariables.locFormsEquiv`: the identification `M_g ≃ Ω^a_{A_g/R}`.

## Main results

* `Cech.WeightedVariables.mem_posPart_iff`: **the two positive parts agree.**
-/

@[expose] public noncomputable section

open KaehlerDifferential LaurentPolynomial Polynomial

attribute [local instance] instVAddNatIntGradedLocalizedModule

universe u

namespace Cech.WeightedVariables

variable {R : Type u} [CommRing R] {m n : ℕ} (a : ℕ)

/-- The forms of `A_g`. -/
abbrev LocForms (g : Ring R m n) : Type u :=
  ⋀[Localization.Away g]^a (Ω[Localization.Away g⁄R])

section General

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The base change of forms `⋀^a Ω_{A/R} → ⋀^a Ω_{A_g/R}` is a localization at the powers of
`g`. -/
instance isLocalizedModule_mapExteriorPower_away (g : A) :
    IsLocalizedModule (Submonoid.powers g)
      (mapExteriorPower R A (Localization.Away g) a) :=
  IsLocalization.isLocalizedModule_of_exteriorPower (Localization.Away g)
    (map R R A (Localization.Away g)) a (Submonoid.powers g)
    ((mapExteriorPower R A (Localization.Away g) a).restrictScalars A)
    (mapExteriorPower_ιMulti R A (Localization.Away g) a)

/-- **The localization of the forms of `A` at `g` is the module of forms of `A_g`.** -/
def locFormsEquiv (g : A) :
    LocalizedModule (Submonoid.powers g) (⋀[A]^a (Ω[A⁄R])) ≃ₗ[A]
      ⋀[Localization.Away g]^a (Ω[Localization.Away g⁄R]) :=
  IsLocalizedModule.iso (Submonoid.powers g) (mapExteriorPower R A (Localization.Away g) a)

/-- The identification on a fraction `x / s` is `s⁻¹ · x`. -/
theorem locFormsEquiv_mk (g : A) (x : ⋀[A]^a (Ω[A⁄R])) (s : Submonoid.powers g) :
    locFormsEquiv a g (LocalizedModule.mk x s) =
      (Localization.mk 1 s : Localization.Away g) •
        mapExteriorPower R A (Localization.Away g) a x := by
  rw [locFormsEquiv, IsLocalizedModule.iso_apply_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff,
    ← algebraMap_smul (Localization.Away g) (s : A), smul_smul,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul,
    Localization.mk_self, one_smul]

end General

/-! ### The abstract computation -/

section Abstract

attribute [local instance] instVAddNatIntGradedLocalizedModule

variable {R A E : Type u} [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra R E]
  {g : A} (Λ : E[T;T⁻¹] ≃ₐ[R] Localization.Away g) (gr : ℤ → Submodule R A)

/-- **A homogeneous fraction of forms is a form of the same weight on the Laurent model**, as
soon as the functions of weight `w` on `A` are `c Tʷ` in the model and `1 / gᵏ` is `c T^{-kd}`. -/
theorem formsₛₗ_symm_smul_mapExteriorPower_mem (p : ℕ) {d : ℕ}
    (hmap : ∀ w b, b ∈ gr w →
      Λ.symm (algebraMap A (Localization.Away g) b) ∈ LaurentDeRham.weightGrading R E w)
    (k : ℕ) (c : E)
    (hc : Λ.symm (Localization.mk 1 ⟨g ^ k, k, rfl⟩) =
      LaurentPolynomial.C c * LaurentPolynomial.T (-((k : ℤ) * d)))
    {e : ℤ} {x : ⋀[A]^p (Ω[A⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p (e + k • (d : ℤ))) :
    formsₛₗ Λ.symm.toAlgHom p ((Localization.mk 1 ⟨g ^ k, k, rfl⟩ : Localization.Away g) •
      mapExteriorPower R A (Localization.Away g) p x) ∈ LaurentDeRham.weightComponent R E e p := by
  rw [map_smulₛₗ]
  have hω : formsₛₗ Λ.symm.toAlgHom p (mapExteriorPower R A (Localization.Away g) p x) ∈
      LaurentDeRham.weightComponent R E (e + k • (d : ℤ)) p := by
    rw [← formsₛₗ_toAlgHom, formsₛₗ_comp]
    exact formsₛₗ_mem_gradedDifferentialFormComponent _ (fun w b hb => hmap w b hb) hx
  have hc' : ((Λ.symm.toAlgHom : Localization.Away g →+* E[T;T⁻¹])
      (Localization.mk 1 ⟨g ^ k, k, rfl⟩)) =
      LaurentPolynomial.C c * LaurentPolynomial.T (-((k : ℤ) * d)) := hc
  rw [hc', mul_smul]
  have hT := (LaurentDeRham.map_smulTEquiv_weightComponent R E (e + k • (d : ℤ))
    (-((k : ℤ) * d)) p).le ⟨_, hω, rfl⟩
  have hdeg : -((k : ℤ) * d) + (e + k • (d : ℤ)) = e := by rw [nsmul_eq_mul]; ring
  rw [hdeg] at hT
  exact smul_mem_gradedDifferentialFormComponent
    (fun hi hj' => SetLike.mul_mem_graded hi hj') (LaurentDeRham.C_mem_weightGrading R E c) hT

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- **A homogeneous element of weight `e` of the localized forms is a form of weight `e` on the
Laurent model.** -/
theorem formsₛₗ_symm_locFormsEquiv_mem (p : ℕ)
    [SetLike.GradedSMul 𝒜 fun e : ℤ => gradedDifferentialFormComponent gr p e] {d : ℕ}
    (hg : g ∈ 𝒜 d)
    (hmap : ∀ w b, b ∈ gr w →
      Λ.symm (algebraMap A (Localization.Away g) b) ∈ LaurentDeRham.weightGrading R E w)
    (hcoef : ∀ k : ℕ, ∃ c : E, Λ.symm (Localization.mk 1 ⟨g ^ k, k, rfl⟩) =
      LaurentPolynomial.C c * LaurentPolynomial.T (-((k : ℤ) * d)))
    {e : ℤ} {z : LocalizedModule (Submonoid.powers g) (⋀[A]^p (Ω[A⁄R]))}
    (hz : z ∈ Stacks.GradedLocalization.gradedPiece 𝒜
      (fun e : ℤ => gradedDifferentialFormComponent gr p e) g e) :
    formsₛₗ Λ.symm.toAlgHom p (locFormsEquiv p g z) ∈ LaurentDeRham.weightComponent R E e p := by
  obtain ⟨k, x, hx, rfl⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 _ hg e z).1 hz
  obtain ⟨c, hc⟩ := hcoef k
  rw [locFormsEquiv_mk]
  exact formsₛₗ_symm_smul_mapExteriorPower_mem Λ gr p hmap k c hc hx

/-- The forms of positive weight on the Laurent model, carried back to `E[T;T⁻¹]`, are sums of
forms of positive weight. -/
theorem formsₛₗ_symm_mem_iSup_of_mem_posForms (p : ℕ) {η : ⋀[Localization.Away g]^p
      (Ω[Localization.Away g⁄R])}
    (hη : η ∈ PolynomialDeRham.Chart.posForms Λ p) :
    formsₛₗ Λ.symm.toAlgHom p η ∈
      ⨆ k : ℕ, LaurentDeRham.weightComponent R E ((k + 1 : ℕ) : ℤ) p := by
  induction hη using Submodule.iSup_induction' with
  | mem k η hη =>
      obtain ⟨ζ, hζ, rfl⟩ := hη
      rw [formsₗ_apply, formsₛₗ_symm_apply]
      exact Submodule.mem_iSup_of_mem k hζ
  | zero =>
      rw [map_zero]
      exact zero_mem _
  | add η η' _ _ h h' =>
      rw [map_add]
      exact add_mem h h'

/-- **An injective map of graded groups reflects positivity**: if `Φ` carries the degree-`e`
part of `M` into that of `N` and is injective, an element whose image is a sum of elements of
positive degree is itself a sum of elements of positive degree. -/
theorem mem_iSup_of_map_mem_iSup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R N]
    (𝓜 : ℤ → AddSubgroup M) [DirectSum.Decomposition 𝓜] (𝓝 : ℤ → Submodule R N)
    [DirectSum.Decomposition 𝓝] (Φ : M →+ N) (hinj : Function.Injective Φ)
    (hΦ : ∀ e x, x ∈ 𝓜 e → Φ x ∈ 𝓝 e) {z : M} (hz : Φ z ∈ ⨆ n : ℕ, 𝓝 ((n + 1 : ℕ) : ℤ)) :
    z ∈ ⨆ n : ℕ, 𝓜 ((n : ℤ) + 1) := by
  classical
  have hzsum : z = ∑ e ∈ DFinsupp.support (DirectSum.decompose 𝓜 z),
      (DirectSum.decompose 𝓜 z e : M) := (DirectSum.sum_support_decompose 𝓜 z).symm
  have hneg : ∀ e : ℤ, e ≤ 0 → (DirectSum.decompose 𝓝 (Φ z) e : N) = 0 := by
    intro e he
    generalize Φ z = w at hz
    induction hz using Submodule.iSup_induction' with
    | mem k w hw =>
        refine DirectSum.decompose_of_mem_ne 𝓝 hw ?_
        push_cast
        omega
    | zero => simp
    | add w w' _ _ h h' => simp [h, h']
  have hzero : ∀ e ∈ DFinsupp.support (DirectSum.decompose 𝓜 z), e ≤ 0 →
      (DirectSum.decompose 𝓜 z e : M) = 0 := by
    intro e he hle
    have h := hneg e hle
    rw [hzsum, map_sum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
      AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single_of_mem e he fun e' _ hne =>
        DirectSum.decompose_of_mem_ne 𝓝 (hΦ e' _ (DirectSum.decompose 𝓜 z e').2) hne,
      DirectSum.decompose_of_mem_same 𝓝 (hΦ e _ (DirectSum.decompose 𝓜 z e).2)] at h
    exact hinj (h.trans (map_zero Φ).symm)
  rw [hzsum]
  refine AddSubgroup.sum_mem _ fun e he => ?_
  by_cases hle : e ≤ 0
  · rw [hzero e he hle]
    exact zero_mem _
  · refine AddSubgroup.mem_iSup_of_mem (e - 1).toNat ?_
    rw [show ((e - 1).toNat : ℤ) + 1 = e by omega]
    exact (DirectSum.decompose 𝓜 z e).2

/-- **The positive part of the localized forms is the space of forms of positive weight on the
Laurent model.** -/
theorem mem_iSup_gradedPiece_iff (p : ℕ)
    [SetLike.GradedSMul 𝒜 fun e : ℤ => gradedDifferentialFormComponent gr p e]
    [DirectSum.Decomposition fun e : ℤ => gradedDifferentialFormComponent gr p e] {d : ℕ}
    (hg : g ∈ 𝒜 d)
    (hmap : ∀ w b, b ∈ gr w →
      Λ.symm (algebraMap A (Localization.Away g) b) ∈ LaurentDeRham.weightGrading R E w)
    (hcoef : ∀ k : ℕ, ∃ c : E, Λ.symm (Localization.mk 1 ⟨g ^ k, k, rfl⟩) =
      LaurentPolynomial.C c * LaurentPolynomial.T (-((k : ℤ) * d)))
    (z : LocalizedModule (Submonoid.powers g) (⋀[A]^p (Ω[A⁄R]))) :
    z ∈ (⨆ e : ℕ, Stacks.GradedLocalization.gradedPiece 𝒜
      (fun e : ℤ => gradedDifferentialFormComponent gr p e) g ((e : ℤ) + 1)) ↔
      locFormsEquiv p g z ∈ PolynomialDeRham.Chart.posForms Λ p := by
  classical
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · induction hz using AddSubgroup.iSup_induction' with
    | hp e z hz =>
        refine Submodule.mem_iSup_of_mem e ⟨formsₛₗ Λ.symm.toAlgHom p (locFormsEquiv p g z), ?_, ?_⟩
        · have := formsₛₗ_symm_locFormsEquiv_mem Λ gr p hg hmap hcoef hz
          push_cast at this ⊢
          exact this
        · rw [formsₗ_apply, formsₛₗ_apply_symm]
    | h1 =>
        rw [LinearEquiv.map_zero]
        exact (PolynomialDeRham.Chart.posForms Λ p).zero_mem
    | hadd z z' _ _ hz hz' =>
        rw [LinearEquiv.map_add]
        exact (PolynomialDeRham.Chart.posForms Λ p).add_mem hz hz'
  · let := Stacks.GradedLocalization.gradedDecomposition 𝒜
      (fun e : ℤ => gradedDifferentialFormComponent gr p e) hg
    let : DirectSum.Decomposition fun e : ℤ => LaurentDeRham.weightComponent R E e p :=
      (LaurentDeRham.isInternal_weightComponent R E p).chooseDecomposition
    exact mem_iSup_of_map_mem_iSup
      (Stacks.GradedLocalization.gradedPiece 𝒜
        (fun e : ℤ => gradedDifferentialFormComponent gr p e) g)
      (fun e : ℤ => LaurentDeRham.weightComponent R E e p)
      ((formsₗ Λ.symm.toAlgHom p).toAddMonoidHom.comp
        (locFormsEquiv p g).toLinearMap.toAddMonoidHom)
      ((formsₛₗ_injective Λ.symm p).comp (locFormsEquiv p g).injective)
      (fun e x hx => formsₛₗ_symm_locFormsEquiv_mem Λ gr p hg hmap hcoef hx)
      (formsₛₗ_symm_mem_iSup_of_mem_posForms Λ p hz)

end Abstract

/-! ### The chart of a set of indices -/

section Chart

variable {t : Finset (Fin n)} {j : Fin n}

/-- `yⱼ · ∏_{i ∈ t \ {j}} yᵢ = ∏_{i ∈ t} yᵢ` for `j ∈ t`. -/
theorem yVar_mul_prod_erase (hj : j ∈ t) :
    yVar R m n j * ∏ i ∈ t.erase j, yVar R m n i = ∏ i ∈ t, yVar R m n i :=
  Finset.mul_prod_erase t (yVar R m n) hj

/-- The degree of `∏_{j ∈ t} yⱼ`, written as the degree of the cofactor of `yⱼ` plus one. -/
theorem prod_yVar_mem_succ (hj : j ∈ t) :
    (∏ i ∈ t, yVar R m n i) ∈ natGrading R m n ((∑ _i ∈ t.erase j, 1) + 1) :=
  Stacks.GradedLaurent.mem_of_mul_eq (natGrading R m n) (yVar_mem R m n j)
    (prod_yVar_mem_natGrading (t.erase j)) (yVar_mul_prod_erase hj)

variable (R m) in
/-- **The Laurent chart of `A_g` attached to `j ∈ t`**, `A₍g₎[T;T⁻¹] ≅ A_g` with `T ↦ yⱼ`. -/
abbrev chartLaurent (hj : j ∈ t) :
    (HomogeneousLocalization.Away (natGrading R m n) (∏ i ∈ t, yVar R m n i))[T;T⁻¹] ≃ₐ[R]
      Localization.Away (∏ i ∈ t, yVar R m n i) :=
  Stacks.Truncation.Chart.laurentAlgEquiv (yVar_mem R m n j)
    (prod_yVar_mem_natGrading (t.erase j)) (yVar_mul_prod_erase hj)

variable (R m) in
/-- The degree-zero localization `A₍g₎`, `g = ∏_{j ∈ t} yⱼ`. -/
abbrev chartE (t : Finset (Fin n)) : Type u :=
  HomogeneousLocalization.Away (natGrading R m n) (∏ i ∈ t, yVar R m n i)

/-- A homogeneous fraction `x / gᵏ` of weight `w` is `c Tʷ` in the Laurent chart, explicitly. -/
theorem exists_chartLaurent_symm_mk_eq (hj : j ∈ t) {e k : ℕ} {x : Ring R m n}
    (hx : x ∈ natGrading R m n e) :
    ∃ c : chartE R m t, (chartLaurent R m hj).symm
      (Localization.mk x (Stacks.GradedLaurent.powSub _ k)) =
        LaurentPolynomial.C c * LaurentPolynomial.T
          ((e : ℤ) - k * ((∑ _i ∈ t.erase j, 1 : ℕ) + 1 : ℕ)) := by
  obtain ⟨c, hc⟩ := Stacks.GradedLaurent.exists_mk_eq_val_mul_zpow (natGrading R m n)
    (yVar_mem R m n j) (prod_yVar_mem_natGrading (t.erase j)) (yVar_mul_prod_erase hj) hx k
  refine ⟨c, ?_⟩
  rw [AlgEquiv.symm_apply_eq, Stacks.Truncation.Chart.laurentAlgEquiv_apply, map_mul,
    Stacks.GradedLaurent.laurentDivisorHom_C, Stacks.GradedLaurent.laurentDivisorHom_T, hc]
  push_cast
  rfl

/-- A homogeneous fraction `x / gᵏ` of weight `w` is `c Tʷ` in the Laurent chart. -/
theorem chartLaurent_symm_mk_mem (hj : j ∈ t) {e k : ℕ} {x : Ring R m n}
    (hx : x ∈ natGrading R m n e) :
    (chartLaurent R m hj).symm (Localization.mk x (Stacks.GradedLaurent.powSub _ k)) ∈
      LaurentDeRham.weightGrading R (chartE R m t)
        ((e : ℤ) - k * ((∑ _i ∈ t.erase j, 1 : ℕ) + 1 : ℕ)) := by
  obtain ⟨c, hc⟩ := exists_chartLaurent_symm_mk_eq hj (k := k) hx
  rw [hc, ← LaurentPolynomial.single_eq_C_mul_T]
  exact LaurentDeRham.single_mem_weightGrading R _ _ c

/-- A function of weight `w` on `A` is `c Tʷ` in the Laurent chart. -/
theorem chartLaurent_symm_algebraMap_mem (hj : j ∈ t) {w : ℤ} {b : Ring R m n}
    (hb : b ∈ intGrading R m n w) :
    (chartLaurent R m hj).symm
      (algebraMap (Ring R m n) (Localization.Away (∏ i ∈ t, yVar R m n i)) b)
      ∈ LaurentDeRham.weightGrading R (chartE R m t) w := by
  rcases lt_or_ge w 0 with hw | hw
  · have hb0 : b = 0 := by
      refine MvPolynomial.ext _ _ fun μ => ?_
      by_contra hμ
      have := hb (by simpa using hμ)
      rw [weight_int] at this
      omega
    rw [hb0, map_zero, map_zero]
    exact zero_mem _
  · obtain ⟨w', rfl⟩ := Int.eq_ofNat_of_zero_le hw
    have hb' : b ∈ natGrading R m n w' := by
      intro μ hμ
      have := hb hμ
      rw [weight_int] at this
      exact_mod_cast this
    have h := chartLaurent_symm_mk_mem hj (k := 0) hb'
    have h1 : (Localization.mk b (Stacks.GradedLaurent.powSub (∏ i ∈ t, yVar R m n i) 0) :
        Localization.Away (∏ i ∈ t, yVar R m n i)) = algebraMap _ _ b := by
      rw [← Localization.mk_one_eq_algebraMap]
      congr 1
    rw [h1] at h
    simpa using h

/-- `1 / gᵏ` is `c T^{-k deg g}` in the Laurent chart. -/
theorem chartLaurent_coef (hj : j ∈ t) (k : ℕ) :
    ∃ c : chartE R m t, (chartLaurent R m hj).symm
      (Localization.mk 1 ⟨(∏ i ∈ t, yVar R m n i) ^ k, k, rfl⟩) =
        LaurentPolynomial.C c * LaurentPolynomial.T
          (-((k : ℤ) * (((∑ _i ∈ t.erase j, 1 : ℕ) + 1 : ℕ) : ℤ))) := by
  obtain ⟨c, hc⟩ := exists_chartLaurent_symm_mk_eq (R := R) (m := m) hj (e := 0) (k := k)
    (x := 1) (SetLike.one_mem_graded (natGrading R m n))
  refine ⟨c, ?_⟩
  rw [show (Localization.mk 1 ⟨(∏ i ∈ t, yVar R m n i) ^ k, k, rfl⟩ :
      Localization.Away (∏ i ∈ t, yVar R m n i)) =
    Localization.mk 1 (Stacks.GradedLaurent.powSub _ k) from rfl, hc]
  push_cast
  ring_nf

/-- **A homogeneous element of weight `e` of `M_g` is a form of weight `e` in the Laurent
chart.** -/
theorem formsₛₗ_chartLaurent_symm_mem (hj : j ∈ t) {e : ℤ}
    {z : cechMod (yVar R m n) (Forms R m n a) t}
    (hz : z ∈ Stacks.GradedLocalization.gradedPiece (natGrading R m n) (formsGrading R m n a)
      (∏ i ∈ t, yVar R m n i) e) :
    formsₛₗ (chartLaurent R m hj).symm.toAlgHom a (locFormsEquiv a _ z) ∈
      LaurentDeRham.weightComponent R (chartE R m t) e a :=
  formsₛₗ_symm_locFormsEquiv_mem (chartLaurent R m hj) (intGrading R m n) a
    (prod_yVar_mem_succ hj)
    (fun _ _ hb => chartLaurent_symm_algebraMap_mem (R := R) (m := m) hj hb)
    (chartLaurent_coef hj) hz

/-- **The positive part of `M_g` is the space of forms of positive weight on the Laurent
chart.** -/
theorem mem_posPart_iff (hj : j ∈ t) (z : cechMod (yVar R m n) (Forms R m n a) t) :
    z ∈ posPart R m n a t ↔
      locFormsEquiv a _ z ∈ PolynomialDeRham.Chart.posForms (chartLaurent R m hj) a :=
  mem_iSup_gradedPiece_iff (chartLaurent R m hj) (intGrading R m n) a (prod_yVar_mem_succ hj)
    (fun _ _ hb => chartLaurent_symm_algebraMap_mem (R := R) (m := m) hj hb)
    (chartLaurent_coef hj) z

end Chart

end Cech.WeightedVariables

end
