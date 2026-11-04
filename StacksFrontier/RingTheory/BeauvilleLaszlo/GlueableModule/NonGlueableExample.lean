module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingPair
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule.SmoothGerms

/-!
# Glueable modules: a non-glueable module over a glueing pair

Let `R` be the ring of germs at `0` of smooth functions on `ℝ` and `f = x` the coordinate
germ. Hadamard's lemma supplies division by the coordinate, `φ(x) = exp(-1/x²)` is the flat
function, and the `(x)`-adic completion of the germ ring is identified with `ℝ[[x]]`. The
module `R/φR` is then not glueable, so the glueability hypothesis is not vacuous even for a
glueing pair.

## Main results

* `exists_non_glueable_module_over_smooth_germ_ring` (Stacks 0BNY): over the ring of germs
  at `0` of smooth functions on `ℝ`, with `f = x`, the module `R/φR` for
  `φ(x) = exp(-1/x²)` is not glueable.

## References

* [Stacks Project, Tag 0BNY](https://stacks.math.columbia.edu/tag/0BNY)
-/

@[expose] public section

namespace BeauvilleLaszlo

section

noncomputable section

open scoped Manifold _root_.ContDiff
open Opposite Topology CategoryTheory Filter TopologicalSpace



universe u

open _root_.ContDiff

open scoped Interval

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]


variable [CompleteSpace F]

private def constantSection (c : ℝ) : smoothRingSheaf.presheaf.obj (op ⊤) :=
  ⟨fun _ => c, contMDiff_const⟩

private def constantSectionHom : ℝ →+* smoothRingSheaf.presheaf.obj (op ⊤) where
  toFun := constantSection
  map_zero' := by apply ContMDiffMap.ext; intro x; rfl
  map_one' := by apply ContMDiffMap.ext; intro x; rfl
  map_add' a b := by apply ContMDiffMap.ext; intro x; rfl
  map_mul' a b := by apply ContMDiffMap.ext; intro x; rfl

private noncomputable def constantGermHom : ℝ →+* smoothRingStalk :=
  (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0)).hom.comp constantSectionHom

private theorem eval_constantGerm (c : ℝ) :
    smoothSheafCommRing.eval (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ 0 (constantGermHom c) = c := by
  rw [constantGermHom, RingHom.comp_apply, smoothSheafCommRing.eval_germ]
  rfl

private theorem flat_smooth :
    ContDiff ℝ ∞ (fun x : ℝ => expNegInvGlue (x ^ 2)) := by
  exact expNegInvGlue.contDiff.comp (contDiff_id.pow 2)

private theorem flatDiv_smooth :
    ContDiff ℝ ∞ (fun x : ℝ =>
      x * ((Polynomial.X : Polynomial ℝ).eval ((x ^ 2)⁻¹) * expNegInvGlue (x ^ 2))) := by
  exact contDiff_id.mul
    ((expNegInvGlue.contDiff_polynomial_eval_inv_mul Polynomial.X).comp
      (contDiff_id.pow 2))

private noncomputable def flatSection :
    (smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.obj (op ⊤) :=
  ⟨fun x => expNegInvGlue (x.1 ^ 2), by
    exact flat_smooth.contMDiff.comp contMDiff_subtype_val⟩

private noncomputable def coordSection :
    (smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.obj (op ⊤) :=
  ⟨fun x => x.1, by exact contMDiff_subtype_val⟩

private theorem smooth_germ_decomposition (r : smoothRingStalk) :
    ∃ q : smoothRingStalk,
      r = constantGermHom
          (smoothSheafCommRing.eval (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) ℝ ℝ 0 r) +
        smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection * q := by
  obtain ⟨U, h0U, g, rfl⟩ := smoothRingSheaf.presheaf.exists_germ_eq r
  obtain ⟨W, h0W, hWU, q, hq⟩ := smooth_section_division_at_zero U h0U g
  refine ⟨smoothRingSheaf.presheaf.germ W 0 h0W q, ?_⟩
  let iWU : W ⟶ U := homOfLE hWU
  let iWtop : W ⟶ ⊤ := homOfLE le_top
  have hsec : smoothRingSheaf.presheaf.map iWU.op g =
      smoothRingSheaf.presheaf.map iWtop.op
          (constantSection (g ⟨0, h0U⟩)) +
        smoothRingSheaf.presheaf.map iWtop.op coordSection * q := by
    apply ContMDiffMap.ext
    intro x
    show g ⟨x.1, hWU x.2⟩ =
      g ⟨0, h0U⟩ + x.1 * q x
    exact hq x
  have hstalk := congrArg
    (fun s : smoothRingSheaf.presheaf.obj (op W) =>
      smoothRingSheaf.presheaf.germ W 0 h0W s) hsec
  rw [smoothSheafCommRing.eval_germ]
  show smoothRingSheaf.presheaf.germ U 0 h0U g =
    constantGermHom (g ⟨0, h0U⟩) +
      smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection *
        smoothRingSheaf.presheaf.germ W 0 h0W q
  rw [← smoothRingSheaf.presheaf.germ_res_apply iWU 0 h0W g]
  rw [map_add, map_mul,
    smoothRingSheaf.presheaf.germ_res_apply iWtop 0 h0W,
    smoothRingSheaf.presheaf.germ_res_apply iWtop 0 h0W] at hstalk
  exact hstalk

private theorem polynomial_approximation
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hdec : ∀ a : A, ∃ b : A, a = s (eps a) + f * b)
    (n : ℕ) (a : A) :
    ∃ p : Polynomial k, f ^ n ∣ a - Polynomial.eval₂ s f p := by
  induction n generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := hdec a
    obtain ⟨p, hp⟩ := ih b
    refine ⟨Polynomial.C (eps a) + Polynomial.X * p, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    nth_rewrite 1 [hb]
    convert mul_dvd_mul_left f hp using 1 <;> ring

private theorem eval_polynomial_constCoeff
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (p : Polynomial k) :
    eps (Polynomial.eval₂ s f p) = p.coeff 0 := by
  have hcomp : eps.comp (Polynomial.eval₂RingHom s f) = Polynomial.evalRingHom 0 := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa using hsec c
    · simp [hf]
  have h := congrArg (fun e : Polynomial k →+* k => e p) hcomp
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

private theorem polynomial_divisibility_reflects
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (hreg : IsRegular f) (n : ℕ) (p : Polynomial k) :
    f ^ n ∣ Polynomial.eval₂ s f p → Polynomial.X ^ n ∣ p := by
  induction n generalizing p with
  | zero => intro _; simp
  | succ n ih =>
    intro hdiv
    obtain ⟨a, ha⟩ := hdiv
    have hconst : p.coeff 0 = 0 := by
      have h := congrArg eps ha
      simp only [eval_polynomial_constCoeff s eps f hsec hf p] at h
      simpa [pow_succ, hf] using h
    have hp : p = Polynomial.X * p.divX := by
      simpa [hconst] using (Polynomial.X_mul_divX_add p).symm
    have hq : f ^ n ∣ Polynomial.eval₂ s f p.divX := by
      refine ⟨a, ?_⟩
      apply hreg.left
      calc
        f * Polynomial.eval₂ s f p.divX =
            Polynomial.eval₂ s f (Polynomial.X * p.divX) := by simp
        _ = Polynomial.eval₂ s f p := congrArg _ hp.symm
        _ = f ^ (n + 1) * a := ha
        _ = f * (f ^ n * a) := by rw [pow_succ]; ring
    obtain ⟨q, hq⟩ := ih p.divX hq
    refine ⟨q, ?_⟩
    rw [hp, pow_succ, hq]
    ring

private noncomputable def flatDivSection :
    (smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.obj (op ⊤) :=
  ⟨fun x => x.1 * ((Polynomial.X : Polynomial ℝ).eval ((x.1 ^ 2)⁻¹) *
      expNegInvGlue (x.1 ^ 2)),
    by exact flatDiv_smooth.contMDiff.comp contMDiff_subtype_val⟩

private theorem flatSection_apply (x : ℝ) :
    flatSection ⟨x, Set.mem_univ x⟩ =
      if x = 0 then 0 else Real.exp (-1 / x ^ 2) := by
  by_cases hx : x = 0
  · simp [flatSection, hx]
  · have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [flatSection, expNegInvGlue, hx, div_eq_mul_inv]

private theorem flatDivSection_apply (x : ℝ) :
    flatDivSection ⟨x, Set.mem_univ x⟩ =
      if x = 0 then 0 else Real.exp (-1 / x ^ 2) / x := by
  by_cases hx : x = 0
  · simp [flatDivSection, hx]
  · have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp only [flatDivSection, Polynomial.eval_X,
      expNegInvGlue, if_neg (not_le.mpr hpos), if_neg hx]
    rw [show x * ((x ^ 2)⁻¹ * Real.exp (-(x ^ 2)⁻¹)) =
      Real.exp (-(x ^ 2)⁻¹) / x by field_simp]
    simp [div_eq_mul_inv]

private theorem flatPower_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      x ^ n * ((Polynomial.X ^ n : Polynomial ℝ).eval ((x ^ 2)⁻¹) *
        expNegInvGlue (x ^ 2))) := by
  exact (contDiff_id.pow n).mul
    ((expNegInvGlue.contDiff_polynomial_eval_inv_mul (Polynomial.X ^ n)).comp
      (contDiff_id.pow 2))

private def flatPowerSection (n : ℕ) :
    (smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.obj (op ⊤) :=
  ⟨fun x => x.1 ^ n * ((Polynomial.X ^ n : Polynomial ℝ).eval ((x.1 ^ 2)⁻¹) *
      expNegInvGlue (x.1 ^ 2)),
    by exact (flatPower_smooth n).contMDiff.comp contMDiff_subtype_val⟩

private theorem flatPowerSection_apply (n : ℕ) (x : ℝ) :
    flatPowerSection n ⟨x, Set.mem_univ x⟩ =
      if x = 0 then 0 else Real.exp (-1 / x ^ 2) / x ^ n := by
  by_cases hx : x = 0
  · simp [flatPowerSection, hx]
  · have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp only [flatPowerSection, Polynomial.eval_pow, Polynomial.eval_X,
      expNegInvGlue, if_neg (not_le.mpr hpos), if_neg hx]
    field_simp
    ring_nf
    simp [hx]

private theorem coord_pow_mul_flatPower (n : ℕ) :
    coordSection ^ n * flatPowerSection n = flatSection := by
  apply ContMDiffMap.ext
  intro x
  show x.1 ^ n * flatPowerSection n x = flatSection x
  have hp := flatPowerSection_apply n x.1
  have hf := flatSection_apply x.1
  change flatPowerSection n x = _ at hp
  change flatSection x = _ at hf
  rw [hp, hf]
  by_cases hx : x.1 = 0
  · simp [hx]
  · simp [hx]
    field_simp

private theorem coord_pow_mul_flatPower_succ (n : ℕ) :
    coordSection ^ n * flatPowerSection (n + 1) = flatDivSection := by
  apply ContMDiffMap.ext
  intro x
  show x.1 ^ n * flatPowerSection (n + 1) x = flatDivSection x
  have hp := flatPowerSection_apply (n + 1) x.1
  have hf := flatDivSection_apply x.1
  change flatPowerSection (n + 1) x = _ at hp
  change flatDivSection x = _ at hf
  rw [hp, hf]
  by_cases hx : x.1 = 0
  · simp [hx]
  · simp [hx, pow_succ, div_eq_mul_inv, mul_assoc, mul_comm]
    field_simp

private theorem flat_germ_pow_dvd (n : ℕ) :
    (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) ^ n ∣
      smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatSection := by
  refine ⟨smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0)
    (flatPowerSection n), ?_⟩
  rw [← map_pow, ← map_mul, coord_pow_mul_flatPower]

private theorem flatDiv_germ_pow_dvd (n : ℕ) :
    (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) ^ n ∣
      smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatDivSection := by
  refine ⟨smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0)
    (flatPowerSection (n + 1)), ?_⟩
  rw [← map_pow, ← map_mul, coord_pow_mul_flatPower_succ]

private theorem flat_germ_completion_zero :
    algebraMap smoothRingStalk
      (AdicCompletion (Ideal.span
        {smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection})
        smoothRingStalk)
      (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatSection) = 0 := by
  exact completion_zero_of_forall_pow_dvd _ _ flat_germ_pow_dvd

private theorem flatDiv_germ_completion_zero :
    algebraMap smoothRingStalk
      (AdicCompletion (Ideal.span
        {smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection})
        smoothRingStalk)
      (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatDivSection) = 0 := by
  exact completion_zero_of_forall_pow_dvd _ _ flatDiv_germ_pow_dvd


private theorem coord_germ_regular :
    IsRegular (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) := by
  apply regular_germ_of_punctured_nonzero
  intro x hx
  show x ≠ 0
  exact hx

private theorem flat_germ_regular :
    IsRegular (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatSection) := by
  apply regular_germ_of_punctured_nonzero
  intro x hx
  rw [flatSection_apply, if_neg hx]
  exact (Real.exp_pos _).ne'

private theorem coord_mul_flatDiv :
    coordSection * flatDivSection = flatSection := by
  apply ContMDiffMap.ext
  intro x
  show x.1 * (x.1 * ((Polynomial.X : Polynomial ℝ).eval ((x.1 ^ 2)⁻¹) *
    expNegInvGlue (x.1 ^ 2))) = expNegInvGlue (x.1 ^ 2)
  by_cases hx : x.1 = 0
  · simp [hx]
  · simp only [Polynomial.eval_X]
    have hx2 : x.1 ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp

private theorem eval_coord_germ :
    smoothSheafCommRing.eval (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ 0
      (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) = 0 := by
  rw [smoothSheafCommRing.eval_germ]
  rfl

private theorem coord_germ_not_isUnit :
    ¬ IsUnit (((smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.germ ⊤ 0
        (Set.mem_univ 0)) coordSection) := by
  rw [smoothSheafCommRing.isUnit_stalk_iff]
  simpa only [not_not, RingHom.mem_ker] using eval_coord_germ

private theorem quotient_mul_nonzero {R : Type*} [CommRing R] {f ψ : R}
    (hφ : IsRegular (f * ψ)) (hf : ¬ IsUnit f) :
    (Ideal.Quotient.mk (Ideal.span {f * ψ}) ψ) ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_dvd] at h
  obtain ⟨a, ha⟩ := h
  have hψ : IsRegular ψ := hφ.of_mul_right
  have h1 : (1 : R) = f * a := hψ.left (by
    calc
      ψ * 1 = ψ := mul_one ψ
      _ = (f * ψ) * a := ha
      _ = ψ * (f * a) := by ring)
  exact hf (isUnit_of_dvd_one ⟨a, h1⟩)

private theorem coord_germ_mul_flatDiv_germ :
    let S := smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ
    (S.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) *
      (S.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatDivSection) =
      (S.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatSection) := by
  dsimp
  rw [← map_mul]
  rw [coord_mul_flatDiv]

private theorem flatDiv_quotient_nonzero
    (hφ : IsRegular
      ((smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ℝ ℝ).presheaf.germ ⊤ 0
          (Set.mem_univ 0) flatSection)) :
    let S := smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ
    let R := S.presheaf.stalk (0 : ℝ)
    let φ : R := S.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatSection
    let ψ : R := S.presheaf.germ ⊤ 0 (Set.mem_univ 0) flatDivSection
    Ideal.Quotient.mk (Ideal.span {φ}) ψ ≠ 0 := by
  dsimp
  rw [← coord_germ_mul_flatDiv_germ] at hφ ⊢
  exact quotient_mul_nonzero hφ coord_germ_not_isUnit

private theorem quotient_mul_torsion {R : Type*} [CommRing R] (f ψ : R) :
    f • (Ideal.Quotient.mk (Ideal.span {f * ψ}) ψ) = 0 := by
  show (Ideal.Quotient.mk (Ideal.span {f * ψ})) (f * ψ) = 0
  simp

private theorem quotient_tmul_zero {R C : Type*} [CommRing R] [CommRing C]
    [Algebra R C] {φ ψ : R} (hψ : algebraMap R C ψ = 0) :
    TensorProduct.mk R (R ⧸ Ideal.span {φ}) C
      (Ideal.Quotient.mk (Ideal.span {φ}) ψ) 1 = 0 := by
  have hm : (Ideal.Quotient.mk (Ideal.span {φ})) ψ =
      ψ • (1 : R ⧸ Ideal.span {φ}) := by simp [Algebra.smul_def]
  rw [hm]
  show (ψ • (1 : R ⧸ Ideal.span {φ})) ⊗ₜ[R] (1 : C) = 0
  rw [TensorProduct.smul_tmul]
  simp [Algebra.smul_def, hψ]

private noncomputable def quotientTensorEquivOfMapEqZero
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    {φ : R} (hφ : algebraMap R C φ = 0) :
    TensorProduct R (R ⧸ Ideal.span {φ}) C ≃ₗ[R] C := by
  have hspan : Ideal.span {φ} ≤ RingHom.ker (algebraMap R C) := by
    apply Ideal.span_le.mpr
    simpa [Set.singleton_subset_iff, RingHom.mem_ker] using hφ
  have hzero : (Ideal.span {φ}) • (⊤ : Submodule R C) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro r hr c _
    have hr0 : algebraMap R C r = 0 := hspan hr
    simp [Algebra.smul_def, hr0]
  exact (TensorProduct.quotTensorEquivQuotSMul C (Ideal.span {φ})).trans
    ((Ideal.span {φ} • (⊤ : Submodule R C)).quotEquivOfEqBot hzero)

private theorem quotientTensorEquivOfMapEqZero_apply
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    {φ : R} (hφ : algebraMap R C φ = 0) (r : R) (c : C) :
    quotientTensorEquivOfMapEqZero hφ
      (TensorProduct.mk R (R ⧸ Ideal.span {φ}) C
        (Ideal.Quotient.mk (Ideal.span {φ}) r) c) = algebraMap R C r * c := by
  simp [quotientTensorEquivOfMapEqZero,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    Submodule.quotEquivOfEqBot_apply_mk, Algebra.smul_def]

private theorem torsion_tensor_map_not_injective
    {R C M : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module R M] {f : R} {m : M}
    (hm : m ≠ 0) (ht : ∃ n : ℕ, f ^ n • m = 0)
    (hz : TensorProduct.mk R M C m 1 = 0) :
    ¬ Function.Injective
      (fun x : {x : M // ∃ n : ℕ, f ^ n • x = 0} ↦
        TensorProduct.mk R M C x.1 1) := by
  intro hinj
  let x : {x : M // ∃ n : ℕ, f ^ n • x = 0} := ⟨m, ht⟩
  let z : {x : M // ∃ n : ℕ, f ^ n • x = 0} := ⟨0, ⟨0, by simp⟩⟩
  have hxz : x = z := hinj (by simp [x, z, hz])
  exact hm (congrArg Subtype.val hxz)

private noncomputable def adicCompletionEquivOfQuotientEquivs
    {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B)
    (q : ∀ n : ℕ,
      (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃+* (B ⧸ (J ^ n • ⊤ : Ideal B)))
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n)
      (x : A ⧸ (I ^ n • ⊤ : Ideal A)),
      AdicCompletion.transitionMap J B hmn (q n x) =
        q m (AdicCompletion.transitionMap I A hmn x)) :
    AdicCompletion I A ≃+* AdicCompletion J B where
  toFun x := ⟨fun n => q n (x.val n), fun hmn => by
    rw [hq hmn, x.property hmn]⟩
  invFun y := ⟨fun n => (q n).symm (y.val n), fun {m n} hmn => by
    apply (q m).injective
    rw [← hq hmn, (q n).apply_symm_apply, (q m).apply_symm_apply,
      y.property hmn]⟩
  left_inv x := by ext n; exact (q n).symm_apply_apply (x.val n)
  right_inv y := by ext n; exact (q n).apply_symm_apply (y.val n)
  map_mul' x y := by ext n; exact map_mul (q n) (x.val n) (y.val n)
  map_add' x y := by ext n; exact map_add (q n) (x.val n) (y.val n)

private noncomputable def polynomialEvalQuotientEquiv
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (hreg : IsRegular f)
    (hdec : ∀ a : A, ∃ b : A, a = s (eps a) + f * b)
    (n : ℕ) :
    (Polynomial k ⧸ (Ideal.span {(Polynomial.X : Polynomial k)} ^ n • ⊤ :
      Ideal (Polynomial k))) ≃+*
      (A ⧸ (Ideal.span {f} ^ n • ⊤ : Ideal A)) := by
  let h : Polynomial k →+* A := Polynomial.eval₂RingHom s f
  let I : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
  let J : Ideal A := Ideal.span {f}
  have hI : (I ^ n • ⊤ : Ideal (Polynomial k)) = I ^ n := by ext x; simp
  have hJ : (J ^ n • ⊤ : Ideal A) = J ^ n := by ext x; simp
  have hmem (p : Polynomial k) : p ∈ (I ^ n • ⊤ : Ideal (Polynomial k)) ↔
      h p ∈ (J ^ n • ⊤ : Ideal A) := by
    rw [hI, hJ]
    simp only [I, J, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · intro hp
      simpa [h] using map_dvd h hp
    · intro hp
      exact polynomial_divisibility_reflects s eps f hsec hf hreg n p hp
  let q : (Polynomial k ⧸ (I ^ n • ⊤ : Ideal (Polynomial k))) →+*
      (A ⧸ (J ^ n • ⊤ : Ideal A)) :=
    Ideal.quotientMap (J ^ n • ⊤ : Ideal A) h (fun p hp => (hmem p).mp hp)
  apply RingEquiv.ofBijective q
  constructor
  · exact Ideal.quotientMap_injective' (fun p hp => (hmem p).mpr hp)
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hp⟩ := polynomial_approximation s eps f hdec n a
    refine ⟨Ideal.Quotient.mk (I ^ n • ⊤ : Ideal (Polynomial k)) p, ?_⟩
    change Ideal.Quotient.mk (J ^ n • ⊤ : Ideal A) (h p) =
      Ideal.Quotient.mk (J ^ n • ⊤ : Ideal A) a
    rw [Ideal.Quotient.eq]
    rw [hJ]
    simp only [J, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := hp
    refine ⟨-c, ?_⟩
    change Polynomial.eval₂ s f p - a = f ^ n * -c
    rw [mul_neg, ← hc]
    ring

private theorem polynomialEvalQuotientEquiv_mk
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (hreg : IsRegular f)
    (hdec : ∀ a : A, ∃ b : A, a = s (eps a) + f * b)
    (n : ℕ) (p : Polynomial k) :
    polynomialEvalQuotientEquiv s eps f hsec hf hreg hdec n
      (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (Polynomial.eval₂ s f p) := by
  rfl

private noncomputable def polynomialEvalAdicCompletionEquiv
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (hreg : IsRegular f)
    (hdec : ∀ a : A, ∃ b : A, a = s (eps a) + f * b) :
    AdicCompletion (Ideal.span {(Polynomial.X : Polynomial k)}) (Polynomial k) ≃+*
      AdicCompletion (Ideal.span {f}) A := by
  let q : ∀ n : ℕ,
      (Polynomial k ⧸ (Ideal.span {(Polynomial.X : Polynomial k)} ^ n • ⊤ :
        Ideal (Polynomial k))) ≃+*
      (A ⧸ (Ideal.span {f} ^ n • ⊤ : Ideal A)) :=
        fun n => polynomialEvalQuotientEquiv s eps f hsec hf hreg hdec n
  apply adicCompletionEquivOfQuotientEquivs _ _ q
  intro m n hmn x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change AdicCompletion.transitionMap _ _ hmn
      (polynomialEvalQuotientEquiv s eps f hsec hf hreg hdec n
        (Ideal.Quotient.mk _ p)) =
      polynomialEvalQuotientEquiv s eps f hsec hf hreg hdec m
        (AdicCompletion.transitionMap _ _ hmn (Ideal.Quotient.mk _ p))
  rw [polynomialEvalQuotientEquiv_mk,
    AdicCompletion.transitionMap_ideal_mk,
    AdicCompletion.transitionMap_ideal_mk,
    polynomialEvalQuotientEquiv_mk]

private theorem polynomialEvalAdicCompletionEquiv_of
    {k A : Type*} [CommRing k] [CommRing A]
    (s : k →+* A) (eps : A →+* k) (f : A)
    (hsec : ∀ c : k, eps (s c) = c) (hf : eps f = 0)
    (hreg : IsRegular f)
    (hdec : ∀ a : A, ∃ b : A, a = s (eps a) + f * b)
    (p : Polynomial k) :
    polynomialEvalAdicCompletionEquiv s eps f hsec hf hreg hdec
      (algebraMap (Polynomial k)
        (AdicCompletion (Ideal.span {(Polynomial.X : Polynomial k)}) (Polynomial k)) p) =
      algebraMap A (AdicCompletion (Ideal.span {f}) A)
        (Polynomial.eval₂ s f p) := by
  apply AdicCompletion.ext
  intro n
  show polynomialEvalQuotientEquiv s eps f hsec hf hreg hdec n
      ((AdicCompletion.of (Ideal.span {(Polynomial.X : Polynomial k)})
        (Polynomial k) p).val n) =
      ((AdicCompletion.of (Ideal.span {f}) A
        (Polynomial.eval₂ s f p)).val n)
  rw [AdicCompletion.of_apply, AdicCompletion.of_apply]
  exact polynomialEvalQuotientEquiv_mk s eps f hsec hf hreg hdec n p

/-- Powers of the image ideal are the images of the powers, written with `• ⊤`. -/
private theorem pow_smul_top_eq_map {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : J = I.map e.toRingHom) (n : ℕ) :
    (J ^ n • ⊤ : Ideal B) = (I ^ n • ⊤ : Ideal A).map (e : A →+* B) := by
  have hI : (I ^ n • ⊤ : Ideal A) = I ^ n := by ext x; simp
  have hJ : (J ^ n • ⊤ : Ideal B) = J ^ n := by ext x; simp
  rw [hI, hJ, hIJ]
  exact (Ideal.map_pow e.toRingHom I n).symm

private noncomputable def adicCompletionCongrRingEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hIJ : J = I.map e.toRingHom) :
    AdicCompletion I A ≃+* AdicCompletion J B := by
  let q : ∀ n : ℕ,
      (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃+* (B ⧸ (J ^ n • ⊤ : Ideal B)) :=
    fun n => Ideal.quotientEquiv (I ^ n • ⊤ : Ideal A) (J ^ n • ⊤ : Ideal B) e
      (pow_smul_top_eq_map e I J hIJ n)
  apply adicCompletionEquivOfQuotientEquivs I J q
  intro m n hmn x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change AdicCompletion.transitionMap J B hmn
      (q n (Ideal.Quotient.mk _ a)) =
      q m (AdicCompletion.transitionMap I A hmn (Ideal.Quotient.mk _ a))
  dsimp only [q]
  rw [Ideal.quotientEquiv_mk,
    AdicCompletion.transitionMap_ideal_mk,
    AdicCompletion.transitionMap_ideal_mk,
    Ideal.quotientEquiv_mk]

private theorem adicCompletionCongrRingEquiv_of
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hIJ : J = I.map e.toRingHom) (a : A) :
    adicCompletionCongrRingEquiv e I J hIJ
      (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion J B) (e a) := by
  apply AdicCompletion.ext
  intro n
  show (Ideal.quotientEquiv (I ^ n • ⊤ : Ideal A)
      (J ^ n • ⊤ : Ideal B) e (pow_smul_top_eq_map e I J hIJ n))
    ((AdicCompletion.of I A a).val n) =
      (AdicCompletion.of J B (e a)).val n
  rw [AdicCompletion.of_apply, AdicCompletion.of_apply]
  exact Ideal.quotientEquiv_mk _ _ _ _ _

private theorem uniqueAlgEquiv_map_idealOfVars :
    (MvPolynomial.idealOfVars Unit ℝ).map
      (MvPolynomial.uniqueAlgEquiv ℝ Unit).toRingEquiv.toRingHom =
        Ideal.span {(Polynomial.X : Polynomial ℝ)} := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    simp [MvPolynomial.uniqueAlgEquiv_apply]
  · intro hp
    refine ⟨MvPolynomial.X (), ⟨(), rfl⟩, ?_⟩
    simpa [MvPolynomial.uniqueAlgEquiv_apply] using hp.symm

private noncomputable def polyCompletionEquivPowerSeries :
    AdicCompletion (Ideal.span {(Polynomial.X : Polynomial ℝ)}) (Polynomial ℝ) ≃+*
      PowerSeries ℝ := by
  let e : MvPolynomial Unit ℝ ≃+* Polynomial ℝ :=
    (MvPolynomial.uniqueAlgEquiv ℝ Unit).toRingEquiv
  let g : AdicCompletion (MvPolynomial.idealOfVars Unit ℝ) (MvPolynomial Unit ℝ) ≃+*
      AdicCompletion (Ideal.span {(Polynomial.X : Polynomial ℝ)}) (Polynomial ℝ) := by
    exact adicCompletionCongrRingEquiv e (MvPolynomial.idealOfVars Unit ℝ)
      (Ideal.span {Polynomial.X}) uniqueAlgEquiv_map_idealOfVars.symm
  exact ((MvPowerSeries.toAdicCompletionAlgEquiv Unit ℝ).toRingEquiv.trans g).symm

private theorem polyCompletionEquivPowerSeries_coord :
    polyCompletionEquivPowerSeries
      (algebraMap (Polynomial ℝ)
        (AdicCompletion (Ideal.span {(Polynomial.X : Polynomial ℝ)}) (Polynomial ℝ))
        Polynomial.X) = PowerSeries.X := by
  apply polyCompletionEquivPowerSeries.symm.injective
  rw [RingEquiv.symm_apply_apply]
  show (algebraMap (Polynomial ℝ)
      (AdicCompletion (Ideal.span {(Polynomial.X : Polynomial ℝ)}) (Polynomial ℝ))
      Polynomial.X) =
    (adicCompletionCongrRingEquiv
      (MvPolynomial.uniqueAlgEquiv ℝ Unit).toRingEquiv
      (MvPolynomial.idealOfVars Unit ℝ)
      (Ideal.span {Polynomial.X}) uniqueAlgEquiv_map_idealOfVars.symm)
      ((MvPowerSeries.toAdicCompletionAlgEquiv Unit ℝ).toRingEquiv
        (PowerSeries.X : PowerSeries ℝ))
  show _ = adicCompletionCongrRingEquiv _ _
    (Ideal.span {Polynomial.X}) uniqueAlgEquiv_map_idealOfVars.symm
    (MvPowerSeries.toAdicCompletion Unit ℝ (MvPowerSeries.X () : MvPowerSeries Unit ℝ))
  rw [← MvPolynomial.coe_X, MvPowerSeries.toAdicCompletion_coe]
  show _ = adicCompletionCongrRingEquiv _ _ _ _
    (algebraMap (MvPolynomial Unit ℝ)
      (AdicCompletion (MvPolynomial.idealOfVars Unit ℝ) (MvPolynomial Unit ℝ))
      (MvPolynomial.X ()))
  rw [adicCompletionCongrRingEquiv_of]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

private noncomputable def smoothGermCompletionEquiv :
    AdicCompletion
      (Ideal.span {smoothRingSheaf.presheaf.germ ⊤ 0
        (Set.mem_univ 0) coordSection}) smoothRingStalk ≃+*
      PowerSeries ℝ := by
  let eps : smoothRingStalk →+* ℝ :=
    smoothSheafCommRing.eval (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ 0
  let f : smoothRingStalk := smoothRingSheaf.presheaf.germ ⊤ 0
    (Set.mem_univ 0) coordSection
  have hsec (c : ℝ) : eps (constantGermHom c) = c := eval_constantGerm c
  have hf : eps f = 0 := eval_coord_germ
  exact (polynomialEvalAdicCompletionEquiv constantGermHom eps f
    hsec hf coord_germ_regular smooth_germ_decomposition).symm.trans
      polyCompletionEquivPowerSeries

private theorem smoothGermCompletionEquiv_coord :
    smoothGermCompletionEquiv
      (algebraMap smoothRingStalk
        (AdicCompletion
          (Ideal.span {smoothRingSheaf.presheaf.germ ⊤ 0
            (Set.mem_univ 0) coordSection}) smoothRingStalk)
        (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection)) =
      PowerSeries.X := by
  let eps : smoothRingStalk →+* ℝ :=
    smoothSheafCommRing.eval (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ 0
  let f : smoothRingStalk := smoothRingSheaf.presheaf.germ ⊤ 0
    (Set.mem_univ 0) coordSection
  have hsec (c : ℝ) : eps (constantGermHom c) = c := eval_constantGerm c
  have hf : eps f = 0 := eval_coord_germ
  let e := polynomialEvalAdicCompletionEquiv constantGermHom eps f hsec hf
    coord_germ_regular smooth_germ_decomposition
  have hX := polynomialEvalAdicCompletionEquiv_of constantGermHom eps f hsec hf
    coord_germ_regular smooth_germ_decomposition (Polynomial.X : Polynomial ℝ)
  simp only [Polynomial.eval₂_X] at hX
  show polyCompletionEquivPowerSeries
      (e.symm (algebraMap smoothRingStalk
        (AdicCompletion (Ideal.span {f}) smoothRingStalk) f)) = PowerSeries.X
  rw [← hX, e.symm_apply_apply]
  exact polyCompletionEquivPowerSeries_coord

/-- The ring `R` of germs at zero of smooth functions on `ℝ`, with coordinate germ `f`, has
completion `ℝ[[X]]`. The flat germs `φ(x) = exp (-1 / x²)` and `ψ(x) = φ(x) / x` vanish
in the completion, while the class of `ψ` in `M = R / φR` is nonzero `f`-torsion. It therefore
lies in the kernel of the completion base-change map, so `M` is not glueable. -/
@[stacks 0BNY]
public theorem exists_non_glueable_module_over_smooth_germ_ring :
    let S := smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ℝ ℝ
    let R := S.presheaf.stalk (0 : ℝ)
    ∃ (f₀ φ₀ ψ₀ : S.presheaf.obj (op ⊤)),
      (∀ x : ℝ, f₀ ⟨x, Set.mem_univ x⟩ = x) ∧
      (∀ x : ℝ, φ₀ ⟨x, Set.mem_univ x⟩ =
        if x = 0 then 0 else Real.exp (-1 / x ^ 2)) ∧
      (∀ x : ℝ, ψ₀ ⟨x, Set.mem_univ x⟩ =
        if x = 0 then 0 else Real.exp (-1 / x ^ 2) / x) ∧
      let f : R := S.presheaf.germ ⊤ 0 (Set.mem_univ 0) f₀
      let φ : R := S.presheaf.germ ⊤ 0 (Set.mem_univ 0) φ₀
      let ψ : R := S.presheaf.germ ⊤ 0 (Set.mem_univ 0) ψ₀
      IsRegular f ∧ IsRegular φ ∧ f * ψ = φ ∧
      ∃ e : AdicCompletion (Ideal.span {f}) R ≃+* PowerSeries ℝ,
        e (algebraMap R (AdicCompletion (Ideal.span {f}) R) f) = PowerSeries.X ∧
        algebraMap R (AdicCompletion (Ideal.span {f}) R) φ = 0 ∧
        algebraMap R (AdicCompletion (Ideal.span {f}) R) ψ = 0 ∧
        (let M := R ⧸ Ideal.span {φ}
         let m : M := Ideal.Quotient.mk (Ideal.span {φ}) ψ
         let C := AdicCompletion (Ideal.span {f}) R
         m ≠ 0 ∧ f • m = 0 ∧
          TensorProduct.mk R M C m 1 = 0 ∧
          (∃ q : TensorProduct R M C ≃ₗ[R] C,
            ∀ (r : R) (c : C),
              q (TensorProduct.mk R M C (Ideal.Quotient.mk (Ideal.span {φ}) r) c) =
                algebraMap R C r * c) ∧
          ¬ Function.Injective
            (fun x : {x : M // ∃ n : ℕ, f ^ n • x = 0} ↦
              TensorProduct.mk R M C x.1 1)) := by
  refine ⟨coordSection, flatSection, flatDivSection, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact flatSection_apply
  · exact flatDivSection_apply
  · dsimp
    refine ⟨coord_germ_regular, flat_germ_regular,
      coord_germ_mul_flatDiv_germ, smoothGermCompletionEquiv,
      smoothGermCompletionEquiv_coord, flat_germ_completion_zero,
      flatDiv_germ_completion_zero, ?_⟩
    have hm := flatDiv_quotient_nonzero flat_germ_regular
    have hfm :
        (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) coordSection) •
          (Ideal.Quotient.mk
            (Ideal.span {smoothRingSheaf.presheaf.germ ⊤ 0
              (Set.mem_univ 0) flatSection})
            (smoothRingSheaf.presheaf.germ ⊤ 0
              (Set.mem_univ 0) flatDivSection)) = 0 := by
      rw [← coord_germ_mul_flatDiv_germ]
      exact quotient_mul_torsion _ _
    refine ⟨hm, hfm, quotient_tmul_zero flatDiv_germ_completion_zero,
      ⟨quotientTensorEquivOfMapEqZero flat_germ_completion_zero,
        quotientTensorEquivOfMapEqZero_apply flat_germ_completion_zero⟩, ?_⟩
    exact torsion_tensor_map_not_injective hm
      ⟨1, by simpa using hfm⟩
      (quotient_tmul_zero flatDiv_germ_completion_zero)



end

end

end BeauvilleLaszlo

end
