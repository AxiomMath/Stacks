module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Translation operators and continuous-kernel operators on `L²` of a compact group

Let `A` be a compact commutative topological group with a finite left-invariant measure `μ`.
This file sets up the bounded operators on `L²(A, μ; ℂ)` used to show that the characters of `A`
separate points.

## Main definitions

* `Stacks.Pontryagin.translate μ g`: the translation `f ↦ f (g * ·)`, a linear isometry of
  `L²(A, μ)`, viewed as a bounded operator.
* `Stacks.Pontryagin.kernelOp μ u`: for a continuous map `u : A → L²(A, μ)`, the operator
  `f ↦ (x ↦ ⟪u x, f⟫)`, whose values are continuous functions.
* `Stacks.Pontryagin.kernel μ ψ`: for `ψ : C(A, ℂ)`, the continuous map `x ↦ ψ (· / x)` into
  `L²(A, μ)`; `kernelOp μ (kernel μ ψ)` is the convolution operator with kernel `conj ψ`.

## Main results

* `Stacks.Pontryagin.translate_mul`, `Stacks.Pontryagin.star_translate`: translations form a
  unitary representation.
* `Stacks.Pontryagin.continuous_translate_mul_kernelOp`: `g ↦ translate μ g * kernelOp μ u` is
  continuous for the operator norm.
* `Stacks.Pontryagin.translate_mul_kernelOp_kernel`: convolution operators commute with
  translations.
* `Stacks.Pontryagin.translate_mul_kernelOp_kernel_ne`: a suitable convolution operator is not
  fixed by the translation by `a ≠ 1`.

## References

* [Stacks, Tag 03VI]
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology ComplexConjugate
open scoped InnerProductSpace

namespace Stacks.Pontryagin

variable {A : Type*} [TopologicalSpace A]

section Shift

variable [CommGroup A] [IsTopologicalGroup A]

/-- Left translation of the argument is continuous in the translating element. -/
theorem continuous_comp_mulLeft {X : Type*} [TopologicalSpace X] (u : C(A, X)) :
    Continuous fun g : A => u.comp (ContinuousMap.mulLeft g) :=
  (u.comp ⟨fun p : A × A => p.1 * p.2, continuous_mul⟩).curry.continuous

/-- The continuous map `x ↦ ψ (· / x)` from `A` to `C(A, ℂ)`. -/
def shift (ψ : C(A, ℂ)) : C(A, C(A, ℂ)) :=
  (ψ.comp ⟨fun p : A × A => p.2 / p.1, by fun_prop⟩).curry

/-- Evaluation of `shift ψ`. -/
@[simp]
theorem shift_apply (ψ : C(A, ℂ)) (x y : A) : shift ψ x y = ψ (y / x) :=
  rfl

end Shift

variable [MeasurableSpace A] (μ : Measure A)

section KernelOp

/-- The continuous function `x ↦ ⟪u x, f⟫`. -/
def innerCM (u : C(A, Lp ℂ 2 μ)) (f : Lp ℂ 2 μ) : C(A, ℂ) :=
  ⟨fun x => ⟪u x, f⟫_ℂ, u.continuous.inner continuous_const⟩

/-- Evaluation of `innerCM μ u f`. -/
@[simp]
theorem innerCM_apply (u : C(A, Lp ℂ 2 μ)) (f : Lp ℂ 2 μ) (x : A) :
    innerCM μ u f x = ⟪u x, f⟫_ℂ :=
  rfl

variable [CompactSpace A]

/-- The sup norm of `x ↦ ⟪u x, f⟫` is at most `‖u‖ * ‖f‖`. -/
theorem norm_innerCM_le (u : C(A, Lp ℂ 2 μ)) (f : Lp ℂ 2 μ) : ‖innerCM μ u f‖ ≤ ‖u‖ * ‖f‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (u.norm_coe_le_norm x)
      (norm_nonneg _))

/-- `innerCM μ u` as a bounded linear map `L²(A, μ) → C(A, ℂ)`. -/
def innerCLM (u : C(A, Lp ℂ 2 μ)) : Lp ℂ 2 μ →L[ℂ] C(A, ℂ) :=
  LinearMap.mkContinuous
    { toFun := innerCM μ u
      map_add' := fun f f' => by ext x; simp [inner_add_right]
      map_smul' := fun c f => by ext x; simp [inner_smul_right] }
    ‖u‖ (norm_innerCM_le μ u)

variable [BorelSpace A] [IsFiniteMeasure μ]

/-- The operator `f ↦ (x ↦ ⟪u x, f⟫)` on `L²(A, μ)` attached to a continuous map
`u : A → L²(A, μ)`. -/
def kernelOp (u : C(A, Lp ℂ 2 μ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp (innerCLM μ u)

/-- `kernelOp μ u f` is the class of the continuous function `x ↦ ⟪u x, f⟫`. -/
theorem kernelOp_apply (u : C(A, Lp ℂ 2 μ)) (f : Lp ℂ 2 μ) :
    kernelOp μ u f = ContinuousMap.toLp 2 μ ℂ (innerCM μ u f) :=
  rfl

/-- `kernelOp μ` is additive. -/
theorem kernelOp_sub (u v : C(A, Lp ℂ 2 μ)) :
    kernelOp μ u - kernelOp μ v = kernelOp μ (u - v) := by
  ext1 f
  rw [sub_apply, kernelOp_apply, kernelOp_apply, kernelOp_apply, ← map_sub]
  congr 1
  ext x
  simp [inner_sub_left]

/-- Operator norm bound for `kernelOp μ u`. -/
theorem norm_kernelOp_le (u : C(A, Lp ℂ 2 μ)) :
    ‖kernelOp μ u‖ ≤ ‖(ContinuousMap.toLp 2 μ ℂ : C(A, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ * ‖u‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (LinearMap.mkContinuous_norm_le _ (norm_nonneg u) _)
      (norm_nonneg _))

/-- `kernelOp μ` is Lipschitz, hence continuous, for the operator norm. -/
theorem continuous_kernelOp : Continuous (kernelOp μ (A := A)) := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ‖(ContinuousMap.toLp 2 μ ℂ : C(A, ℂ) →L[ℂ] Lp ℂ 2 μ)‖₊) fun u v => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, kernelOp_sub, coe_nnnorm]
  exact norm_kernelOp_le μ _

end KernelOp

section Translate

variable [CommGroup A] [IsTopologicalGroup A] [BorelSpace A] [μ.IsMulLeftInvariant]

/-- The translation `f ↦ f (g * ·)` on `L²(A, μ)`, as a bounded operator. -/
def translate (g : A) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (g * ·) (measurePreserving_mul_left μ g)).toContinuousLinearMap

/-- `translate μ g f` is almost everywhere equal to `f (g * ·)`. -/
theorem translate_ae_eq (g : A) (f : Lp ℂ 2 μ) : translate μ g f =ᵐ[μ] fun x => f (g * x) :=
  Lp.coeFn_compMeasurePreserving f _

/-- Translations preserve the inner product of `L²(A, μ)`. -/
theorem inner_translate_translate (g : A) (f f' : Lp ℂ 2 μ) :
    ⟪translate μ g f, translate μ g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (g * ·) (measurePreserving_mul_left μ g)).inner_map_map f f'

/-- Translations have operator norm at most one. -/
theorem norm_translate_le (g : A) : ‖translate μ g‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]
    exact (Lp.norm_compMeasurePreserving f _).le

/-- The translations form a representation of `A`. -/
theorem translate_mul (g h : A) : translate μ g * translate μ h = translate μ (g * h) := by
  ext1 f
  refine Lp.ext ?_
  have h1 := translate_ae_eq μ g (translate μ h f)
  have h2 := (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq_comp
    (translate_ae_eq μ h f)
  have h3 := translate_ae_eq μ (g * h) f
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [mul_apply_eq_comp, hx1, hx3]
  simp only [Function.comp] at hx2
  rw [hx2, mul_left_comm, ← mul_assoc]

/-- The translation by `1` is the identity. -/
theorem translate_one : translate μ (1 : A) = 1 := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [translate_ae_eq μ 1 f] with x hx
  rw [hx, one_mul, one_apply_eq_self]

/-- The adjoint of the translation by `g` is the translation by `g⁻¹`. -/
theorem star_translate (g : A) : star (translate μ g) = translate μ g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro f f'
  rw [← inner_translate_translate μ g (translate μ g⁻¹ f) f', ← mul_apply_eq_comp,
    translate_mul, mul_inv_cancel, translate_one, one_apply_eq_self]

variable [CompactSpace A] [IsFiniteMeasure μ]

/-- Translating a continuous function in `L²` translates its argument. -/
theorem translate_toLp (g : A) (F : C(A, ℂ)) :
    translate μ g (ContinuousMap.toLp 2 μ ℂ F) =
      ContinuousMap.toLp 2 μ ℂ (F.comp (ContinuousMap.mulLeft g)) := by
  refine Lp.ext ?_
  have h1 := translate_ae_eq μ g (ContinuousMap.toLp 2 μ ℂ F)
  have h2 := (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ F)
  have h3 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (F.comp (ContinuousMap.mulLeft g))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx3]
  exact hx2

/-- Translating the values of `kernelOp μ u` translates `u`. -/
theorem translate_mul_kernelOp (g : A) (u : C(A, Lp ℂ 2 μ)) :
    translate μ g * kernelOp μ u = kernelOp μ (u.comp (ContinuousMap.mulLeft g)) := by
  ext1 f
  rw [mul_apply_eq_comp, kernelOp_apply, kernelOp_apply, translate_toLp]
  rfl

/-- `g ↦ translate μ g * kernelOp μ u` is continuous for the operator norm. -/
theorem continuous_translate_mul_kernelOp (u : C(A, Lp ℂ 2 μ)) :
    Continuous fun g : A => translate μ g * kernelOp μ u := by
  simp_rw [translate_mul_kernelOp]
  exact (continuous_kernelOp μ).comp (continuous_comp_mulLeft u)

/-- Precomposing `kernelOp μ u` with a translation translates the values of `u` the other
way. -/
theorem kernelOp_mul_translate (g : A) (u : C(A, Lp ℂ 2 μ)) :
    kernelOp μ u * translate μ g =
      kernelOp μ
        ((⟨translate μ g⁻¹, (translate μ g⁻¹).continuous⟩ : C(Lp ℂ 2 μ, Lp ℂ 2 μ)).comp u) := by
  ext1 f
  rw [mul_apply_eq_comp, kernelOp_apply, kernelOp_apply]
  congr 1
  ext x
  simp only [innerCM_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [← inner_translate_translate μ g (translate μ g⁻¹ (u x)) f, ← mul_apply_eq_comp,
    translate_mul, mul_inv_cancel, translate_one, one_apply_eq_self]

/-- The continuous map `x ↦ ψ (· / x)` from `A` to `L²(A, μ)`. -/
def kernel (ψ : C(A, ℂ)) : C(A, Lp ℂ 2 μ) :=
  (⟨ContinuousMap.toLp 2 μ ℂ, (ContinuousMap.toLp 2 μ ℂ).continuous⟩ :
    C(C(A, ℂ), Lp ℂ 2 μ)).comp (shift ψ)

omit [μ.IsMulLeftInvariant] in
/-- Evaluation of `kernel μ ψ`. -/
theorem kernel_apply (ψ : C(A, ℂ)) (x : A) :
    kernel μ ψ x = ContinuousMap.toLp 2 μ ℂ (shift ψ x) :=
  rfl

/-- The convolution kernel is translation-equivariant. -/
theorem kernel_mul (ψ : C(A, ℂ)) (g x : A) :
    kernel μ ψ (g * x) = translate μ g⁻¹ (kernel μ ψ x) := by
  rw [kernel_apply, kernel_apply, translate_toLp]
  congr 1
  ext y
  simp only [shift_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft]
  congr 1
  simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm]

/-- Convolution operators commute with translations. -/
theorem translate_mul_kernelOp_kernel (ψ : C(A, ℂ)) (g : A) :
    translate μ g * kernelOp μ (kernel μ ψ) = kernelOp μ (kernel μ ψ) * translate μ g := by
  rw [translate_mul_kernelOp, kernelOp_mul_translate]
  congr 1
  ext1 x
  exact kernel_mul μ ψ g x

/-- If `ψ ≠ 0` and `ψ (y) ψ (y / a)` vanishes identically, then the convolution operator with
kernel `ψ` is not fixed by the translation by `a`. -/
theorem translate_mul_kernelOp_kernel_ne [μ.IsOpenPosMeasure] {a : A} (ψ : C(A, ℂ)) (hψ : ψ ≠ 0)
    (hψa : ∀ y, ψ y * conj (ψ (y / a)) = 0) :
    translate μ a * kernelOp μ (kernel μ ψ) ≠ kernelOp μ (kernel μ ψ) := by
  intro h
  have h1 := congrArg (fun T => T (ContinuousMap.toLp 2 μ ℂ ψ)) h
  simp only [mul_apply_eq_comp, kernelOp_apply, translate_toLp] at h1
  have h2 := congrArg (fun F : C(A, ℂ) => F 1) (ContinuousMap.toLp_injective μ h1)
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, mul_one, innerCM_apply,
    kernel_apply] at h2
  have hs1 : shift ψ 1 = ψ := by ext y; simp
  rw [hs1, ContinuousMap.inner_toLp, ContinuousMap.inner_toLp] at h2
  simp only [shift_apply, hψa, MeasureTheory.integral_zero] at h2
  have h3 : ⟪ContinuousMap.toLp 2 μ ℂ ψ, ContinuousMap.toLp 2 μ ℂ ψ⟫_ℂ ≠ 0 := by
    rw [Ne, inner_self_eq_zero, ← map_zero (ContinuousMap.toLp 2 μ ℂ)]
    exact fun h => hψ (ContinuousMap.toLp_injective μ h)
  rw [ContinuousMap.inner_toLp] at h3
  exact h3 h2.symm

end Translate

end Stacks.Pontryagin
