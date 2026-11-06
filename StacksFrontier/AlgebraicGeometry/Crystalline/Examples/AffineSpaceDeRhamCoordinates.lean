module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerDerivationLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpacePartialDerivatives
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The one-forms of `D = 𝐙_p[x_1, …, x_r]^∧` read in coordinates

In the setup of the example of [Stacks, Tag 07LK] the source identifies the complex
`D → Ω¹_D → ⋯ → Ω^r_D` with an explicit complex of coefficients.  This module supplies the
functionals that make the identification: the `r` coordinate functionals

`Ω¹_{D/A,δ} → D`, `dx_k ↦ 1`, `dx_j ↦ 0` for `j ≠ k`,

and the resulting reading of the degree zero differential of the complex as the tuple of formal
partial derivatives.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.instIsAddTorsionFreeD` — `D` is torsion free.
* `Crystalline.AffineSpaceCrystallineSetup.instIsAdicCompleteBaseIdealD` — `D` is `p`-adically
  complete as a module over the crystalline base `A = 𝐙_p`, so that `Ω^0_D = D`.
* `Crystalline.AffineSpaceCrystallineSetup.coordinateFunctional` — the functional
  `Ω¹_{D/A,δ} → D` attached to `∂/∂x_k`, with
  `coordinateFunctional_coordinateDifferential` computing it on `dx_1, …, dx_r`.
* `Crystalline.AffineSpaceCrystallineSetup.completedFormsZeroEquiv` — the identification
  `Ω^0_D = D` of the degree zero term of the displayed complex with `D`.
* `Crystalline.AffineSpaceCrystallineSetup.completedFormsOneFunctional_completedDifferential` —
  **the degree zero differential of the displayed complex is the tuple of formal partial
  derivatives**: the `k`-th functional of `Ω¹_D` applied to `d ξ` is `∂(ξ)/∂x_k`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07GM](https://stacks.math.columbia.edu/tag/07GM)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-! ### `D` is torsion free -/

/-- `p` is nonzero in the polynomial lift `P = 𝐙_p[x_1, …, x_r]`. -/
public theorem natCast_ne_zero_polynomial : (T.p : T.P) ≠ 0 := by
  have hp : T.p.Prime := Fact.out
  rw [show (T.p : T.P) = MvPolynomial.C (T.p : T.A) from (map_natCast _ _).symm,
    Ne, MvPolynomial.C_eq_zero]
  exact_mod_cast hp.ne_zero

/-- A multiple of `p^v` lying in `p^{e+v} P` is `p^v` times an element of `p^e P`:
`P` is a domain in which `p` is nonzero. -/
public theorem mem_levelFiltration_of_pow_mul_mem (e v : ℕ) {x : T.P}
    (h : (T.p : T.P) ^ v * x ∈ T.levelFiltration (e + v)) : x ∈ T.levelFiltration e := by
  obtain ⟨y, hy⟩ := (T.mem_levelFiltration_iff _ _).mp h
  refine (T.mem_levelFiltration_iff e x).mpr ⟨y, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero v T.natCast_ne_zero_polynomial) ?_
  rw [hy, pow_add]
  ring

/-- An element of `D` killed by `p^v` vanishes. -/
public theorem eq_zero_of_pow_nsmul_eq_zero (v : ℕ) {a : T.D} (h : (T.p ^ v) • a = 0) :
    a = 0 := by
  apply AdicCompletion.ext
  intro e
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration (e + v)) (a.val (e + v))
  have h1 : (T.p ^ v) • a.val (e + v) = 0 := by
    rw [← AdicCompletion.val_smul_apply, h, AdicCompletion.val_zero_apply]
  rw [← hx, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, nsmul_eq_mul,
    Nat.cast_pow] at h1
  have hxe : x ∈ T.levelFiltration e := T.mem_levelFiltration_of_pow_mul_mem e v h1
  rw [← AdicCompletion.transitionMap_comp_eval_apply _ _ (Nat.le_add_right e v) a, ← hx]
  show (T.levelFiltration e).mkQ x = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hxe

/-- A natural number not divisible by `p` is a unit in the crystalline base `A = 𝐙_p`. -/
public theorem isUnit_natCast_of_not_dvd {m : ℕ} (hm : ¬ T.p ∣ m) : IsUnit (m : T.A) := by
  by_contra hcon
  rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hcon
  obtain ⟨c, hc⟩ := hcon
  have hz := congrArg PadicInt.toZMod hc
  rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
    ZMod.natCast_eq_zero_iff] at hz
  exact hm hz

/-- An element of `D` killed by a natural number prime to `p` vanishes. -/
public theorem eq_zero_of_nsmul_eq_zero_of_not_dvd {m : ℕ} (hm : ¬ T.p ∣ m) {a : T.D}
    (h : m • a = 0) : a = 0 := by
  have hu : IsUnit ((m : T.A)) := T.isUnit_natCast_of_not_dvd hm
  have hu' : IsUnit ((m : T.D)) := by
    have hmap := hu.map (algebraMap T.A T.D)
    rwa [map_natCast] at hmap
  refine hu'.mul_right_eq_zero.mp ?_
  rw [← nsmul_eq_mul]
  exact h

/-- **`D = 𝐙_p[x_1, …, x_r]^∧` is torsion free.** -/
public instance instIsAddTorsionFreeD : IsAddTorsionFree T.D := by
  have hp2 : 2 ≤ T.p := (Fact.out : T.p.Prime).two_le
  have key : ∀ n : ℕ, n ≠ 0 → ∀ a : T.D, n • a = 0 → a = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn a ha
      by_cases hdvd : T.p ∣ n
      · obtain ⟨m, rfl⟩ := hdvd
        have hm : m ≠ 0 := by
          rintro rfl
          simp at hn
        have hlt : m < T.p * m := by
          have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          have hle : 2 * m ≤ T.p * m := Nat.mul_le_mul hp2 (le_refl m)
          omega
        refine ih m hlt hm a (T.eq_zero_of_pow_nsmul_eq_zero 1 ?_)
        rw [pow_one, ← mul_smul]
        exact ha
      · exact T.eq_zero_of_nsmul_eq_zero_of_not_dvd hdvd ha
  constructor
  intro n hn a b _ hab'
  rw [← sub_eq_zero]
  exact key n hn (a - b) (by rw [smul_sub, hab', sub_self])

/-- `D` has unique division by nonzero naturals (torsion-freeness of a commutative group). -/
public instance instHasUniqueDivD : HasUniqueDiv T.D :=
  ⟨fun _ hn a b h ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) h⟩

/-- `D` is `p`-adically complete as a module over the crystalline base `A = 𝐙_p`: the ideal
`(p) ⊆ 𝐙_p` generates the ideal `(p) ⊆ D` for which `D` is the completion of `P`. -/
public instance instIsAdicCompleteBaseIdealD : IsAdicComplete T.baseIdeal T.D := by
  have hmap : T.baseIdeal.map (algebraMap T.A T.D) = DividedPowers.pAdicIdeal (A := T.D) T.p := by
    rw [baseIdeal, Ideal.map_span]
    simp
  have h1 : IsHausdorff T.baseIdeal T.D := by
    rw [← IsHausdorff.map_algebraMap_iff (S := T.D) (I := T.baseIdeal) (M := T.D), hmap]
    infer_instance
  have h2 : IsPrecomplete T.baseIdeal T.D := by
    rw [← IsPrecomplete.map_algebraMap_iff (S := T.D) (I := T.baseIdeal) (M := T.D), hmap]
    infer_instance
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

/-! ### The coordinate functionals on one-forms -/

/-- **The `k`-th coordinate functional on `Ω¹_{D/A,δ}`**: the `D`-linear functional sending the
universal divided power differential `d b` to `∂b/∂x_k`. -/
public def coordinateFunctional (k : Fin T.r) : T.differentials →ₗ[T.D] T.D :=
  liftDividedPowerDifferentials T.completedDividedPowers (T.pderiv k)

/-- The `k`-th coordinate functional carries `d b` to the `k`-th partial derivative of `b`. -/
@[simp]
public theorem coordinateFunctional_differential (k : Fin T.r) (b : T.D) :
    T.coordinateFunctional k (T.differential b) = T.pderiv k b :=
  liftDividedPowerDifferentials_apply T.completedDividedPowers (T.pderiv k) b

/-- The coordinate functionals read off the coefficients of the differentials of the
coordinates: `dx_j ↦ 1` for `j = k` and `dx_j ↦ 0` otherwise. -/
public theorem coordinateFunctional_coordinateDifferential (k j : Fin T.r) :
    T.coordinateFunctional k (T.coordinateDifferential j) = if j = k then 1 else 0 := by
  rw [coordinateDifferential, T.coordinateFunctional_differential, T.pderiv_coordinate]

/-! ### The degree zero term of the displayed complex -/

/-- `Ω^0_{D/A,δ} = D`, the degree zero divided power forms being the degree zero exterior
power. -/
public def formsZeroEquiv : T.forms 0 ≃ₗ[T.D] T.D :=
  exteriorPower.zeroEquiv T.D T.differentials

/-- `Ω^1_{D/A,δ} = Ω¹_{D/A,δ}`, the degree one divided power forms being the degree one exterior
power. -/
public def formsOneEquiv : T.forms 1 ≃ₗ[T.D] T.differentials :=
  exteriorPower.oneEquiv T.D T.differentials

/-- The de Rham differential in degree zero, read through `Ω^0 = D` and `Ω^1 = Ω¹`, is the
universal divided power differential of `D`. -/
public theorem formsOneEquiv_deRhamDifferential_zero (omega : T.forms 0) :
    T.formsOneEquiv (T.deRhamDifferential 0 omega) = T.differential (T.formsZeroEquiv omega) := by
  set b := T.formsZeroEquiv omega with hb
  have hzero : b • exteriorPower.ιMulti T.D 0
      (fun _ : Fin 0 ↦ dividedPowerDifferential (A := T.A) T.completedDividedPowers b) =
      omega := by
    refine T.formsZeroEquiv.injective ?_
    show exteriorPower.zeroEquiv T.D T.differentials
      (b • exteriorPower.ιMulti T.D 0
        (fun _ : Fin 0 ↦ dividedPowerDifferential (A := T.A) T.completedDividedPowers b)) = b
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  have hgen := (dividedPowerDeRhamComplex (A := T.A)
    T.completedDividedPowers).differential_generator 0 (fun _ : Fin 1 ↦ b)
  rw [hzero] at hgen
  show T.formsOneEquiv ((dividedPowerDeRhamComplex (A := T.A)
    T.completedDividedPowers).differential 0 omega) = T.differential b
  rw [hgen]
  show exteriorPower.oneEquiv T.D T.differentials
    (exteriorPower.ιMulti T.D 1
      (fun _ : Fin 1 ↦ dividedPowerDifferential (A := T.A) T.completedDividedPowers b)) =
    T.differential b
  rw [← exteriorPower.oneEquiv_symm_apply, LinearEquiv.apply_symm_apply]

/-- The `A`-linear functional on `Ω^1_{D/A,δ}` underlying the `k`-th coordinate functional. -/
public def formsOneFunctional (k : Fin T.r) : T.forms 1 →ₗ[T.A] T.D :=
  ((T.coordinateFunctional k).comp T.formsOneEquiv.toLinearMap).restrictScalars T.A

/-- The `A`-linear functional on `Ω^1_{D/A,δ}` is the coordinate functional read through
`Ω^1 = Ω¹`. -/
@[simp]
public theorem formsOneFunctional_apply (k : Fin T.r) (omega : T.forms 1) :
    T.formsOneFunctional k omega = T.coordinateFunctional k (T.formsOneEquiv omega) := rfl

/-- The `A`-linear map `Ω^0_{D/A,δ} → D` underlying the identification `Ω^0_D = D`. -/
public def formsZeroMap : T.forms 0 →ₗ[T.A] T.D :=
  (T.formsZeroEquiv.restrictScalars T.A).toLinearMap

/-- **The identification `Ω^0_D = D`** of the degree zero term of the complex displayed in
[Stacks, Tag 07LK] with `D` itself. -/
public def completedFormsZeroEquiv : T.completedForms 0 ≃ₗ[T.A] T.D :=
  ((AdicCompletion.congr T.baseIdeal
      (T.formsZeroEquiv.restrictScalars T.A)).restrictScalars T.A).trans
    (AdicCompletion.ofLinearEquiv T.baseIdeal T.D).symm

/-- The identification `Ω^0_D = D` read against the canonical map into the completion. -/
public theorem of_completedFormsZeroEquiv (xi : T.completedForms 0) :
    AdicCompletion.of T.baseIdeal T.D (T.completedFormsZeroEquiv xi) =
      AdicCompletion.map T.baseIdeal (T.formsZeroMap) xi := by
  show AdicCompletion.of T.baseIdeal T.D ((AdicCompletion.ofLinearEquiv T.baseIdeal T.D).symm
    (AdicCompletion.congr T.baseIdeal (T.formsZeroEquiv.restrictScalars T.A) xi)) = _
  rw [AdicCompletion.of_ofLinearEquiv_symm]
  rfl

/-- `Crystalline.AffineSpaceCrystallineSetup.of_completedFormsZeroEquiv`, with the degree zero
term of the complex spelled out as the completion of `Ω^0_{D/A,δ}`. -/
public theorem of_completedFormsZeroEquiv' (xi : AdicCompletion T.baseIdeal (T.forms 0)) :
    AdicCompletion.of T.baseIdeal T.D (T.completedFormsZeroEquiv xi) =
      AdicCompletion.map T.baseIdeal (T.formsZeroMap) xi :=
  T.of_completedFormsZeroEquiv xi

/-- If `g` agrees with the completion of `f : M → N` after composing with `N → N^∧`, with `N`
adically complete, then `g` restricts to `f` along `M → M^∧`. -/
private theorem apply_of_eq_of_of_eq_map {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {I : Ideal R} [IsAdicComplete I N] (f : M →ₗ[R] N)
    (g : AdicCompletion I M → N)
    (h : ∀ xi, AdicCompletion.of I N (g xi) = AdicCompletion.map I f xi) (m : M) :
    g (AdicCompletion.of I M m) = f m := by
  refine (AdicCompletion.ofLinearEquiv I N).injective ?_
  show AdicCompletion.of I N _ = AdicCompletion.of I N _
  rw [h, AdicCompletion.map_of]

/-- The identification `Ω^0_D = D` agrees with `Ω^0_{D/A,δ} = D` on the dense image. -/
@[simp]
public theorem completedFormsZeroEquiv_ofForms (omega : T.forms 0) :
    T.completedFormsZeroEquiv (T.ofForms 0 omega) = T.formsZeroEquiv omega := by
  exact apply_of_eq_of_of_eq_map T.formsZeroMap _ T.of_completedFormsZeroEquiv' omega

/-- **The `k`-th coordinate functional on `Ω^1_D`**, the degree one term of the complex displayed
in [Stacks, Tag 07LK]: the `p`-adic completion of the coordinate functional on
`Ω^1_{D/A,δ}`, read back into `D` using that `D` is `p`-adically complete. -/
public def completedFormsOneFunctional (k : Fin T.r) : T.completedForms 1 →ₗ[T.A] T.D :=
  ((AdicCompletion.ofLinearEquiv T.baseIdeal T.D).symm.toLinearMap.restrictScalars T.A).comp
    ((AdicCompletion.map T.baseIdeal (T.formsOneFunctional k)).restrictScalars T.A)

/-- The coordinate functional on `Ω^1_D` read against the canonical map into the completion. -/
public theorem of_completedFormsOneFunctional (k : Fin T.r) (eta : T.completedForms 1) :
    AdicCompletion.of T.baseIdeal T.D (T.completedFormsOneFunctional k eta) =
      AdicCompletion.map T.baseIdeal (T.formsOneFunctional k) eta := by
  show AdicCompletion.of T.baseIdeal T.D ((AdicCompletion.ofLinearEquiv T.baseIdeal T.D).symm
    (AdicCompletion.map T.baseIdeal (T.formsOneFunctional k) eta)) = _
  rw [AdicCompletion.of_ofLinearEquiv_symm]

/-- The coordinate functional on `Ω^1_D` agrees with the one on `Ω^1_{D/A,δ}` on the dense
image. -/
@[simp]
public theorem completedFormsOneFunctional_ofForms (k : Fin T.r) (omega : T.forms 1) :
    T.completedFormsOneFunctional k (T.ofForms 1 omega) =
      T.coordinateFunctional k (T.formsOneEquiv omega) := by
  exact apply_of_eq_of_of_eq_map (T.formsOneFunctional k) _ (T.of_completedFormsOneFunctional k)
    omega

/-- The canonical map into the completion carries the formal partial derivative to its
completion. -/
public theorem of_pderiv (k : Fin T.r) (y : T.D) :
    AdicCompletion.of T.baseIdeal T.D (T.pderiv k y) =
      AdicCompletion.map T.baseIdeal (T.pderivHom k) (AdicCompletion.of T.baseIdeal T.D y) :=
  (AdicCompletion.map_of T.baseIdeal (T.pderivHom k) y).symm

/-- The uncompleted form of the identification of the degree zero differential: on
`Ω^0_{D/A,δ}` the composite of the de Rham differential with the `k`-th coordinate functional
is the `k`-th formal partial derivative. -/
public theorem formsOneFunctional_comp_deRhamDifferential_zero (k : Fin T.r) :
    (T.formsOneFunctional k) ∘ₗ (T.deRhamDifferential 0) =
      (T.pderivHom k) ∘ₗ (T.formsZeroMap) := by
  refine LinearMap.ext fun omega ↦ ?_
  show T.coordinateFunctional k (T.formsOneEquiv (T.deRhamDifferential 0 omega)) =
    T.pderivHom k (T.formsZeroEquiv omega)
  rw [T.formsOneEquiv_deRhamDifferential_zero, T.coordinateFunctional_differential]
  rfl

/-- **The degree zero differential of the complex displayed in [Stacks, Tag 07LK] is the tuple of
formal partial derivatives**: reading `Ω^0_D` as `D` and taking the `k`-th coordinate of `Ω^1_D`,
the differential `d : Ω^0_D → Ω^1_D` becomes `∂/∂x_k`. -/
public theorem completedFormsOneFunctional_completedDifferential (k : Fin T.r)
    (xi : T.completedForms 0) :
    T.completedFormsOneFunctional k (T.completedDifferential 0 xi) =
      T.pderiv k (T.completedFormsZeroEquiv xi) := by
  revert xi
  show ∀ xi : AdicCompletion T.baseIdeal (T.forms 0),
    T.completedFormsOneFunctional k (T.completedDifferential 0 xi) =
      T.pderiv k (T.completedFormsZeroEquiv xi)
  intro xi
  refine (AdicCompletion.ofLinearEquiv T.baseIdeal T.D).injective ?_
  show AdicCompletion.of T.baseIdeal T.D
      (T.completedFormsOneFunctional k (T.completedDifferential 0 xi)) =
    AdicCompletion.of T.baseIdeal T.D (T.pderiv k (T.completedFormsZeroEquiv xi))
  rw [T.of_completedFormsOneFunctional, T.of_pderiv, T.of_completedFormsZeroEquiv']
  show AdicCompletion.map T.baseIdeal (T.formsOneFunctional k)
      (AdicCompletion.map T.baseIdeal (T.deRhamDifferential 0) xi) =
    AdicCompletion.map T.baseIdeal (T.pderivHom k)
      (AdicCompletion.map T.baseIdeal T.formsZeroMap xi)
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply,
    T.formsOneFunctional_comp_deRhamDifferential_zero]

end AffineSpaceCrystallineSetup

end Crystalline

end
