module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamCoordinates

/-!
# `H⁰` of the complex displayed in [Stacks, Tag 07LK] is `𝐙_p`

This module proves conclusion (2) of the example of [Stacks, Tag 07LK] for the complex the source
displays, `D → Ω¹_D → ⋯ → Ω^r_D`, and for every number `r` of variables: the kernel of its degree
zero differential is the crystalline base `A = 𝐙_p`.

The degree zero differential is the tuple of formal partial derivatives `(∂/∂x_1, …, ∂/∂x_r)` on
`D = 𝐙_p[x_1, …, x_r]^∧`, and an element of `D` all of whose partial derivatives vanish is a
constant.  The `m`-th monomial coefficient `D → 𝐙_p`
(`Crystalline.AffineSpaceCrystallineSetup.monomialCoeff`) is defined level by level from
`MvPolynomial.lcoeff m`, and an element of `D` is determined by its monomial coefficients.

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.monomialCoeff` — the `m`-th monomial coefficient of an
  element of `D`.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.monomialCoeff_algebraMap` — on polynomials it is the
  monomial coefficient.
* `Crystalline.AffineSpaceCrystallineSetup.eq_zero_of_monomialCoeff_eq_zero` — an element of `D`
  is determined by its monomial coefficients.
* `Crystalline.AffineSpaceCrystallineSetup.eq_algebraMap_of_pderiv_eq_zero` — an element of `D`
  with vanishing partial derivatives is the image of an element of `𝐙_p`.
* `Crystalline.AffineSpaceCrystallineSetup.kerCompletedDifferentialZeroEquiv` — **conclusion (2)
  of [Stacks, Tag 07LK] for the displayed complex**: the kernel of
  `d : Ω^0_D → Ω^1_D` is `𝐙_p`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-! ### The `p`-adic filtration of the crystalline base -/

/-- `𝐙_p` is `p`-adically complete. -/
public instance instIsAdicCompleteBaseIdealA : IsAdicComplete T.baseIdeal T.A := by
  change IsAdicComplete (Ideal.span {(T.p : T.A)}) T.A
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

/-- A multiple of `p^n` lies in the `n`-th step of the `p`-adic filtration of `𝐙_p`. -/
public theorem pow_mul_mem_baseIdeal_pow_smul (n : ℕ) (c : T.A) :
    (T.p : T.A) ^ n * c ∈ T.baseIdeal ^ n • (⊤ : Submodule T.A T.A) := by
  rw [baseIdeal, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨c, Submodule.mem_top, by rw [smul_eq_mul]⟩

/-- An element of the `n`-th step of the `p`-adic filtration of `𝐙_p` is a multiple of `p^n`. -/
public theorem exists_eq_pow_mul_of_mem_baseIdeal_pow_smul (n : ℕ) {c : T.A}
    (h : c ∈ T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)) :
    ∃ d : T.A, c = (T.p : T.A) ^ n * d := by
  rw [baseIdeal, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨d, -, hd⟩ := h
  exact ⟨d, by rw [← hd, smul_eq_mul]⟩

/-- A polynomial all of whose coefficients are divisible by `p^n` is divisible by `p^n`. -/
public theorem mem_levelFiltration_of_forall_coeff (n : ℕ) {x : T.P}
    (h : ∀ m, x.coeff m ∈ T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)) :
    x ∈ T.levelFiltration n := by
  classical
  have hC : ((T.p : T.P) ^ n) = MvPolynomial.C ((T.p : T.A) ^ n) := by
    rw [map_pow, map_natCast]
  choose d hd using fun m ↦ T.exists_eq_pow_mul_of_mem_baseIdeal_pow_smul n (h m)
  refine (T.mem_levelFiltration_iff n x).mpr
    ⟨∑ m ∈ x.support, MvPolynomial.monomial m (d m), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [MvPolynomial.as_sum x]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [hd m, hC, MvPolynomial.C_mul_monomial]

/-! ### The monomial coefficients of `D` -/

/-- The `m`-th monomial coefficient of a polynomial, read modulo `p^n`. -/
public def monomialCoeffLevel (m : Fin T.r →₀ ℕ) (n : ℕ) :
    T.P ⧸ T.levelFiltration n →ₗ[T.A] T.A ⧸ (T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)) :=
  Submodule.mapQ ((T.levelFiltration n).restrictScalars T.A)
    (T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)) (MvPolynomial.lcoeff T.A m) (by
      intro x hx
      obtain ⟨y, rfl⟩ := (T.mem_levelFiltration_iff n x).mp hx
      have hC : ((T.p : T.P) ^ n) = MvPolynomial.C ((T.p : T.A) ^ n) := by
        rw [map_pow, map_natCast]
      change ((T.p : T.P) ^ n * y).coeff m ∈
        T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)
      rw [hC, MvPolynomial.coeff_C_mul]
      exact T.pow_mul_mem_baseIdeal_pow_smul n _)

/-- The level map is the monomial coefficient on representatives. -/
@[simp]
public theorem monomialCoeffLevel_mkQ (m : Fin T.r →₀ ℕ) (n : ℕ) (x : T.P) :
    T.monomialCoeffLevel m n ((T.levelFiltration n).mkQ x) =
      (T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)).mkQ (x.coeff m) := rfl

/-- The `m`-th monomial coefficient of an element of `D`, as a compatible family of
coefficients modulo every power of `p`. -/
public def monomialCoeffHom (m : Fin T.r →₀ ℕ) : T.D →ₗ[T.A] AdicCompletion T.baseIdeal T.A where
  toFun a := ⟨fun n ↦ T.monomialCoeffLevel m n (a.val n), by
    intro i n hin
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (a.val n)
    have hval : a.val i = (T.levelFiltration i).mkQ x := by
      rw [← AdicCompletion.transitionMap_comp_eval_apply _ _ hin a, ← hx]
      rfl
    change AdicCompletion.transitionMap T.baseIdeal T.A hin
        (T.monomialCoeffLevel m n (a.val n)) = T.monomialCoeffLevel m i (a.val i)
    rw [← hx, hval, T.monomialCoeffLevel_mkQ, T.monomialCoeffLevel_mkQ]
    rfl⟩
  map_add' a b := by
    apply AdicCompletion.ext
    intro n
    change T.monomialCoeffLevel m n ((a + b).val n) =
      T.monomialCoeffLevel m n (a.val n) + T.monomialCoeffLevel m n (b.val n)
    rw [AdicCompletion.val_add_apply, map_add]
  map_smul' c a := by
    apply AdicCompletion.ext
    intro n
    change T.monomialCoeffLevel m n ((c • a).val n) = c • T.monomialCoeffLevel m n (a.val n)
    rw [AdicCompletion.val_smul_apply, map_smul]

/-- **The `m`-th monomial coefficient of an element of `D = 𝐙_p[x_1, …, x_r]^∧`**, a
`𝐙_p`-linear functional. -/
public def monomialCoeff (m : Fin T.r →₀ ℕ) : T.D →ₗ[T.A] T.A :=
  ((AdicCompletion.ofLinearEquiv T.baseIdeal T.A).symm.toLinearMap).comp (T.monomialCoeffHom m)

/-- The monomial coefficient of an element of `D` agrees modulo `p^n` with the corresponding
coefficient of any polynomial representing it at the level `n`. -/
public theorem monomialCoeff_sub_mem (m : Fin T.r →₀ ℕ) (a : T.D) (n : ℕ) (x : T.P)
    (hx : (T.levelFiltration n).mkQ x = a.val n) :
    T.monomialCoeff m a - x.coeff m ∈
      T.baseIdeal ^ n • (⊤ : Submodule T.A T.A) := by
  have hof : AdicCompletion.of T.baseIdeal T.A (T.monomialCoeff m a) = T.monomialCoeffHom m a := by
    show AdicCompletion.of T.baseIdeal T.A ((AdicCompletion.ofLinearEquiv T.baseIdeal T.A).symm
      (T.monomialCoeffHom m a)) = _
    rw [AdicCompletion.of_ofLinearEquiv_symm]
  have hval : (AdicCompletion.of T.baseIdeal T.A (T.monomialCoeff m a)).val n =
      (T.monomialCoeffHom m a).val n := by rw [hof]
  rw [AdicCompletion.of_apply] at hval
  have hright : (T.monomialCoeffHom m a).val n =
      (T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)).mkQ (x.coeff m) := by
    show T.monomialCoeffLevel m n (a.val n) = _
    rw [← hx, T.monomialCoeffLevel_mkQ]
  rw [hright] at hval
  rw [← Submodule.Quotient.eq]
  exact hval

/-- Two elements of `𝐙_p` agreeing modulo every `p^n` are equal. -/
private theorem eq_of_forall_sub_mem_baseIdeal_pow_smul {x y : T.A}
    (h : ∀ n : ℕ, x - y ∈ T.baseIdeal ^ n • (⊤ : Submodule T.A T.A)) : x = y :=
  (IsHausdorff.eq_iff_smodEq (I := T.baseIdeal)).mpr fun n ↦ SModEq.sub_mem.mpr (h n)

/-- On the dense image of `P` the functional is the monomial coefficient of a polynomial. -/
@[simp]
public theorem monomialCoeff_algebraMap (m : Fin T.r →₀ ℕ) (f : T.P) :
    T.monomialCoeff m (algebraMap T.P T.D f) = f.coeff m :=
  T.eq_of_forall_sub_mem_baseIdeal_pow_smul fun n ↦ T.monomialCoeff_sub_mem m _ n f rfl

/-- **An element of `D` is determined by its monomial coefficients.** -/
public theorem eq_zero_of_monomialCoeff_eq_zero {a : T.D} (h : ∀ m, T.monomialCoeff m a = 0) :
    a = 0 := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (a.val n)
  have hcoeff : ∀ m, x.coeff m ∈ T.baseIdeal ^ n • (⊤ : Submodule T.A T.A) := by
    intro m
    have hmem := T.monomialCoeff_sub_mem m a n x hx
    rw [h m, zero_sub] at hmem
    exact (Submodule.neg_mem_iff _).mp hmem
  rw [← hx]
  show (T.levelFiltration n).mkQ x = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact T.mem_levelFiltration_of_forall_coeff n hcoeff

/-- The partial derivative multiplies the coefficient at `m + e_k` by `m_k + 1`. -/
public theorem monomialCoeff_pderiv (k : Fin T.r) (m : Fin T.r →₀ ℕ) (a : T.D) :
    T.monomialCoeff m (T.pderiv k a) =
      T.monomialCoeff (m + Finsupp.single k 1) a * ((m k : T.A) + 1) := by
  refine T.eq_of_forall_sub_mem_baseIdeal_pow_smul fun n ↦ ?_
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (a.val n)
  have hder : (T.levelFiltration n).mkQ (MvPolynomial.pderiv k x) = (T.pderiv k a).val n := by
    rw [T.pderiv_apply, T.val_pderivHom_of_mkQ k a n x hx]
  have h1 := T.monomialCoeff_sub_mem m (T.pderiv k a) n _ hder
  have h2 := T.monomialCoeff_sub_mem (m + Finsupp.single k 1) a n x hx
  have hkey : T.monomialCoeff m (T.pderiv k a) -
      T.monomialCoeff (m + Finsupp.single k 1) a * ((m k : T.A) + 1) =
      (T.monomialCoeff m (T.pderiv k a) - (MvPolynomial.pderiv k x).coeff m) -
        (T.monomialCoeff (m + Finsupp.single k 1) a -
          x.coeff (m + Finsupp.single k 1)) * ((m k : T.A) + 1) := by
    rw [MvPolynomial.coeff_pderiv]
    ring
  rw [hkey]
  refine Submodule.sub_mem _ h1 ?_
  rw [mul_comm]
  exact Submodule.smul_mem _ _ h2

/-- A constant of `D` is the image of the corresponding constant polynomial. -/
private theorem algebraMap_eq_algebraMap_C (c : T.A) :
    algebraMap T.A T.D c = algebraMap T.P T.D (MvPolynomial.C c) :=
  IsScalarTower.algebraMap_apply T.A T.P T.D c

/-- **An element of `D` with vanishing partial derivatives is a constant.**  Every coefficient at
a nonzero multi-index is killed, `m_k + 1` being a nonzerodivisor of `𝐙_p`. -/
public theorem eq_algebraMap_of_pderiv_eq_zero {a : T.D} (h : ∀ k, T.pderiv k a = 0) :
    a = algebraMap T.A T.D (T.monomialCoeff 0 a) := by
  classical
  have hconst : ∀ m : Fin T.r →₀ ℕ,
      T.monomialCoeff m (algebraMap T.A T.D (T.monomialCoeff 0 a)) =
        if m = 0 then T.monomialCoeff 0 a else 0 := by
    intro m
    rw [T.algebraMap_eq_algebraMap_C, T.monomialCoeff_algebraMap, MvPolynomial.coeff_C]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos (by rw [hm])]
    · rw [if_neg hm, if_neg (by simpa [eq_comm] using hm)]
  have hvanish : ∀ m : Fin T.r →₀ ℕ, m ≠ 0 → T.monomialCoeff m a = 0 := by
    intro m hm
    obtain ⟨k, hk⟩ : ∃ k, m k ≠ 0 := by
      by_contra hcon
      exact hm (Finsupp.ext fun k ↦ by simpa using not_exists.mp hcon k)
    set m' := m - Finsupp.single k 1 with hm'
    have hadd : m' + Finsupp.single k 1 = m := by
      rw [hm']
      refine Finsupp.ext fun j ↦ ?_
      by_cases hj : j = k
      · subst hj
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [hj]
    have hzero : T.monomialCoeff m' (T.pderiv k a) = 0 := by rw [h k, map_zero]
    rw [T.monomialCoeff_pderiv, hadd] at hzero
    have hne : ((m' k : T.A) + 1) ≠ 0 := by
      have : ((m' k + 1 : ℕ) : T.A) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      simpa using this
    exact (mul_eq_zero.mp hzero).resolve_right hne
  rw [← sub_eq_zero]
  refine T.eq_zero_of_monomialCoeff_eq_zero fun m ↦ ?_
  rw [map_sub, hconst m]
  by_cases hm : m = 0
  · rw [if_pos hm, hm, sub_self]
  · rw [if_neg hm, hvanish m hm, sub_zero]

/-! ### Conclusion (2) of [Stacks, Tag 07LK] for the displayed complex -/

/-- The `0`-th coefficient of a constant is that constant. -/
@[simp]
public theorem monomialCoeff_zero_algebraMap (c : T.A) :
    T.monomialCoeff 0 (algebraMap T.A T.D c) = c := by
  rw [T.algebraMap_eq_algebraMap_C, T.monomialCoeff_algebraMap, MvPolynomial.coeff_zero_C]

/-- The degree zero differential of the displayed complex kills the constants. -/
public theorem completedDifferential_zero_eq_zero_of_eq_algebraMap {xi : T.completedForms 0}
    {c : T.A} (h : T.completedFormsZeroEquiv xi = algebraMap T.A T.D c) :
    T.completedDifferential 0 xi = 0 := by
  have hxi : xi = T.ofForms 0 (T.formsZeroEquiv.symm (algebraMap T.A T.D c)) := by
    refine T.completedFormsZeroEquiv.injective ?_
    rw [h, T.completedFormsZeroEquiv_ofForms, LinearEquiv.apply_symm_apply]
  have hd : T.deRhamDifferential 0 (T.formsZeroEquiv.symm (algebraMap T.A T.D c)) = 0 := by
    refine T.formsOneEquiv.injective ?_
    rw [T.formsOneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply,
      T.differential_algebraMap, map_zero]
  rw [hxi, T.completedDifferential_ofForms, hd, map_zero]

/-- An element of the kernel of the degree zero differential has vanishing partial
derivatives. -/
public theorem pderiv_completedFormsZeroEquiv_eq_zero {xi : T.completedForms 0}
    (hxi : T.completedDifferential 0 xi = 0) (k : Fin T.r) :
    T.pderiv k (T.completedFormsZeroEquiv xi) = 0 := by
  rw [← T.completedFormsOneFunctional_completedDifferential k xi, hxi, map_zero]

/-- **Conclusion (2) of [Stacks, Tag 07LK] for the complex the source displays.**  The kernel of
the degree zero differential `d : Ω^0_D → Ω^1_D` of the completed divided power de Rham complex
of `D = 𝐙_p[x_1, …, x_r]^∧` is the crystalline base `𝐙_p`: an element of `Ω^0_D = D` is killed
by `d` exactly when all its formal partial derivatives vanish, which for an element of the
`p`-adic completion of a polynomial ring means that it is a constant. -/
public def kerCompletedDifferentialZeroEquiv :
    LinearMap.ker (T.completedDifferential 0) ≃ₗ[T.A] T.A := by
  refine LinearEquiv.ofLinear
    ((T.monomialCoeff 0).comp (T.completedFormsZeroEquiv.toLinearMap.comp
      (LinearMap.ker (T.completedDifferential 0)).subtype))
    (LinearMap.codRestrict _
      (T.completedFormsZeroEquiv.symm.toLinearMap.comp (Algebra.linearMap T.A T.D))
      (fun c ↦ ?_)) ?_ ?_
  · refine LinearMap.mem_ker.mpr
      (T.completedDifferential_zero_eq_zero_of_eq_algebraMap (c := c) ?_)
    change T.completedFormsZeroEquiv (T.completedFormsZeroEquiv.symm (algebraMap T.A T.D c)) = _
    rw [LinearEquiv.apply_symm_apply]
  · refine LinearMap.ext fun c ↦ ?_
    change T.monomialCoeff 0 (T.completedFormsZeroEquiv
      (T.completedFormsZeroEquiv.symm (algebraMap T.A T.D c))) = c
    rw [LinearEquiv.apply_symm_apply, T.monomialCoeff_zero_algebraMap]
  · refine LinearMap.ext fun xi ↦ ?_
    refine Subtype.ext ?_
    change T.completedFormsZeroEquiv.symm
      (algebraMap T.A T.D (T.monomialCoeff 0 (T.completedFormsZeroEquiv xi.1))) = xi.1
    refine T.completedFormsZeroEquiv.injective ?_
    rw [LinearEquiv.apply_symm_apply]
    exact (T.eq_algebraMap_of_pderiv_eq_zero
      (T.pderiv_completedFormsZeroEquiv_eq_zero (LinearMap.mem_ker.mp xi.2))).symm

end AffineSpaceCrystallineSetup

end Crystalline

end
