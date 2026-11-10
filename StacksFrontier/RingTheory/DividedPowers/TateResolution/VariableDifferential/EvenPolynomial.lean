module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.OddExtensionLeibniz

/-!
# The differential on an even divided-power variable

This file defines `evenPolynomialDifferential` on the divided-power polynomial algebra `A⟨T⟩`,
sending `T⁽ⁿ⁾` to `f T⁽ⁿ⁻¹⁾`, proves its Leibniz rule and that it is square-zero for a cycle `f`,
and shows that both one-variable extensions are differential graded algebras.
-/

@[expose] public section

namespace DividedPowers.TateResolution

attribute [local implicit_reducible] TwistedModule

universe u v

/-- The differential on the coefficient of `T⁽ⁿ⁾`: it sends `a` to
`(dA a) T⁽ⁿ⁾ + (signRingHom 𝒜 1 a * f) T⁽ⁿ⁻¹⁾`, the second term absent for `n = 0`. -/
noncomputable def evenCoefficientDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f : A) (n : ℕ) :
    A →ₗ[R] EvenVariableAlgebra A :=
  (EvenVariableAlgebra.monomialLinearMap (R := R) n).comp dA +
    if n = 0 then 0 else
      (EvenVariableAlgebra.monomialLinearMap (R := R) (n - 1)).comp
        ((LinearMap.mulRight R f).comp (gradingSignLinearMap 𝒜 1))

/-- The differential on the divided-power polynomial algebra `A⟨T⟩` extending `dA` and
sending `T⁽ⁿ⁾` to `f T⁽ⁿ⁻¹⁾`, assembled coefficientwise from `evenCoefficientDifferential`. -/
noncomputable def evenPolynomialDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f : A) :
    EvenVariableAlgebra A →ₗ[R] EvenVariableAlgebra A :=
  (Finsupp.lsum R (evenCoefficientDifferential 𝒜 dA f)).comp
    ({ toFun := EvenVariableAlgebra.coeff
       map_add' := by intro x y; ext n; simp
       map_smul' := by
         intro r x
         apply Finsupp.ext
         intro n
         simp [EvenVariableAlgebra.coeff_smul] } :
      EvenVariableAlgebra A →ₗ[R] ℕ →₀ A)

private theorem evenCoefficientDifferential_coeff
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f : A) (k n : ℕ) (a : A) :
    (evenCoefficientDifferential 𝒜 dA f k a).coeff n =
      (if k = n then dA a else 0) +
        (if k = n + 1 then signRingHom 𝒜 1 a * f else 0) := by
  by_cases hk : k = 0
  · subst k
    simp [evenCoefficientDifferential, EvenVariableAlgebra.monomialLinearMap_apply,
      EvenVariableAlgebra.coeff_monomial, LinearMap.comp_apply,
      Finsupp.single_apply]
  · have hsub : k - 1 = n ↔ k = n + 1 := by omega
    simp [evenCoefficientDifferential, hk, hsub,
      EvenVariableAlgebra.monomialLinearMap_apply,
      EvenVariableAlgebra.coeff_monomial, LinearMap.comp_apply,
      LinearMap.mulRight_apply, gradingSignLinearMap, Finsupp.single_apply]

/-- `evenPolynomialDifferential` on a monomial `a T⁽ⁿ⁾` is
`(dA a) T⁽ⁿ⁾ + (signRingHom 𝒜 1 a * f) T⁽ⁿ⁻¹⁾`, the second term absent for `n = 0`. -/
theorem evenPolynomialDifferential_monomial
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f : A) (n : ℕ) (a : A) :
    evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial n a) =
      EvenVariableAlgebra.monomial n (dA a) +
        if n = 0 then 0 else
          EvenVariableAlgebra.monomial (n - 1) (signRingHom 𝒜 1 a * f) := by
  by_cases hn : n = 0
  · subst n
    simp [evenPolynomialDifferential, evenCoefficientDifferential,
      EvenVariableAlgebra.coeff_monomial, EvenVariableAlgebra.monomialLinearMap_apply,
      gradingSignLinearMap]
  · simp [evenPolynomialDifferential, evenCoefficientDifferential,
      EvenVariableAlgebra.coeff_monomial, EvenVariableAlgebra.monomialLinearMap_apply, hn,
      LinearMap.mulRight_apply, gradingSignLinearMap]

/-- The coefficient of `T⁽ⁿ⁾` in `evenPolynomialDifferential 𝒜 dA f x` is
`dA (x.coeff n) + signRingHom 𝒜 1 (x.coeff (n + 1)) * f`. -/
public theorem evenPolynomialDifferential_coeff
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f : A) (x : EvenVariableAlgebra A) (n : ℕ) :
    (evenPolynomialDifferential 𝒜 dA f x).coeff n =
      dA (x.coeff n) + signRingHom 𝒜 1 (x.coeff (n + 1)) * f := by
  classical
  change ((Finsupp.lsum R (evenCoefficientDifferential 𝒜 dA f) x.coeff).coeff n) = _
  rw [Finsupp.lsum_apply]
  let c : EvenVariableAlgebra A →+ A :=
    { toFun := fun y => y.coeff n
      map_zero' := by change (0 : ℕ →₀ A) n = 0; simp
      map_add' := by intro y z; change y.coeff n + z.coeff n = _; rfl }
  change c (x.coeff.sum fun b => evenCoefficientDifferential 𝒜 dA f b) = _
  simp only [Finsupp.sum, map_sum]
  change (∑ b ∈ x.coeff.support,
    (evenCoefficientDifferential 𝒜 dA f b (x.coeff b)).coeff n) = _
  simp only [evenCoefficientDifferential_coeff]
  rw [Finset.sum_add_distrib,
    Finset.sum_ite_eq' x.coeff.support n (fun k => dA (x.coeff k)),
    Finset.sum_ite_eq' x.coeff.support (n + 1)
      (fun k => signRingHom 𝒜 1 (x.coeff k) * f)]
  by_cases hn : x.coeff n = 0 <;>
    by_cases hn1 : x.coeff (n + 1) = 0 <;>
    simp [Finsupp.mem_support_iff, hn, hn1]

theorem evenPolynomialDifferential_dpow_monomial_one
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (f : A) (n i : ℕ) (hn : n ≠ 0) (hi : 0 < i) :
    evenPolynomialDifferential 𝒜 dA f
        ((evenVariableDividedPowerStructure d hd γ).dpow n
          (EvenVariableAlgebra.monomial i (1 : A))) =
      evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i (1 : A)) *
        (evenVariableDividedPowerStructure d hd γ).dpow (n - 1)
          (EvenVariableAlgebra.monomial i (1 : A)) := by
  let δ := evenVariableDividedPowerStructure d hd γ
  let C (m : ℕ) :=
    dividedPowerMonomialCoefficient
      m i
  have hC (m : ℕ) : C m = Nat.uniformBell m i := by
    dsimp [C]
    rw [Nat.uniformBell_eq_div m (by omega : i ≠ 0)]
    simp [dividedPowerMonomialCoefficient,
      Nat.mul_comm]
  have hle : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hni : (n - 1) * i + i = n * i := by
    calc
      (n - 1) * i + i = (n - 1) * i + 1 * i := by simp
      _ = ((n - 1) + 1) * i := (Nat.add_mul _ _ _).symm
      _ = n * i := by rw [Nat.sub_add_cancel hle]
  have hrec : C n = Nat.choose (n * i - 1) (i - 1) * C (n - 1) := by
    rw [hC n, hC (n - 1)]
    have h := Nat.uniformBell_succ_left (n - 1) i
    have hni' : (n - 1) * i + i - 1 = n * i - 1 := by rw [hni]
    simpa [Nat.sub_add_cancel hle, hni'] using h
  have hdpn : δ.dpow n (EvenVariableAlgebra.monomial i (1 : A)) =
      EvenVariableAlgebra.monomial (n * i) (C n • (1 : A)) := by
    simpa [C] using
      dpow_monomial_one d hd γ n i hi
  have hdpPrev : δ.dpow (n - 1) (EvenVariableAlgebra.monomial i (1 : A)) =
      EvenVariableAlgebra.monomial ((n - 1) * i) (C (n - 1) • (1 : A)) := by
    simpa [C] using
      dpow_monomial_one d hd γ (n - 1) i hi
  have hd1 : dA (1 : A) = 0 :=
    IsGradedDerivation.d_grade_zero (SetLike.one_mem_graded 𝒜)
  have hsignC : signRingHom 𝒜 1 (C n • (1 : A)) = C n • (1 : A) := by
    have hc : C n • (1 : A) ∈ 𝒜 0 :=
      (𝒜 0).nsmul_mem (SetLike.one_mem_graded 𝒜) (C n)
    rw [signRingHom_of_mem 𝒜 1 0 hc]
    simp
  have hdaC : dA (C n : A) = 0 := by
    apply IsGradedDerivation.d_grade_zero (𝒜 := 𝒜) (d := dA)
    simpa using SetLike.algebraMap_mem_graded 𝒜 (C n : R)
  have hleft : evenPolynomialDifferential 𝒜 dA f
      (EvenVariableAlgebra.monomial (n * i) (C n • (1 : A))) =
      EvenVariableAlgebra.monomial (n * i - 1) (C n • f) := by
    rw [evenPolynomialDifferential_monomial]
    have hpos : n * i ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hn) hi)
    simp [hdaC, hpos]
  have hdiffT : evenPolynomialDifferential 𝒜 dA f
      (EvenVariableAlgebra.monomial i (1 : A)) =
      EvenVariableAlgebra.monomial (i - 1) f := by
    rw [evenPolynomialDifferential_monomial]
    simp [hd1, hi.ne']
  have hright : evenPolynomialDifferential 𝒜 dA f
      (EvenVariableAlgebra.monomial i (1 : A)) *
        EvenVariableAlgebra.monomial ((n - 1) * i) (C (n - 1) • (1 : A)) =
      EvenVariableAlgebra.monomial (n * i - 1) (C n • f) := by
    rw [hdiffT]
    have hpow : n - 1 + 1 = n := by omega
    rw [EvenVariableAlgebra.monomial_mul_monomial]
    have hdeg : i - 1 + (n - 1) * i = n * i - 1 := by
      calc
        i - 1 + (n - 1) * i = (n - 1) * i + i - 1 := by omega
        _ = n * i - 1 := by rw [hni]
    rw [hdeg]
    apply congrArg (EvenVariableAlgebra.monomial (n * i - 1))
    rw [hrec]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    simp only [mul_one]
    rw [(Nat.cast_commute (C (n - 1)) f).eq.symm]
    rw [← mul_assoc]
  change evenPolynomialDifferential 𝒜 dA f (δ.dpow n _ ) = _
  rw [hdpn, hdpPrev, hleft, hright]

theorem evenPolynomialDifferential_dpow_add
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA]
    (x y : A) (hx : x ∈ positiveEvenPart 𝒜)
    (hy : y ∈ positiveEvenPart 𝒜)
    (hxD : ∀ m, m ≠ 0 → dA (γ.dpow m x) = dA x * γ.dpow (m - 1) x)
    (hyD : ∀ m, m ≠ 0 → dA (γ.dpow m y) = dA y * γ.dpow (m - 1) y)
    (n : ℕ) :
    dA (γ.dpow (n + 1) (x + y)) =
      dA (x + y) * γ.dpow n (x + y) := by
  have hEven (z : A) (hz : z ∈ positiveEvenPart 𝒜) (m : ℕ) : γ.dpow m z ∈ evenPart 𝒜 := by
    by_cases hm : m = 0
    · subst m
      rw [γ.dpow_zero hz]
      exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
    · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem hm hz)
  have hEvenX := hEven x hx
  have hEvenY := hEven y hy
  have hD0 : dA (1 : A) = 0 :=
    IsGradedDerivation.d_grade_zero (SetLike.one_mem_graded 𝒜)
  have hdxOdd : dA x ∈ oddPart 𝒜 :=
    differential_positiveEvenPart_oddPart 𝒜 dA hx
  have hdyOdd : dA y ∈ oddPart 𝒜 :=
    differential_positiveEvenPart_oddPart 𝒜 dA hy
  have hmul (a b : A) (ha : a ∈ evenPart 𝒜)
      (hb : b ∈ evenPart 𝒜) :
      dA (a * b) = dA a * b + a * dA b := by
    rw [differential_mul_sign 𝒜 dA, signRingHom_eq_self_evenPart 𝒜 ha]
  have hdy :
      (∑ k ∈ Finset.range (n + 2), γ.dpow k x * dA (γ.dpow (n + 1 - k) y)) =
        (∑ k ∈ Finset.range (n + 1), γ.dpow k x * γ.dpow (n - k) y) * dA y := by
    rw [Finset.sum_range_succ]
    have hz : dA (γ.dpow 0 y) = 0 := by simp [γ.dpow_zero hy, hD0]
    have hend : n + 1 - (n + 1) = 0 := by omega
    rw [hend, hz]
    simp only [mul_zero, add_zero]
    calc
      (∑ k ∈ Finset.range (n + 1), γ.dpow k x * dA (γ.dpow (n + 1 - k) y)) =
          ∑ k ∈ Finset.range (n + 1),
            (γ.dpow k x * γ.dpow (n - k) y) * dA y := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
        have heq : n + 1 - k = (n - k) + 1 := by omega
        rw [heq, hyD (n - k + 1) (by omega)]
        have hcomm₁ : γ.dpow k x * dA y = dA y * γ.dpow k x :=
          evenPart_comm_oddPart 𝒜 (hEvenX k) hdyOdd
        have hcomm₂ : γ.dpow k x * γ.dpow (n - k) y ∈
            evenPart 𝒜 :=
          evenPart_mul_mem 𝒜 (hEvenX k) (hEvenY (n - k))
        calc
          γ.dpow k x * (dA y * γ.dpow (n - k) y) =
              (γ.dpow k x * dA y) * γ.dpow (n - k) y := by rw [mul_assoc]
          _ = (dA y * γ.dpow k x) * γ.dpow (n - k) y := by rw [hcomm₁]
          _ = dA y * (γ.dpow k x * γ.dpow (n - k) y) := by rw [← mul_assoc]
          _ = (γ.dpow k x * γ.dpow (n - k) y) * dA y :=
            (evenPart_comm_oddPart 𝒜 hcomm₂ hdyOdd).symm
      _ = (∑ k ∈ Finset.range (n + 1), γ.dpow k x * γ.dpow (n - k) y) * dA y := by
        rw [Finset.sum_mul]
  have hdx :
      (∑ k ∈ Finset.range (n + 2), dA (γ.dpow k x) * γ.dpow (n + 1 - k) y) =
        (∑ k ∈ Finset.range (n + 1), γ.dpow k x * γ.dpow (n - k) y) * dA x := by
    rw [Finset.sum_range_succ']
    have hz : dA (γ.dpow 0 x) = 0 := by simp [γ.dpow_zero hx, hD0]
    simp only [hz, zero_mul, add_zero]
    calc
      (∑ k ∈ Finset.range (n + 1),
          dA (γ.dpow (k + 1) x) * γ.dpow (n + 1 - (k + 1)) y) =
          ∑ k ∈ Finset.range (n + 1), dA (γ.dpow (k + 1) x) * γ.dpow (n - k) y := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        omega
      _ = ∑ k ∈ Finset.range (n + 1),
          dA x * (γ.dpow k x * γ.dpow (n - k) y) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hxD (k + 1) (by omega)]
        have hidx : k + 1 - 1 = k := by omega
        rw [hidx]
        rw [← mul_assoc]
      _ = dA x * (∑ k ∈ Finset.range (n + 1),
          γ.dpow k x * γ.dpow (n - k) y) := by rw [Finset.mul_sum]
      _ = (∑ k ∈ Finset.range (n + 1),
          γ.dpow k x * γ.dpow (n - k) y) * dA x := by
        have hconvEven : (∑ k ∈ Finset.range (n + 1),
            γ.dpow k x * γ.dpow (n - k) y) ∈ evenPart 𝒜 := by
          apply Submodule.sum_mem
          intro k hk
          exact evenPart_mul_mem 𝒜 (hEvenX k) (hEvenY (n - k))
        exact (evenPart_comm_oddPart 𝒜 hconvEven hdxOdd).symm
  have haddRange (m : ℕ) : γ.dpow m (x + y) =
      ∑ k ∈ Finset.range (m + 1), γ.dpow k x * γ.dpow (m - k) y := by
    rw [γ.dpow_add hx hy, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm (k : ℕ) : dA (γ.dpow k x * γ.dpow (n + 1 - k) y) =
      dA (γ.dpow k x) * γ.dpow (n + 1 - k) y +
        γ.dpow k x * dA (γ.dpow (n + 1 - k) y) :=
    hmul _ _ (hEvenX k) (hEvenY (n + 1 - k))
  rw [haddRange (n + 1), map_sum]
  simp_rw [hterm]
  simp only [Nat.add_assoc]
  rw [Finset.sum_add_distrib, hdy, hdx, ← haddRange n, map_add]
  have hcEven : (γ.dpow n (x + y)) ∈ evenPart 𝒜 := hEven _ (Submodule.add_mem _ hx hy) n
  have hcommX : γ.dpow n (x + y) * dA x = dA x * γ.dpow n (x + y) :=
    evenPart_comm_oddPart 𝒜 hcEven hdxOdd
  have hcommY : γ.dpow n (x + y) * dA y = dA y * γ.dpow n (x + y) :=
    evenPart_comm_oddPart 𝒜 hcEven hdyOdd
  rw [hcommX, hcommY]
  simp [add_mul]

theorem evenPolynomialDifferential_inclusion
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (f a : A) :
    evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.coeffEmbedding a) =
      EvenVariableAlgebra.coeffEmbedding (dA a) := by
  simpa [EvenVariableAlgebra.coeffEmbedding_apply] using
    evenPolynomialDifferential_monomial 𝒜 dA f 0 a

theorem evenPolynomialDifferential_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (f : A) :
    evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial 1 1) =
      EvenVariableAlgebra.coeffEmbedding f := by
  have h : 1 - 1 = 0 := by omega
  have hd1 : dA (1 : A) = 0 :=
    IsGradedDerivation.d_grade_zero (SetLike.one_mem_graded 𝒜)
  rw [evenPolynomialDifferential_monomial, h]
  simp [hd1, EvenVariableAlgebra.coeffEmbedding_apply]

/-- A coefficient of an element of `grade 𝒜 d m` lies in `𝒜 (m - k * d)` when `k * d ≤ m`. -/
private theorem coeff_mem_of_mem_grade
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) {d m k : ℕ} {x : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d m) (hk : k * d ≤ m) :
    x.coeff k ∈ 𝒜 (m - k * d) := by
  simpa [hk] using (EvenVariableAlgebra.mem_grade_iff 𝒜 d m x).mp hx k

/-- A coefficient of an element of `grade 𝒜 d m` vanishes when `m < k * d`. -/
private theorem coeff_eq_zero_of_mem_grade
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) {d m k : ℕ} {x : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d m) (hk : ¬ k * d ≤ m) :
    x.coeff k = 0 := by
  simpa [hk] using (EvenVariableAlgebra.mem_grade_iff 𝒜 d m x).mp hx k

private theorem evenPolynomialDifferential_grade_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd : 0 < d) (f : A) {x : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d 0) :
    evenPolynomialDifferential 𝒜 dA f x = 0 := by
  have hzero (k : ℕ) (hk : 0 < k) : x.coeff k = 0 :=
    coeff_eq_zero_of_mem_grade 𝒜 hx (Nat.not_le_of_gt (Nat.mul_pos hk hd))
  ext k
  rw [evenPolynomialDifferential_coeff]
  by_cases hk : k = 0
  · subst k
    have hda : dA (x.coeff 0) = 0 :=
      IsGradedDerivation.d_grade_zero
        (by simpa using coeff_mem_of_mem_grade 𝒜 hx (k := 0) (by simp))
    simp [hda, hzero 1 (by omega : 0 < 1)]
  · have hkn : 0 < k := Nat.pos_of_ne_zero hk
    simp [hzero k hkn, hzero (k + 1) (by omega)]

private theorem evenPolynomialDifferential_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d hd : ℕ) (hdpos : 0 < d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1))
    {x : EvenVariableAlgebra A} (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (hd + 1)) :
    evenPolynomialDifferential 𝒜 dA f x ∈ EvenVariableAlgebra.grade 𝒜 d hd := by
  rw [EvenVariableAlgebra.mem_grade_iff]
  intro k
  rw [evenPolynomialDifferential_coeff]
  by_cases hkd : k * d ≤ hd
  · have hkdin : k * d ≤ hd + 1 := by omega
    have hbase := coeff_mem_of_mem_grade 𝒜 hx hkdin
    have hbase' : dA (x.coeff k) ∈ 𝒜 (hd - k * d) := by
      have hidx : hd + 1 - k * d = (hd - k * d) + 1 := by omega
      rw [hidx] at hbase
      exact IsGradedDerivation.d_mem hbase
    have hprod : signRingHom 𝒜 1 (x.coeff (k + 1)) * f ∈ 𝒜 (hd - k * d) := by
      by_cases hnext : (k + 1) * d ≤ hd + 1
      · have hnext' := coeff_mem_of_mem_grade 𝒜 hx hnext
        have hsign : signRingHom 𝒜 1 (x.coeff (k + 1)) ∈
            𝒜 (hd + 1 - (k + 1) * d) := by
          rw [signRingHom_of_mem 𝒜 1 _ hnext']
          exact (𝒜 (hd + 1 - (k + 1) * d)).smul_mem _ hnext'
        have hmul : (k + 1) * d = k * d + d := Nat.succ_mul k d
        have hidx : (hd + 1 - (k + 1) * d) + (d - 1) = hd - k * d := by omega
        simpa [hidx] using SetLike.mul_mem_graded hsign hf_grade
      · simp [coeff_eq_zero_of_mem_grade 𝒜 hx hnext]
    simpa [hkd] using Submodule.add_mem _ hbase' hprod
  · have hbase0 : dA (x.coeff k) = 0 := by
      by_cases hbasele : k * d ≤ hd + 1
      · have hbase := coeff_mem_of_mem_grade 𝒜 hx hbasele
        have hidx : hd + 1 - k * d = 0 := by omega
        rw [hidx] at hbase
        exact IsGradedDerivation.d_grade_zero hbase
      · simp [coeff_eq_zero_of_mem_grade 𝒜 hx hbasele]
    have hmul : (k + 1) * d = k * d + d := Nat.succ_mul k d
    have hnext : ¬ (k + 1) * d ≤ hd + 1 := by omega
    have hnext0 := coeff_eq_zero_of_mem_grade 𝒜 hx hnext
    have hbot : dA (x.coeff k) + signRingHom 𝒜 1 (x.coeff (k + 1)) * f = 0 := by
      simp [hbase0, hnext0]
    simpa [hkd] using hbot

private theorem evenPolynomialDifferential_leibniz
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1))
    {i j : ℕ} {x y : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d i)
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d j) :
    evenPolynomialDifferential 𝒜 dA f (x * y) =
      evenPolynomialDifferential 𝒜 dA f x * y +
        (-1 : R) ^ i • (x * evenPolynomialDifferential 𝒜 dA f y) := by
  apply EvenVariableAlgebra.homogeneous_induction_on
    (𝒜 := 𝒜) (d := d) (m := i)
    (P := fun z ↦
      evenPolynomialDifferential 𝒜 dA f (z * y) =
        evenPolynomialDifferential 𝒜 dA f z * y +
          (-1 : R) ^ i • (z * evenPolynomialDifferential 𝒜 dA f y)) hx
  · simp
  · intro n a hnd ha
    apply EvenVariableAlgebra.homogeneous_induction_on
      (𝒜 := 𝒜) (d := d) (m := j)
      (P := fun y ↦
        evenPolynomialDifferential 𝒜 dA f
            (EvenVariableAlgebra.monomial n a * y) =
          evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial n a) * y +
            (-1 : R) ^ i •
              (EvenVariableAlgebra.monomial n a * evenPolynomialDifferential 𝒜 dA f y)) hy
    · simp
    · intro m b hmd hb
      rw [EvenVariableAlgebra.monomial_mul_monomial,
        evenPolynomialDifferential_monomial,
        evenPolynomialDifferential_monomial,
        evenPolynomialDifferential_monomial]
      let C : ℕ := Nat.choose (n + m) n
      have hbase : dA (C • (a * b)) =
          C • (dA a * b + signRingHom 𝒜 1 a * dA b) := by
        calc
          dA (C • (a * b)) = C • dA (a * b) := map_nsmul dA C (a * b)
          _ = C • (dA a * b + signRingHom 𝒜 1 a * dA b) := by
            rw [differential_mul_sign 𝒜 dA]
      have hbase' : dA ((n + m).choose n • (a * b)) =
          (n + m).choose n • (dA a * b + signRingHom 𝒜 1 a * dA b) := by
        simpa [C] using hbase
      have hdEven : Even d := Fact.out
      have hpow (e k : ℕ) (hk : k * d ≤ e) : (-1 : R) ^ e = (-1 : R) ^ (e - k * d) := by
        rw [← Nat.sub_add_cancel hk, pow_add, (hdEven.mul_left k).neg_one_pow, mul_one,
          Nat.add_sub_cancel]
      have hsign (e k : ℕ) (z : A) (hk : k * d ≤ e) (hz : z ∈ 𝒜 (e - k * d)) :
          signRingHom 𝒜 1 z = (-1 : R) ^ e • z := by
        rw [signRingHom_of_mem 𝒜 1 (e - k * d) hz, hpow e k hk]
        simp
      have hsigna := hsign i n a (by omega) ha
      have hsignb := hsign j m b (by omega) hb
      have hfcomm : f * b = (-1 : R) ^ j • (b * f) := by
        have hcomm := IsStrictlyGradedComm.graded_comm
          (𝒜 := 𝒜) hf_grade hb
        have hpow' : (-1 : R) ^ ((d - 1) * (j - m * d)) = (-1 : R) ^ j := by
          rw [pow_mul, Odd.neg_one_pow (Nat.Even.sub_odd hd hdEven odd_one),
            hpow j m (by omega)]
        rw [hpow'] at hcomm
        simpa [smul_eq_mul] using hcomm
      -- The coefficient equality is the Leibniz rule in `A` and Pascal's identity.
      ext k
      by_cases hkn : k = n + m
      · subst k
        rw [hbase']
        by_cases hsum : n + m = 0
        · have hn0 : n = 0 := by omega
          have hm0 : m = 0 := by omega
          subst n
          subst m
          simp [EvenVariableAlgebra.coeff_monomial,
            EvenVariableAlgebra.monomial_mul_monomial, hsigna]
        · by_cases hn0 : n = 0
          · subst n
            have hm0 : m ≠ 0 := by omega
            have hleft : m - 1 ≠ m := by omega
            simp [EvenVariableAlgebra.coeff_monomial,
              EvenVariableAlgebra.monomial_mul_monomial, hsigna, hsignb, hm0, hleft, mul_add]
          · by_cases hm0 : m = 0
            · subst m
              have hleft : n - 1 ≠ n := by omega
              have hright : n - 1 + 0 ≠ n := by omega
              simp [EvenVariableAlgebra.coeff_monomial,
                EvenVariableAlgebra.monomial_mul_monomial, hsigna, hsignb, hn0, hleft,
                add_mul]
            · have hleft : n + m - 1 ≠ n + m := by omega
              have hright₁ : n - 1 + m ≠ n + m := by omega
              have hright₂ : n + (m - 1) ≠ n + m := by omega
              have hnlt : n - 1 ≠ n := by omega
              have hmlt : m - 1 ≠ m := by omega
              simp [EvenVariableAlgebra.coeff_monomial,
                EvenVariableAlgebra.monomial_mul_monomial, hsigna, hsignb, hn0, hm0, hleft,
                hnlt, hmlt, add_mul, mul_add]
      · by_cases hkp : k = n + m - 1
        · subst k
          have hsumPos : 0 < n + m := by omega
          have hneq : n + m ≠ n + m - 1 := Ne.symm hkn
          by_cases hn0 : n = 0
          · subst n
            have hm0 : m ≠ 0 := by omega
            have hneq' : m ≠ m - 1 := by omega
            simp [EvenVariableAlgebra.coeff_monomial,
              EvenVariableAlgebra.monomial_mul_monomial, hneq', hsigna, hsignb, hm0, mul_add,
              smul_smul, mul_comm ((-1 : R) ^ j) ((-1 : R) ^ i), mul_assoc]
          · by_cases hm0 : m = 0
            · subst m
              have hneq' : n ≠ n - 1 := by omega
              simp [EvenVariableAlgebra.coeff_monomial,
                EvenVariableAlgebra.monomial_mul_monomial, hneq', hsigna, hsignb, hn0, add_mul,
                hfcomm, smul_smul,
                mul_comm ((-1 : R) ^ j) ((-1 : R) ^ i), mul_assoc]
            · have hpascal : Nat.choose (n + m) n =
                  Nat.choose (n + m - 1) (n - 1) +
                    Nat.choose (n + m - 1) n := by
                have hsum : n + m - 1 + 1 = n + m := by omega
                have hn : n - 1 + 1 = n := by omega
                simpa [hsum, hn] using
                  (Nat.choose_succ_succ' (n + m - 1) (n - 1))
              have hidx₁ : n - 1 + m = n + m - 1 := by omega
              have hidx₂ : n + (m - 1) = n + m - 1 := by omega
              simp [EvenVariableAlgebra.coeff_monomial,
                EvenVariableAlgebra.monomial_mul_monomial, hkn, hsigna, hsignb, hfcomm, hn0, hm0,
                hidx₁, hidx₂, hpascal, smul_smul, add_mul, mul_add, mul_assoc,
                mul_comm ((-1 : R) ^ j) ((-1 : R) ^ i)]
        · by_cases hsum : n + m = 0
          · have hn0 : n = 0 := by omega
            have hm0 : m = 0 := by omega
            subst n
            subst m
            simp [EvenVariableAlgebra.coeff_monomial, hkn,
              EvenVariableAlgebra.monomial_mul_monomial]
          · have hkn' : n + m ≠ k := Ne.symm hkn
            have hkp' : n + m - 1 ≠ k := Ne.symm hkp
            by_cases hn0 : n = 0
            · subst n
              have hm0 : m ≠ 0 := by omega
              have hmk : m ≠ k := by omega
              have hmk' : m - 1 ≠ k := by omega
              simp [EvenVariableAlgebra.coeff_monomial, hm0,
                hmk, hmk',
                EvenVariableAlgebra.monomial_mul_monomial, mul_add]
            · by_cases hm0 : m = 0
              · subst m
                have hidx : n - 1 + 0 = n + 0 - 1 := by omega
                have hnk : n ≠ k := by omega
                have hnk' : n - 1 ≠ k := by omega
                simp [EvenVariableAlgebra.coeff_monomial, hn0,
                  hnk, hnk',
                  hidx, EvenVariableAlgebra.monomial_mul_monomial, add_mul]
              · have hidx₁ : n - 1 + m = n + m - 1 := by omega
                have hidx₂ : n + (m - 1) = n + m - 1 := by omega
                simp [EvenVariableAlgebra.coeff_monomial, hkn', hkp', hn0, hm0, hidx₁,
                  hidx₂, EvenVariableAlgebra.monomial_mul_monomial, add_mul, mul_add]
    · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
      rw [mul_add, map_add, map_add, ih₁, ih₂]
      simp [mul_add, smul_add, add_assoc]
      abel
  · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
    rw [add_mul, map_add, ih₁, ih₂]
    simp [add_mul, smul_add, add_assoc]
    abel

/-- The differential of an even divided-power variable extension is a graded derivation. Unlike
`evenPolynomialDifferential_isDGA` this needs no cycle hypothesis on `f`, since a graded
derivation is not required to be square-zero. -/
theorem evenPolynomialDifferential_isGradedDerivation
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) :
    IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d)
      (evenPolynomialDifferential 𝒜 dA f) where
  d_grade_zero hx := evenPolynomialDifferential_grade_zero 𝒜 dA d hd f hx
  d_mem hx := evenPolynomialDifferential_mem 𝒜 dA d _ hd f hf_grade hx
  leibniz hx hy := evenPolynomialDifferential_leibniz 𝒜 dA d hd f hf_grade hx hy

private theorem evenPolynomialDifferential_sq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (d : ℕ) [Fact (Even d)] (hdpos : 0 < d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1))
    (hf_cycle : dA f = 0) (x : EvenVariableAlgebra A) :
    evenPolynomialDifferential 𝒜 dA f
      (evenPolynomialDifferential 𝒜 dA f x) = 0 := by
  have hd_even : Even d := Fact.out
  have hd_odd : Odd (d - 1) := Nat.Even.sub_odd hdpos hd_even odd_one
  have hf_sq : f * f = 0 := by
    rcases hd_odd with ⟨k, hk⟩
    have hidx : d - 1 = 2 * k + 1 := hk
    rw [hidx] at hf_grade
    simpa [pow_two] using IsStrictlyGradedComm.odd_sq_zero hf_grade
  ext n
  rw [evenPolynomialDifferential_coeff 𝒜 dA f
      (evenPolynomialDifferential 𝒜 dA f x) n,
    evenPolynomialDifferential_coeff 𝒜 dA f x n,
    evenPolynomialDifferential_coeff 𝒜 dA f x (n + 1)]
  simp only [map_add]
  rw [IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := dA) (x.coeff n)]
  have hcycle := differential_mul_cycle 𝒜 dA hf_grade hf_cycle (signRingHom 𝒜 1 (x.coeff (n + 1)))
  rw [hcycle]
  have hanti := gradingSign_anticommutes_differential 𝒜 dA (x.coeff (n + 1))
  have hanti' : dA (signRingHom 𝒜 1 (x.coeff (n + 1))) =
      -signRingHom 𝒜 1 (dA (x.coeff (n + 1))) :=
    eq_neg_of_add_eq_zero_right hanti
  rw [hanti']
  have hlast :
      signRingHom 𝒜 1
          (signRingHom 𝒜 1 (x.coeff (n + 2)) * f) * f = 0 := by
    rw [map_mul, signRingHom_involutive 𝒜 1]
    rw [signRingHom_of_mem 𝒜 1 (d - 1) hf_grade]
    have hpow : (-1 : R) ^ (d - 1) = -1 := Odd.neg_one_pow hd_odd
    rw [Nat.one_mul, hpow, neg_one_smul]
    simp [hf_sq, mul_assoc]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [add_mul]
  rw [hlast]
  simp

/-- For even positive `d` and a cycle `f` of degree `d - 1`, `evenPolynomialDifferential`
makes the divided-power polynomial algebra a differential graded algebra. -/
theorem evenPolynomialDifferential_isDGA
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1)) (hf_cycle : dA f = 0) :
    IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 d)
      (evenPolynomialDifferential 𝒜 dA f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact evenPolynomialDifferential_grade_zero 𝒜 dA d hd f hx
  · intro n x hx
    exact evenPolynomialDifferential_mem 𝒜 dA d n hd f hf_grade hx
  · intro x
    exact evenPolynomialDifferential_sq_zero 𝒜 dA d hd f hf_grade hf_cycle x
  · intro i j x y hx hy
    exact evenPolynomialDifferential_leibniz 𝒜 dA d hd f hf_grade hx hy

/-- For odd positive `d` and a cycle `f` of degree `d - 1`, `oddExtensionDifferential`
makes the odd-variable extension `A⟨T⟩` a differential graded algebra. -/
theorem oddExtensionDifferential_isDGA
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1)) (hf_cycle : dA f = 0) :
    IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 d)
      (oddExtensionDifferential 𝒜 dA d f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact oddExtensionDifferential_grade_zero 𝒜 dA d hd f
  · intro n x hx
    exact oddExtensionDifferential_mem 𝒜 dA d hd f hf_grade hx
  · intro x
    exact oddExtensionDifferential_sq_zero 𝒜 dA d hd_odd f hf_grade hf_cycle x
  · intro i j x y hx hy
    exact oddExtensionDifferential_leibniz 𝒜 dA d hd_odd f hf_grade hx hy

end DividedPowers.TateResolution
