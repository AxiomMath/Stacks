module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.EvenPolynomial

/-!
# Uniqueness of the differential on a one-variable extension

This file proves that `evenPolynomialDifferential` is compatible with divided powers and that a
differential on a one-variable extension is determined by its values on `A` and on `T`; it then
states the existence and uniqueness theorems for both odd and even variables.
-/

@[expose] public section

namespace DividedPowers.TateResolution

attribute [local implicit_reducible] TwistedModule

universe u v

private theorem evenPolynomialDifferential_dpow_monomial
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1))
    {k i : ℕ} {a : A} (ha : a ∈ 𝒜 (2 * k)) (hi : 0 < i)
    (hz : EvenVariableAlgebra.monomial i a ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d))
    {n : ℕ} (hn : n ≠ 0) :
    evenPolynomialDifferential 𝒜 dA f
        ((evenVariableDividedPowerStructure d hd γ).dpow n (EvenVariableAlgebra.monomial i a)) =
      evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i a) *
        (evenVariableDividedPowerStructure d hd γ).dpow (n - 1)
          (EvenVariableAlgebra.monomial i a) := by
  let δ := evenVariableDividedPowerStructure d hd γ
  let E : A →+* EvenVariableAlgebra A := EvenVariableAlgebra.coeffEmbedding
  let T := EvenVariableAlgebra.monomial i (1 : A)
  let Z := EvenVariableAlgebra.monomial i a
  let D := evenPolynomialDifferential 𝒜 dA f
  let : IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) D :=
    evenPolynomialDifferential_isGradedDerivation 𝒜 dA d hd f hf_grade
  have hAeven : a ∈ evenPart 𝒜 :=
    Submodule.mem_iSup_of_mem k ha
  have hEeven : E a ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d) :=
    Submodule.mem_iSup_of_mem k
      ((EvenVariableAlgebra.coeffEmbedding_mem_grade_iff 𝒜 d (2 * k) a).2 ha)
  have hTgrade : T ∈ EvenVariableAlgebra.grade 𝒜 d (i * d) :=
    EvenVariableAlgebra.monomial_one_mem_grade 𝒜 d i
  have hTpos : T ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    obtain ⟨q, hq⟩ := (Fact.out : Even d)
    have hdq : d = 2 * q := by omega
    have hiq : 0 < i * q := Nat.mul_pos hi (by omega)
    have hidx : i * d = 2 * ((i * q - 1) + 1) := by
      rw [hdq, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hiq))]
      ring
    rw [hidx] at hTgrade
    exact Submodule.mem_iSup_of_mem (i * q - 1) hTgrade
  have hTEven : T ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d) :=
    positiveEvenPart_le_evenPart _ hTpos
  have hZeq : Z = E a * T := by
    simp [Z, E, T, EvenVariableAlgebra.coeffEmbedding_apply,
      EvenVariableAlgebra.monomial_mul_monomial]
  have hpowGrade (m : ℕ) : a ^ m ∈ 𝒜 (2 * (k * m)) := by
    induction m with
    | zero => simpa using SetLike.one_mem_graded 𝒜
    | succ m ih =>
        rw [pow_succ]
        have hm := SetLike.mul_mem_graded ih ha
        simpa [Nat.mul_succ, Nat.mul_add, Nat.add_mul, mul_comm, mul_left_comm,
          mul_assoc, add_assoc, add_comm, add_left_comm] using hm
  have hEpowEven (m : ℕ) : E (a ^ m) ∈
      evenPart (EvenVariableAlgebra.grade 𝒜 d) :=
    Submodule.mem_iSup_of_mem (k * m)
      ((EvenVariableAlgebra.coeffEmbedding_mem_grade_iff 𝒜 d
        (2 * (k * m)) (a ^ m)).2 (hpowGrade m))
  have hDp (m : ℕ) : δ.dpow m Z = E (a ^ m) * δ.dpow m T := by
    by_cases hm : m = 0
    · subst m
      rw [δ.dpow_zero hz, δ.dpow_zero hTpos]
      simp only [pow_zero, map_one, one_mul]
    · rw [hZeq, δ.dpow_mul_even hm hEeven hTpos, map_pow]
  have hmulD (x y : EvenVariableAlgebra A)
      (hx : x ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d))
      (hy : y ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d)) :
      D (x * y) = D x * y + x * D y := by
    rw [differential_mul_sign (EvenVariableAlgebra.grade 𝒜 d) D,
      signRingHom_eq_self_evenPart (EvenVariableAlgebra.grade 𝒜 d) hx]
  have hTmul : T * δ.dpow (n - 1) T = n • δ.dpow n T := by
    have h := δ.dpow_mul (m := n - 1) (n := 1) hTpos
    rw [δ.dpow_one hTpos] at h
    have hidx : 1 + (n - 1) = n := by omega
    simpa [hidx, Nat.choose_one_right] using h
  have hDg : D (δ.dpow n T) = D T * δ.dpow (n - 1) T :=
    evenPolynomialDifferential_dpow_monomial_one 𝒜 γ d hd dA f n i hn hi
  have hDz : D Z = E (dA a) * T + E a * D T := by
    rw [hZeq, hmulD _ _ hEeven hTEven,
      evenPolynomialDifferential_inclusion 𝒜 dA f a]
  have hDpowA : dA (a ^ n) = n • (a ^ (n - 1) * dA a) :=
    differential_pow_even 𝒜 dA ha n
  have hcommA : dA a * a ^ (n - 1) = a ^ (n - 1) * dA a :=
    (even_element_commute 𝒜 (hpowGrade (n - 1))
      ⟨k * (n - 1), by ring⟩ (dA a)).symm
  have hcommE : E (dA a) * E (a ^ (n - 1)) =
      E (a ^ (n - 1)) * E (dA a) := by
    simpa only [map_mul] using congrArg E hcommA
  have hcommT : T * E (a ^ (n - 1)) = E (a ^ (n - 1)) * T :=
    evenPart_mul_comm (EvenVariableAlgebra.grade 𝒜 d) hTEven (E (a ^ (n - 1)))
  have hDTodd : D T ∈ oddPart (EvenVariableAlgebra.grade 𝒜 d) :=
    differential_positiveEvenPart_oddPart (EvenVariableAlgebra.grade 𝒜 d) D hTpos
  have hcommDT : D T * E (a ^ (n - 1)) = E (a ^ (n - 1)) * D T :=
    (evenPart_comm_oddPart (EvenVariableAlgebra.grade 𝒜 d)
      (hEpowEven (n - 1)) hDTodd).symm
  have hleft : D (δ.dpow n Z) =
      (n • (E (a ^ (n - 1)) * E (dA a))) * δ.dpow n T +
        E (a ^ n) * (D T * δ.dpow (n - 1) T) := by
    rw [hDp n, hmulD _ _ (hEpowEven n)
      (positiveEvenPart_le_evenPart _ (δ.dpow_mem hn hTpos)),
      evenPolynomialDifferential_inclusion, hDpowA, map_nsmul, map_mul, hDg]
  have hfirst : (E (dA a) * T) *
        (E (a ^ (n - 1)) * δ.dpow (n - 1) T) =
        (n • (E (a ^ (n - 1)) * E (dA a))) * δ.dpow n T := by
    calc
        (E (dA a) * T) *
            (E (a ^ (n - 1)) * δ.dpow (n - 1) T) =
            E (dA a) * (T * E (a ^ (n - 1))) * δ.dpow (n - 1) T := by ac_rfl
        _ = E (dA a) * (E (a ^ (n - 1)) * T) * δ.dpow (n - 1) T := by
          rw [hcommT]
        _ = (E (dA a) * E (a ^ (n - 1))) *
              (T * δ.dpow (n - 1) T) := by ac_rfl
        _ = (E (a ^ (n - 1)) * E (dA a)) *
              (T * δ.dpow (n - 1) T) := by rw [hcommE]
        _ = (E (a ^ (n - 1)) * E (dA a)) * (n • δ.dpow n T) := by rw [hTmul]
        _ = (n • (E (a ^ (n - 1)) * E (dA a))) * δ.dpow n T := by
          simp only [nsmul_eq_mul]
          let P := E (a ^ (n - 1)) * E (dA a)
          have hcomm : (n : EvenVariableAlgebra A) * P = P * n :=
            (Nat.cast_commute n P).eq
          change (E (a ^ (n - 1)) * E (dA a)) *
            (n * δ.dpow n T) = (n * (E (a ^ (n - 1)) * E (dA a))) * δ.dpow n T
          calc
            (E (a ^ (n - 1)) * E (dA a)) * (n * δ.dpow n T) =
                (P * n) * δ.dpow n T := by
              rw [← mul_assoc (E (a ^ (n - 1)) * E (dA a))
                (n : EvenVariableAlgebra A) (δ.dpow n T)]
            _ = (n * P) * δ.dpow n T := by rw [hcomm.symm]
  have hsecond : (E a * D T) * (E (a ^ (n - 1)) * δ.dpow (n - 1) T) =
        E (a ^ n) * (D T * δ.dpow (n - 1) T) := by
      calc
        (E a * D T) * (E (a ^ (n - 1)) * δ.dpow (n - 1) T) =
            E a * (D T * E (a ^ (n - 1))) * δ.dpow (n - 1) T := by ac_rfl
        _ = E a * (E (a ^ (n - 1)) * D T) * δ.dpow (n - 1) T := by
          rw [hcommDT]
        _ = (E a * E (a ^ (n - 1))) * (D T * δ.dpow (n - 1) T) := by ac_rfl
        _ = E (a ^ n) * (D T * δ.dpow (n - 1) T) := by
          rw [← map_mul]
          have hpowa : a * a ^ (n - 1) = a ^ n := by
            calc
              a * a ^ (n - 1) = a ^ ((n - 1) + 1) := (pow_succ' a (n - 1)).symm
              _ = a ^ n := by congr 1; omega
          rw [hpowa]
  have hright : D Z * δ.dpow (n - 1) Z =
      (n • (E (a ^ (n - 1)) * E (dA a))) * δ.dpow n T +
        E (a ^ n) * (D T * δ.dpow (n - 1) T) := by
    rw [hDz, hDp (n - 1), add_mul, hfirst, hsecond]
  rw [hleft, hright]

private theorem evenPolynomialDifferential_compatible_homogeneous
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1))
    (e : ℕ) (x : EvenVariableAlgebra A)
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * (e + 1))) :
    ∀ n, n ≠ 0 →
      evenPolynomialDifferential 𝒜 dA f
          ((evenVariableDividedPowerStructure d hd γ).dpow n x) =
        evenPolynomialDifferential 𝒜 dA f x *
          (evenVariableDividedPowerStructure d hd γ).dpow (n - 1) x := by
  let δ := evenVariableDividedPowerStructure d hd γ
  let D := evenPolynomialDifferential 𝒜 dA f
  let : IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) D :=
    evenPolynomialDifferential_isGradedDerivation 𝒜 dA d hd f hf_grade
  apply EvenVariableAlgebra.homogeneous_induction_on
    (𝒜 := 𝒜) (d := d) (m := 2 * (e + 1))
    (P := fun z ↦ ∀ n, n ≠ 0 →
      D (δ.dpow n z) = D z * δ.dpow (n - 1) z) hx
  · intro n hn
    have hzero : δ.dpow n (0 : EvenVariableAlgebra A) = 0 := by
      have h := δ.dpow_mul_even hn (Submodule.zero_mem _)
        (Submodule.zero_mem (positiveEvenPart
          (EvenVariableAlgebra.grade 𝒜 d)))
      simpa [hn] using h
    simp [hzero]
  · intro i a hid hagrad n hn
    have hmonoGrade : EvenVariableAlgebra.monomial i a ∈
        EvenVariableAlgebra.grade 𝒜 d (2 * (e + 1)) := by
      rw [EvenVariableAlgebra.monomial_mem_grade_iff]
      simpa [hid] using hagrad
    have hmonoPos : EvenVariableAlgebra.monomial i a ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      Submodule.mem_iSup_of_mem e hmonoGrade
    by_cases hi : i = 0
    · subst i
      have haPos : a ∈ positiveEvenPart 𝒜 :=
        Submodule.mem_iSup_of_mem e (by simpa using hagrad)
      change D (δ.dpow n (EvenVariableAlgebra.coeffEmbedding a)) = _
      calc
        D (δ.dpow n (EvenVariableAlgebra.coeffEmbedding a)) =
            EvenVariableAlgebra.coeffEmbedding
              (dA (γ.dpow n a)) := by
          rw [dpow_coeffEmbedding
            d hd γ n haPos,
            evenPolynomialDifferential_inclusion]
        _ = EvenVariableAlgebra.coeffEmbedding
              (dA a * γ.dpow (n - 1) a) := by
          rw [IsCompatibleWithDifferential.d_dpow (γ := γ) hn haPos]
        _ = D (EvenVariableAlgebra.coeffEmbedding a) *
              δ.dpow (n - 1) (EvenVariableAlgebra.coeffEmbedding a) := by
          rw [evenPolynomialDifferential_inclusion,
            dpow_coeffEmbedding
              d hd γ (n - 1) haPos]
          exact map_mul EvenVariableAlgebra.coeffEmbedding _ _
    · obtain ⟨q, hq⟩ := (Fact.out : Even d)
      have hdq : d = 2 * q := by omega
      have hprod : i * d = 2 * (i * q) := by rw [hdq]; ring
      have hidx : 2 * (e + 1) - i * d = 2 * ((e + 1) - i * q) := by
        rw [hprod]
        omega
      have ha : a ∈ 𝒜 (2 * ((e + 1) - i * q)) := by
        simpa [hidx] using hagrad
      exact evenPolynomialDifferential_dpow_monomial 𝒜 γ dA d hd f
        hf_grade ha (Nat.pos_of_ne_zero hi) hmonoPos hn
  · intro y z hy hz hpy hpz
    have hyPos : y ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      Submodule.mem_iSup_of_mem
        (p := fun m : ℕ ↦ EvenVariableAlgebra.grade 𝒜 d (2 * (m + 1))) e hy
    have hzPos : z ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      Submodule.mem_iSup_of_mem
        (p := fun m : ℕ ↦ EvenVariableAlgebra.grade 𝒜 d (2 * (m + 1))) e hz
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
        exact evenPolynomialDifferential_dpow_add
          (EvenVariableAlgebra.grade 𝒜 d) δ D y z hyPos hzPos hpy hpz n

private theorem evenPolynomialDifferential_compatible
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1)) :
    IsCompatibleWithDifferential
      (evenVariableDividedPowerStructure d hd γ)
      (evenPolynomialDifferential 𝒜 dA f) := by
  let δ := evenVariableDividedPowerStructure d hd γ
  let D := evenPolynomialDifferential 𝒜 dA f
  let : IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) D :=
    evenPolynomialDifferential_isGradedDerivation 𝒜 dA d hd f hf_grade
  constructor
  intro n x hn hx
  classical
  let P (z : EvenVariableAlgebra A) := ∀ m, m ≠ 0 →
    D (δ.dpow m z) = D z * δ.dpow (m - 1) z
  have hzero : P 0 := by
    intro m hm
    have hdp : δ.dpow m (0 : EvenVariableAlgebra A) = 0 := by
      have h := δ.dpow_mul_even hm (Submodule.zero_mem _)
        (Submodule.zero_mem (positiveEvenPart
          (EvenVariableAlgebra.grade 𝒜 d)))
      simpa [hm] using h
    simp [hdp]
  have hadd : ∀ x y : EvenVariableAlgebra A,
      x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) →
      y ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) →
      P x → P y → P (x + y) := by
    intro x y hx hy hpx hpy m hm
    cases m with
    | zero => omega
    | succ m =>
        exact evenPolynomialDifferential_dpow_add
          (EvenVariableAlgebra.grade 𝒜 d) δ D x y hx hy hpx hpy m
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun e : ℕ ↦ EvenVariableAlgebra.grade 𝒜 d (2 * (e + 1))) x).mp hx
  have hsumP : P (∑ e ∈ g.support, (g e : EvenVariableAlgebra A)) := by
    have h := Finset.sum_induction (s := g.support)
      (fun e ↦ (g e : EvenVariableAlgebra A))
      (fun z ↦ z ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) ∧ P z)
      (fun z w hz hw ↦ ⟨Submodule.add_mem _ hz.1 hw.1, hadd z w hz.1 hw.1 hz.2 hw.2⟩)
      ⟨Submodule.zero_mem _, hzero⟩
      (fun e he ↦ ⟨Submodule.mem_iSup_of_mem e (hg e),
        evenPolynomialDifferential_compatible_homogeneous
          𝒜 γ dA d hd f hf_grade e (g e) (hg e)⟩)
    exact h.2
  have hrepr : x = ∑ e ∈ g.support, (g e : EvenVariableAlgebra A) := by
    rw [← hgsum, Finsupp.sum]
  rw [hrepr]
  exact hsumP n hn

private theorem evenPolynomialDifferential_unique
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (f : A)
    (dExt : EvenVariableAlgebra A →ₗ[R] EvenVariableAlgebra A)
    [IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) dExt]
    [IsCompatibleWithDifferential
      (evenVariableDividedPowerStructure d hd γ) dExt]
    (hbase : ∀ a, dExt (EvenVariableAlgebra.coeffEmbedding a) =
      EvenVariableAlgebra.coeffEmbedding (dA a))
    (hgen : dExt (EvenVariableAlgebra.monomial 1 1) =
      EvenVariableAlgebra.coeffEmbedding f) :
    dExt = evenPolynomialDifferential 𝒜 dA f := by
  classical
  let δ := evenVariableDividedPowerStructure d hd γ
  have hTpos : EvenVariableAlgebra.monomial 1 (1 : A) ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    obtain ⟨q, hq⟩ := (Fact.out : Even d)
    have hqd : d = 2 * q := by omega
    have hqpos : 0 < q := by rw [hqd] at hd; omega
    have hTgrade : EvenVariableAlgebra.monomial 1 (1 : A) ∈
        EvenVariableAlgebra.grade 𝒜 d (2 * q) := by
      rw [hqd]
      simpa using EvenVariableAlgebra.monomial_one_mem_grade 𝒜 d 1
    have hidx : 2 * q = 2 * ((q - 1) + 1) := by omega
    rw [hidx] at hTgrade
    exact Submodule.mem_iSup_of_mem (q - 1) hTgrade
  have hpowT (n : ℕ) : dExt (EvenVariableAlgebra.monomial n (1 : A)) =
      if n = 0 then 0 else EvenVariableAlgebra.monomial (n - 1) f := by
    by_cases hn : n = 0
    · subst n
      have hd1 : dExt (1 : EvenVariableAlgebra A) = 0 :=
        IsGradedDerivation.d_grade_zero
          (𝒜 := EvenVariableAlgebra.grade 𝒜 d) (d := dExt)
          (SetLike.one_mem_graded (EvenVariableAlgebra.grade 𝒜 d))
      exact hd1
    · have hdp : δ.dpow n (EvenVariableAlgebra.monomial 1 (1 : A)) =
        EvenVariableAlgebra.monomial n (1 : A) := by
        rw [dpow_monomial_one d hd γ n 1
          (by omega : 0 < 1)]
        have hc : dividedPowerMonomialCoefficient n 1 = 1 := by
          simpa [dividedPowerMonomialCoefficient,
            Nat.mul_one] using
              Nat.div_self (Nat.factorial_pos n)
        rw [hc]
        simp
      rw [ite_eq_right hn]
      rw [← hdp, IsCompatibleWithDifferential.d_dpow (γ := δ) hn hTpos,
        hgen]
      have hdp' : δ.dpow (n - 1) (EvenVariableAlgebra.monomial 1 (1 : A)) =
          EvenVariableAlgebra.monomial (n - 1) (1 : A) := by
        by_cases hsub : n - 1 = 0
        · rw [hsub, δ.dpow_zero hTpos]
          rfl
        · rw [dpow_monomial_one d hd γ
            (n - 1) 1 (by omega : 0 < 1)]
          have hc : dividedPowerMonomialCoefficient (n - 1) 1 = 1 := by
            simpa [dividedPowerMonomialCoefficient,
              Nat.mul_one] using
                Nat.div_self (Nat.factorial_pos (n - 1))
          rw [hc]
          simp
      rw [hdp']
      simp [EvenVariableAlgebra.coeffEmbedding_apply,
        EvenVariableAlgebra.monomial_mul_monomial]
  have hmono (n : ℕ) (a : A) :
      dExt (EvenVariableAlgebra.monomial n a) =
        evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial n a) := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous k a =>
        have hgrade : EvenVariableAlgebra.coeffEmbedding (a : A) ∈
            EvenVariableAlgebra.grade 𝒜 d k :=
          (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff 𝒜 d k (a : A)).2 a.property
        have htgrade : EvenVariableAlgebra.monomial n (1 : A) ∈
            EvenVariableAlgebra.grade 𝒜 d (n * d) :=
          EvenVariableAlgebra.monomial_one_mem_grade 𝒜 d n
        have hprod : EvenVariableAlgebra.coeffEmbedding (a : A) *
            EvenVariableAlgebra.monomial n (1 : A) =
            EvenVariableAlgebra.monomial n (a : A) := by
          simp [EvenVariableAlgebra.coeffEmbedding_apply,
            EvenVariableAlgebra.monomial_mul_monomial]
        rw [← hprod]
        rw [IsGradedDerivation.leibniz
          (𝒜 := EvenVariableAlgebra.grade 𝒜 d) (d := dExt) hgrade htgrade,
          hbase, hpowT]
        conv_rhs => rw [hprod, evenPolynomialDifferential_monomial]
        simp [EvenVariableAlgebra.coeffEmbedding_apply,
          EvenVariableAlgebra.monomial_mul_monomial,
          signRingHom_of_mem 𝒜 1 k a.property]
    | add a b ha hb =>
        simp only [map_add, EvenVariableAlgebra.monomial_add, ha, hb]
  apply LinearMap.ext
  intro x
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add n a x hx =>
      simp only [map_add, hx, hmono]

/-- A closed element of degree `d - 1` determines the unique divided-power-compatible
differential after adjoining an odd variable of degree `d`. -/
@[stacks 09PM "odd variable"]
public theorem existsUnique_differential_oddVariableExtension
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) (hd : 0 < d) (hd_odd : Odd d)
    (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) (hf_cycle : dA f = 0) :
    ∃! dExt : OddVariableExtension 𝒜 d →ₗ[R] OddVariableExtension 𝒜 d,
      (IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 d) dExt ∧
        (∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 d x) =
          OddVariableExtension.inclusion 𝒜 d (dA x)) ∧
        dExt (OddVariableExtension.generator 𝒜 d) =
          OddVariableExtension.inclusion 𝒜 d f ∧
        IsCompatibleWithDifferential
          (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd) dExt) := by
  classical
  let dExt := oddExtensionDifferential 𝒜 dA d f
  let : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 d) dExt :=
    oddExtensionDifferential_isDGA 𝒜 dA d hd hd_odd f hf_grade hf_cycle
  refine ⟨dExt, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact inferInstance
    · intro x
      exact oddExtensionDifferential_inclusion 𝒜 dA d f x
    · exact oddExtensionDifferential_generator 𝒜 dA d f
    · exact oddExtensionDifferential_compatible 𝒜 γ dA d hd hd_odd f
        hf_grade
  · intro dExt' h'
    let : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 d) dExt' := h'.1
    exact oddExtensionDifferential_unique 𝒜 dA d hd_odd f dExt'
      h'.2.1 h'.2.2.1

/-- A closed element of degree `d - 1` determines the unique divided-power-compatible
differential after adjoining an even divided-power variable of degree `d`. -/
@[stacks 09PM "even variable"]
public theorem existsUnique_differential_evenVariableAlgebra
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) (hf_cycle : dA f = 0) :
    ∃! dExt : EvenVariableAlgebra A →ₗ[R] EvenVariableAlgebra A,
      (IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 d) dExt ∧
        (∀ x : A, dExt (EvenVariableAlgebra.coeffEmbedding x) =
          EvenVariableAlgebra.coeffEmbedding (dA x)) ∧
        dExt (EvenVariableAlgebra.monomial 1 1) =
          EvenVariableAlgebra.coeffEmbedding f ∧
        IsCompatibleWithDifferential
          (evenVariableDividedPowerStructure d hd γ) dExt) := by
  classical
  let dExt := evenPolynomialDifferential 𝒜 dA f
  let : IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 d) dExt :=
    evenPolynomialDifferential_isDGA 𝒜 dA d hd f hf_grade hf_cycle
  let : IsCompatibleWithDifferential
      (evenVariableDividedPowerStructure d hd γ) dExt :=
    evenPolynomialDifferential_compatible 𝒜 γ dA d hd f hf_grade
  refine ⟨dExt, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact inferInstance
    · intro x
      exact evenPolynomialDifferential_inclusion 𝒜 dA f x
    · exact evenPolynomialDifferential_generator 𝒜 dA f
    · exact inferInstance
  · intro dExt' h'
    let : IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 d) dExt' := h'.1
    let : IsCompatibleWithDifferential
        (evenVariableDividedPowerStructure d hd γ) dExt' := h'.2.2.2
    exact evenPolynomialDifferential_unique 𝒜 γ dA d hd f dExt'
      h'.2.1 h'.2.2.1

/-- The odd-variable extension of a graded derivation is a graded derivation. Unlike
`oddExtensionDifferential_isDGA` this needs no cycle hypothesis on `f`. -/
private theorem oddExtensionDifferential_isGradedDerivation
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) :
    IsGradedDerivation (OddVariableExtension.grade 𝒜 d)
      (oddExtensionDifferential 𝒜 dA d f) where
  d_grade_zero hx := oddExtensionDifferential_grade_zero 𝒜 dA d hd f hx
  d_mem hx := oddExtensionDifferential_mem 𝒜 dA d hd f hf_grade hx
  leibniz hx hy := oddExtensionDifferential_leibniz 𝒜 dA d hd_odd f hf_grade hx hy

/-- An element of degree `d - 1`, with no cycle condition imposed on it, determines the unique
divided-power-compatible graded derivation on the algebra obtained by adjoining an odd variable of
degree `d`. The extension is square-zero precisely when the prescribed value is a cycle, which is
`existsUnique_differential_oddVariableExtension`; this form is what the square-zero lift of
Tag 09PS needs, since there the lifted operator is not square-zero. -/
@[stacks 09PM "odd variable, as a graded derivation"]
public theorem existsUnique_gradedDerivation_oddVariableExtension
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) (hd : 0 < d) (hd_odd : Odd d)
    (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) :
    ∃! dExt : OddVariableExtension 𝒜 d →ₗ[R] OddVariableExtension 𝒜 d,
      (IsGradedDerivation (OddVariableExtension.grade 𝒜 d) dExt ∧
        (∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 d x) =
          OddVariableExtension.inclusion 𝒜 d (dA x)) ∧
        dExt (OddVariableExtension.generator 𝒜 d) =
          OddVariableExtension.inclusion 𝒜 d f ∧
        IsCompatibleWithDifferential
          (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd) dExt) := by
  classical
  let dExt := oddExtensionDifferential 𝒜 dA d f
  let : IsGradedDerivation (OddVariableExtension.grade 𝒜 d) dExt :=
    oddExtensionDifferential_isGradedDerivation 𝒜 dA d hd hd_odd f hf_grade
  refine ⟨dExt, ⟨inferInstance, fun x => oddExtensionDifferential_inclusion 𝒜 dA d f x,
    oddExtensionDifferential_generator 𝒜 dA d f,
    oddExtensionDifferential_compatible 𝒜 γ dA d hd hd_odd f hf_grade⟩, ?_⟩
  intro dExt' h'
  let : IsGradedDerivation (OddVariableExtension.grade 𝒜 d) dExt' := h'.1
  exact oddExtensionDifferential_unique 𝒜 dA d hd_odd f dExt' h'.2.1 h'.2.2.1

/-- An element of degree `d - 1`, with no cycle condition imposed on it, determines the unique
divided-power-compatible graded derivation on the algebra obtained by adjoining an even
divided-power variable of degree `d`. The extension is square-zero precisely when the prescribed
value is a cycle, which is `existsUnique_differential_evenVariableAlgebra`. -/
@[stacks 09PM "even variable, as a graded derivation"]
public theorem existsUnique_gradedDerivation_evenVariableAlgebra
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (f : A) (hf_grade : f ∈ 𝒜 (d - 1)) :
    ∃! dExt : EvenVariableAlgebra A →ₗ[R] EvenVariableAlgebra A,
      (IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) dExt ∧
        (∀ x : A, dExt (EvenVariableAlgebra.coeffEmbedding x) =
          EvenVariableAlgebra.coeffEmbedding (dA x)) ∧
        dExt (EvenVariableAlgebra.monomial 1 1) =
          EvenVariableAlgebra.coeffEmbedding f ∧
        IsCompatibleWithDifferential
          (evenVariableDividedPowerStructure d hd γ) dExt) := by
  classical
  let dExt := evenPolynomialDifferential 𝒜 dA f
  let : IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) dExt :=
    evenPolynomialDifferential_isGradedDerivation 𝒜 dA d hd f hf_grade
  let : IsCompatibleWithDifferential (evenVariableDividedPowerStructure d hd γ) dExt :=
    evenPolynomialDifferential_compatible 𝒜 γ dA d hd f hf_grade
  refine ⟨dExt, ⟨inferInstance, fun x => evenPolynomialDifferential_inclusion 𝒜 dA f x,
    evenPolynomialDifferential_generator 𝒜 dA f, inferInstance⟩, ?_⟩
  intro dExt' h'
  let : IsGradedDerivation (EvenVariableAlgebra.grade 𝒜 d) dExt' := h'.1
  let : IsCompatibleWithDifferential
      (evenVariableDividedPowerStructure d hd γ) dExt' := h'.2.2.2
  exact evenPolynomialDifferential_unique 𝒜 γ dA d hd f dExt' h'.2.1 h'.2.2.1

end DividedPowers.TateResolution
