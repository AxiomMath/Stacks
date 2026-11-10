module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.CoefficientRestriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PolynomialDifferential

/-!
# Lifting a differential across a surjection of coefficient rings

Let `q : R' → R` be a surjection of commutative rings, let `A` be a strictly graded-commutative
graded `R`-algebra with divided powers `γ` and a differential `d` compatible with them, presented
as a graded divided-power polynomial algebra over `MvPolynomial σ R`, and let `B` be a graded
divided-power polynomial algebra over `MvPolynomial σ R'` on the same variables, surjecting onto
`A` by a map `π` which reduces the coefficients along `q` and preserves the grading and the
divided powers.

This file produces a differential `D` on `B` which lifts `d`: it obeys the signed Leibniz rule
and the divided-power Leibniz rule, and `π (D b) = d (π b)` **for every** `b`, not only on the
variables.

## Main results

* `DividedPowers.TateResolution.exists_oddExtAlgHom_of_differential` — a differential on a graded
  divided-power algebra is the same thing as a grading- and divided-power-preserving algebra map
  into the odd-variable extension by one variable of degree one.
* `DividedPowers.TateResolution.exists_oddExtMap` — the odd-variable extension by one variable of
  degree one is functorial in grading- and divided-power-preserving algebra maps.
* `DividedPowers.TateResolution.exists_preimage_mem_grade` — a surjective grading-preserving map
  of graded modules is surjective in each degree.
* `DividedPowers.TateResolution.exists_differential_lift_gradedDividedPowerPolynomial` — the
  lifted differential, with `π ∘ D = d ∘ π`.

## Implementation notes

The identity `π ∘ D = d ∘ π` is a uniqueness statement, not a substitution. Prescribing the
values of `D` on the variables as `π`-preimages of the values of `d` on the variables gives the
identity *on the variables only*; extending it to all of `B` is done by comparing two algebra maps
out of `B`.

The comparison takes place in `W`, the odd-variable extension of `A` by one variable of degree
one, formed over `R'` — the scalars of `A` restricted along `q`, which is what
`DividedPowers.TateResolution.coefficientRestrictGrade` supplies. The two maps `B → W` are

* `ρ ∘ Φ_B`, where `Φ_B : B → B⟨T⟩` is the algebra map `b ↦ b + σ(D b) T` attached to `D` and `ρ`
  is the functoriality of the odd-variable extension applied to `π`;
* `Φ_A ∘ π`, where `Φ_A : A → W` is the algebra map `a ↦ a + σ(d a) T` attached to `d`.

Both are grading- and divided-power-preserving `R'`-algebra maps, and they agree on the
coefficients (because `D` and `d` both vanish in degree zero) and on the variables (by the choice
of the prescribed values). The uniqueness half of
`DividedPowers.TateResolution.existsUnique_gradedDividedPowerPolynomial_map` therefore makes them
equal, and the second coefficient of that equality is `σ (π (D b)) = σ (d (π b))`.

Prescribing the values of `D` on the variables needs *homogeneous* `π`-preimages, which is why
degreewise surjectivity of `π` is proved first: it follows from plain surjectivity by comparing
the homogeneous decompositions of `b` and of `π b`.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w x y

attribute [local implicit_reducible] TwistedModule

section Pair

variable {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The element `a + bT` of the odd-variable extension by one variable of degree one. -/
public noncomputable def oddExtPair (a b : A) : OddVariableExtension 𝒜 1 :=
  OddVariableExtension.inclusion 𝒜 1 a +
    OddVariableExtension.inclusion 𝒜 1 b * OddVariableExtension.generator 𝒜 1

/-- The coefficients of `a + bT` are `(a, b)`. -/
@[simp]
public theorem coefficients_oddExtPair (a b : A) :
    OddVariableExtension.coefficients 𝒜 1 (oddExtPair 𝒜 a b) = (a, b) :=
  coefficients_inclusion_add_mul_generator 𝒜 a b

/-- Every element of the degree-one odd-variable extension is `a + bT`. -/
public theorem oddExtPair_coefficients (z : OddVariableExtension 𝒜 1) :
    oddExtPair 𝒜 (OddVariableExtension.coefficients 𝒜 1 z).1
        (OddVariableExtension.coefficients 𝒜 1 z).2 = z :=
  inclusion_add_mul_generator_coefficients 𝒜 z

/-- `a + bT` is homogeneous of degree `n + 1` when `a` has degree `n + 1` and `b` has degree
`n`. -/
public theorem oddExtPair_mem_grade_succ {n : ℕ} {a b : A} (ha : a ∈ 𝒜 (n + 1))
    (hb : b ∈ 𝒜 n) : oddExtPair 𝒜 a b ∈ OddVariableExtension.grade 𝒜 1 (n + 1) := by
  rw [OddVariableExtension.mem_grade_coefficients_iff, coefficients_oddExtPair]
  refine ⟨ha, ?_⟩
  rw [ite_eq_left (by omega : (1 : ℕ) ≤ n + 1), Nat.add_sub_cancel]
  exact hb

/-- `a` is homogeneous of degree zero in the extension when it is in `A`. -/
public theorem oddExtPair_mem_grade_zero {a : A} (ha : a ∈ 𝒜 0) :
    oddExtPair 𝒜 a 0 ∈ OddVariableExtension.grade 𝒜 1 0 := by
  rw [OddVariableExtension.mem_grade_coefficients_iff, coefficients_oddExtPair]
  refine ⟨ha, ?_⟩
  rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0)]
  exact Submodule.zero_mem _

/-- `a + 0 T` is the image of `a` under the inclusion. -/
private theorem oddExtPair_zero_right (a : A) :
    oddExtPair 𝒜 a 0 = OddVariableExtension.inclusion 𝒜 1 a := by
  unfold oddExtPair
  rw [map_zero, zero_mul, add_zero]

/-- The grading sign is an involution. -/
public theorem signRingEquiv_signRingEquiv (d : ℕ) (a : A) :
    signRingEquiv 𝒜 d (signRingEquiv 𝒜 d a) = a :=
  signRingHom_involutive 𝒜 d a

/-- The grading sign preserves each homogeneous piece. -/
public theorem signRingEquiv_mem_grade (d : ℕ) {m : ℕ} {a : A} (ha : a ∈ 𝒜 m) :
    signRingEquiv 𝒜 d a ∈ 𝒜 m := by
  rw [signRingEquiv_of_mem 𝒜 d m ha]
  exact (𝒜 m).smul_mem _ ha

end Pair

section OfDifferential

variable {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜) (D : A →ₗ[R] A)

omit [IsStrictlyGradedComm 𝒜] in
/-- The signed Leibniz rule for homogeneous elements implies the untwisted form
`D (x y) = σ(x) D(y) + D(x) y` for arbitrary elements. -/
public theorem map_mul_of_leibniz
    (hD : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) (x y : A) :
    D (x * y) = signRingEquiv 𝒜 1 x * D y + D x * y := by
  classical
  have key : ∀ (i : ℕ) (x : A), x ∈ 𝒜 i → ∀ y : A,
      D (x * y) = signRingEquiv 𝒜 1 x * D y + D x * y := by
    intro i x hx y
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j y =>
        rw [hD i j x (y : A) hx y.property, signRingEquiv_of_mem 𝒜 1 i hx, one_mul,
          smul_mul_assoc, add_comm]
    | add y z hy hz =>
        simp only [mul_add, map_add, hy, hz]
        abel
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x => exact key i (x : A) x.property y
  | add x z hx hz =>
      simp only [add_mul, map_add, hx, hz]
      abel

/-- **A differential is an algebra map into the odd-variable extension.** A degree-lowering
`R`-linear map obeying the signed Leibniz rule and the divided-power Leibniz rule is the same
thing as a grading- and divided-power-preserving algebra map `a ↦ a + σ(D a) T` into the
odd-variable extension by one variable of degree one. -/
public theorem exists_oddExtAlgHom_of_differential
    (hD0 : ∀ a : A, a ∈ 𝒜 0 → D a = 0)
    (hDgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n + 1) → D a ∈ 𝒜 n)
    (hDleibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y))
    (hDdpow : ∀ (n : ℕ) (a : A), n ≠ 0 → a ∈ positiveEvenPart 𝒜 →
      D (γ.dpow n a) = D a * γ.dpow (n - 1) a) :
    ∃ Φ : A →ₐ[R] OddVariableExtension 𝒜 1,
      (∀ a : A, Φ a = oddExtPair 𝒜 a (signRingEquiv 𝒜 1 (D a))) ∧
      (∀ (n : ℕ) (a : A), a ∈ 𝒜 n → Φ a ∈ OddVariableExtension.grade 𝒜 1 n) ∧
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
        Φ (γ.dpow n a) =
          (oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow n (Φ a)) := by
  classical
  have hσinv : ∀ a : A, signRingEquiv 𝒜 1 (signRingEquiv 𝒜 1 a) = a :=
    signRingEquiv_signRingEquiv 𝒜 1
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A →ₐ[R] OddVariableExtension 𝒜 1,
      ∀ a : A, Φ a = oddExtPair 𝒜 a (signRingEquiv 𝒜 1 (D a)) := by
    refine ⟨{ toFun := fun a => oddExtPair 𝒜 a (signRingEquiv 𝒜 1 (D a))
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_
              commutes' := ?_ }, fun _ => rfl⟩
    · change oddExtPair 𝒜 1 (signRingEquiv 𝒜 1 (D 1)) = 1
      rw [hD0 1 (SetLike.one_mem_graded 𝒜), map_zero, oddExtPair_zero_right, map_one]
    · intro x y
      change oddExtPair 𝒜 (x * y) (signRingEquiv 𝒜 1 (D (x * y))) =
        oddExtPair 𝒜 x (signRingEquiv 𝒜 1 (D x)) * oddExtPair 𝒜 y (signRingEquiv 𝒜 1 (D y))
      refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      rw [OddVariableExtension.coefficients_mul, coefficients_oddExtPair,
        coefficients_oddExtPair, coefficients_oddExtPair]
      refine Prod.ext rfl ?_
      change signRingEquiv 𝒜 1 (D (x * y)) =
        x * signRingEquiv 𝒜 1 (D y) + signRingEquiv 𝒜 1 (D x) * signRingEquiv 𝒜 1 y
      rw [map_mul_of_leibniz 𝒜 D hDleibniz x y, map_add, map_mul, map_mul, hσinv]
    · change oddExtPair 𝒜 0 (signRingEquiv 𝒜 1 (D 0)) = 0
      rw [map_zero, map_zero, oddExtPair_zero_right, map_zero]
    · intro x y
      change oddExtPair 𝒜 (x + y) (signRingEquiv 𝒜 1 (D (x + y))) =
        oddExtPair 𝒜 x (signRingEquiv 𝒜 1 (D x)) + oddExtPair 𝒜 y (signRingEquiv 𝒜 1 (D y))
      refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      simp only [map_add, coefficients_oddExtPair, Prod.mk_add_mk]
    · intro r
      rw [hD0 _ (SetLike.algebraMap_mem_graded 𝒜 r), map_zero, oddExtPair_zero_right]
      rfl
  have hgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → Φ a ∈ OddVariableExtension.grade 𝒜 1 n := by
    intro n a ha
    rw [hΦ a]
    match n with
    | 0 =>
        rw [hD0 a ha, map_zero]
        exact oddExtPair_mem_grade_zero 𝒜 ha
    | m + 1 =>
        exact oddExtPair_mem_grade_succ 𝒜 ha
          (signRingEquiv_mem_grade 𝒜 1 (hDgrade m a ha))
  refine ⟨Φ, hΦ, hgrade, ?_⟩
  intro n a ha
  have hΦa : Φ a ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1) :=
    algHom_mem_positiveEvenPart 𝒜 (OddVariableExtension.grade 𝒜 1) Φ hgrade ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [γ.dpow_zero ha,
      (oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow_zero hΦa, map_one]
  have heven : γ.dpow (n - 1) a ∈ evenPart 𝒜 := by
    rcases Nat.eq_zero_or_pos (n - 1) with hz | hp
    · rw [hz, γ.dpow_zero ha]
      exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
    · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem (by omega) ha)
  refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
  rw [coefficients_dpow 𝒜 γ n hn.ne' hΦa, hΦ (γ.dpow n a), hΦ a, coefficients_oddExtPair,
    coefficients_oddExtPair]
  refine Prod.ext rfl ?_
  change signRingEquiv 𝒜 1 (D (γ.dpow n a)) = γ.dpow (n - 1) a * signRingEquiv 𝒜 1 (D a)
  rw [hDdpow n a hn.ne' ha, map_mul, signRingEquiv_one_of_mem_evenPart 𝒜 heven,
    mul_comm_of_mem_evenPart 𝒜 heven]

end OfDifferential

section Functoriality

variable {R : Type u} {A : Type w} {B : Type x}
  [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  (γ : DividedPowerStructure 𝒜) (δ : DividedPowerStructure ℬ)
  (φ : B →ₐ[R] A)

omit [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ] in
/-- A grading-preserving algebra map commutes with the grading sign. -/
public theorem map_signRingEquiv (hφ : ∀ (n : ℕ) (b : B), b ∈ ℬ n → φ b ∈ 𝒜 n) (d : ℕ) (b : B) :
    φ (signRingEquiv ℬ d b) = signRingEquiv 𝒜 d (φ b) := by
  classical
  induction b using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous m b =>
      rw [signRingEquiv_of_mem ℬ d m b.property, map_smul,
        signRingEquiv_of_mem 𝒜 d m (hφ m (b : B) b.property)]
  | add b c hb hc => simp only [map_add, hb, hc]

/-- **Functoriality of the degree-one odd-variable extension.** A grading- and
divided-power-preserving algebra map `φ : B → A` induces one `B⟨T⟩ → A⟨T⟩` acting on both
coefficients, again preserving the grading and the divided powers. -/
public theorem exists_oddExtMap
    (hφgrade : ∀ (n : ℕ) (b : B), b ∈ ℬ n → φ b ∈ 𝒜 n)
    (hφdpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ → φ (δ.dpow n b) = γ.dpow n (φ b)) :
    ∃ ρ : OddVariableExtension ℬ 1 →ₐ[R] OddVariableExtension 𝒜 1,
      (∀ b c : B, ρ (oddExtPair ℬ b c) = oddExtPair 𝒜 (φ b) (φ c)) ∧
      (∀ (n : ℕ) (z : OddVariableExtension ℬ 1), z ∈ OddVariableExtension.grade ℬ 1 n →
        ρ z ∈ OddVariableExtension.grade 𝒜 1 n) ∧
      (∀ (n : ℕ) (z : OddVariableExtension ℬ 1),
        z ∈ positiveEvenPart (OddVariableExtension.grade ℬ 1) →
        ρ ((oddVariableDividedPowerStructure ℬ δ 1 Nat.one_pos odd_one).dpow n z) =
          (oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow n (ρ z)) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : OddVariableExtension ℬ 1 → OddVariableExtension 𝒜 1, ∀ z,
      OddVariableExtension.coefficients 𝒜 1 (f z) =
        (φ (OddVariableExtension.coefficients ℬ 1 z).1,
          φ (OddVariableExtension.coefficients ℬ 1 z).2) :=
    ⟨fun z => oddExtPair 𝒜 _ _, fun _ => coefficients_oddExtPair 𝒜 _ _⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OddVariableExtension ℬ 1 →ₐ[R] OddVariableExtension 𝒜 1,
      ∀ z : OddVariableExtension ℬ 1, ρ z =
        oddExtPair 𝒜 (φ (OddVariableExtension.coefficients ℬ 1 z).1)
          (φ (OddVariableExtension.coefficients ℬ 1 z).2) := by
    have hf' : ∀ z, f z = oddExtPair 𝒜 (φ (OddVariableExtension.coefficients ℬ 1 z).1)
        (φ (OddVariableExtension.coefficients ℬ 1 z).2) := fun z =>
      (OddVariableExtension.coefficients 𝒜 1).injective (by rw [hf, coefficients_oddExtPair])
    refine ⟨{ toFun := f
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_
              commutes' := ?_ }, hf'⟩
    · refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      change OddVariableExtension.coefficients 𝒜 1 (f 1) = _
      rw [hf]
      exact Prod.ext (map_one φ) (map_zero φ)
    · intro z w
      refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      change OddVariableExtension.coefficients 𝒜 1 (f (z * w)) = _
      rw [hf, OddVariableExtension.coefficients_mul]
      simp [hf, map_signRingEquiv 𝒜 ℬ φ hφgrade]
    · refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      change OddVariableExtension.coefficients 𝒜 1 (f 0) = _
      rw [hf]
      simp
    · intro z w
      refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      change OddVariableExtension.coefficients 𝒜 1 (f (z + w)) = _
      simp [hf]
    · intro r
      refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
      change OddVariableExtension.coefficients 𝒜 1 (f (algebraMap R _ r)) = _
      rw [hf]
      exact Prod.ext (φ.commutes r) (map_zero φ)
  have hpair : ∀ b c : B, ρ (oddExtPair ℬ b c) = oddExtPair 𝒜 (φ b) (φ c) := by
    intro b c
    rw [hρ, coefficients_oddExtPair]
  have hgrade : ∀ (n : ℕ) (z : OddVariableExtension ℬ 1), z ∈ OddVariableExtension.grade ℬ 1 n →
      ρ z ∈ OddVariableExtension.grade 𝒜 1 n := by
    intro n z hz
    obtain ⟨hz1, hz2⟩ := (OddVariableExtension.mem_grade_coefficients_iff ℬ 1 n z).mp hz
    rw [hρ z, OddVariableExtension.mem_grade_coefficients_iff, coefficients_oddExtPair]
    refine ⟨hφgrade n _ hz1, ?_⟩
    match n with
    | 0 =>
        rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0)] at hz2 ⊢
        rw [Submodule.mem_bot] at hz2 ⊢
        rw [hz2, map_zero]
    | m + 1 =>
        rw [ite_eq_left (by omega : (1 : ℕ) ≤ m + 1), Nat.add_sub_cancel] at hz2 ⊢
        exact hφgrade m _ hz2
  refine ⟨ρ, hpair, hgrade, ?_⟩
  intro n z hz
  have hρz : ρ z ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1) :=
    algHom_mem_positiveEvenPart (OddVariableExtension.grade ℬ 1)
      (OddVariableExtension.grade 𝒜 1) ρ hgrade hz
  obtain ⟨hz1, -⟩ := mem_positiveEvenPart_oddExt ℬ hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(oddVariableDividedPowerStructure ℬ δ 1 Nat.one_pos odd_one).dpow_zero hz,
      (oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow_zero hρz, map_one]
  refine (OddVariableExtension.coefficients 𝒜 1).injective ?_
  rw [coefficients_dpow 𝒜 γ n hn.ne' hρz, hρ z, coefficients_oddExtPair,
    hρ ((oddVariableDividedPowerStructure ℬ δ 1 Nat.one_pos odd_one).dpow n z),
    coefficients_oddExtPair, coefficients_dpow ℬ δ n hn.ne' hz]
  exact Prod.ext (hφdpow n _ hz1)
    (by rw [map_mul, hφdpow (n - 1) _ hz1])

end Functoriality

section GradedSurjective

variable {R : Type u} {R' : Type v} {A : Type w} {B : Type x}
  [CommRing R] [CommRing R'] [Ring A] [Algebra R A] [Ring B] [Algebra R' B]

/-- **A surjective grading-preserving map is surjective in each degree.** -/
public theorem exists_preimage_mem_grade
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ]
    (φ : B →+ A) (hφ : ∀ (n : ℕ) (b : B), b ∈ ℬ n → φ b ∈ 𝒜 n)
    (hsurj : Function.Surjective φ) (n : ℕ) {a : A} (ha : a ∈ 𝒜 n) :
    ∃ b : B, b ∈ ℬ n ∧ φ b = a := by
  classical
  have key : ∀ b : B, ((DirectSum.decompose 𝒜 (φ b) n : 𝒜 n) : A) =
      φ ((DirectSum.decompose ℬ b n : ℬ n) : B) := by
    intro b
    induction b using DirectSum.Decomposition.inductionOn ℬ with
    | zero => simp
    | @homogeneous m b =>
        by_cases hmn : m = n
        · subst hmn
          rw [DirectSum.decompose_of_mem_same ℬ b.property,
            DirectSum.decompose_of_mem_same 𝒜 (hφ m (b : B) b.property)]
        · rw [DirectSum.decompose_of_mem_ne ℬ b.property hmn,
            DirectSum.decompose_of_mem_ne 𝒜 (hφ m (b : B) b.property) hmn, map_zero]
    | add b c hb hc =>
        rw [map_add, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
          DirectSum.add_apply, Submodule.coe_add, Submodule.coe_add, hb, hc, map_add]
  obtain ⟨b, hb⟩ := hsurj a
  refine ⟨(DirectSum.decompose ℬ b n : ℬ n), (DirectSum.decompose ℬ b n).property, ?_⟩
  rw [← key b, hb, DirectSum.decompose_of_mem_same 𝒜 ha]

end GradedSurjective

section Lift

variable {R' : Type u} {R : Type v} {A : Type w} {B : Type x} {σ : Type y}
  [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R' B]

/-- **The lifted differential.** Let `q : R' → R` be a ring map, let `A` be a strictly
graded-commutative graded `R`-algebra with divided powers `γ` and a compatible differential `d`,
presented as a graded divided-power polynomial algebra over `MvPolynomial σ R`, and let `B` be a
graded divided-power polynomial algebra over `MvPolynomial σ R'` on the same variables, surjecting
onto `A` by `π` compatibly with the coefficients, the variables, the grading and the divided
powers. Then `B` carries a differential `D` lifting `d`: `π (D b) = d (π b)` for every `b`. -/
public theorem exists_differential_lift_gradedDividedPowerPolynomial
    (q : R' →+* R)
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d] [IsCompatibleWithDifferential γ d]
    (ι : MvPolynomial σ R →ₐ[R] A) (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
    (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (δ : DividedPowerStructure ℬ) (ι' : MvPolynomial σ R' →ₐ[R'] B)
    (hpolyB : GradedDividedPowerPolynomial ℬ δ ι')
    (e : ∀ n : ℕ, hpoly.indices n ≃ hpolyB.indices n)
    (π : B →+* A)
    (hπsurj : Function.Surjective π)
    (hπalg : ∀ r' : R', π (algebraMap R' B r') = algebraMap R A (q r'))
    (hπcoeff : ∀ p' : MvPolynomial σ R', π (ι' p') = ι (MvPolynomial.map q p'))
    (hπgen : ∀ (n : ℕ) (j : hpoly.indices n),
      π (hpolyB.generator ⟨n, e n j⟩) = hpoly.generator ⟨n, j⟩)
    (hπgrade : ∀ (n : ℕ) (b : B), b ∈ ℬ n → π b ∈ 𝒜 n)
    (hπdpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ →
      π (δ.dpow n b) = γ.dpow n (π b)) :
    ∃ D : B →ₗ[R'] B,
      (∀ b : B, b ∈ ℬ 0 → D b = 0) ∧
      (∀ (n : ℕ) (b : B), b ∈ ℬ (n + 1) → D b ∈ ℬ n) ∧
      (∀ (i j : ℕ) (b c : B), b ∈ ℬ i → c ∈ ℬ j →
        D (b * c) = D b * c + (-1 : R') ^ i • (b * D c)) ∧
      (∀ (n : ℕ) (b : B), n ≠ 0 → b ∈ positiveEvenPart ℬ →
        D (δ.dpow n b) = D b * δ.dpow (n - 1) b) ∧
      (∀ b : B, π (D b) = d (π b)) := by
  classical
  -- the variables of `B`, matched with those of `A`
  have hgenπ : ∀ j : Σ n : ℕ, hpolyB.indices n,
      π (hpolyB.generator j) = hpoly.generator ⟨j.1, (e j.1).symm j.2⟩ := by
    intro j
    have h := hπgen j.1 ((e j.1).symm j.2)
    rwa [Equiv.apply_symm_apply] at h
  -- the prescribed values of the lifted differential: homogeneous preimages of the values of `d`
  -- on the variables of `A`
  have ht : ∀ j : Σ n : ℕ, hpolyB.indices n,
      ∃ b : B, b ∈ ℬ j.1 ∧ π b = d (hpoly.generator ⟨j.1, (e j.1).symm j.2⟩) := by
    intro j
    refine exists_preimage_mem_grade 𝒜 ℬ π.toAddMonoidHom
      (fun n b hb => hπgrade n b hb) hπsurj j.1 ?_
    exact IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜)
      (hpoly.generator_mem ⟨j.1, (e j.1).symm j.2⟩)
  obtain ⟨D, -, hDt, hD0, hDgrade, hDleibniz, hDdpow⟩ :=
    exists_differential_gradedDividedPowerPolynomial ℬ δ ι' hpolyB
      (fun j => (ht j).choose) (fun j => (ht j).choose_spec.1)
  refine ⟨D, hD0, hDgrade, hDleibniz, hDdpow, ?_⟩
  -- `A` over `R'`, with its grading and divided powers restricted along `q`
  let _ : Algebra R' A := algebraOfCoefficientRingHom q
  have hsmul : ∀ r' : R', algebraMap R' A r' = algebraMap R A (q r') := fun _ => rfl
  let _ : GradedAlgebra (coefficientRestrictGrade q hsmul 𝒜) :=
    gradedAlgebra_coefficientRestrictGrade q hsmul 𝒜
  let _ : IsStrictlyGradedComm (coefficientRestrictGrade q hsmul 𝒜) :=
    isStrictlyGradedComm_coefficientRestrictGrade q hsmul 𝒜
  have hsmul' : ∀ (r' : R') (a : A), r' • a = q r' • a := fun r' a =>
    smul_eq_of_algebraMap_comp q hsmul r' a
  -- `d` as an `R'`-linear map, and its clauses for the restricted grading
  obtain ⟨d', hd'⟩ : ∃ d' : A →ₗ[R'] A, ∀ a : A, d' a = d a :=
    ⟨{ toFun := d
       map_add' := d.map_add
       map_smul' := fun r' a => by
         change d (r' • a) = r' • d a
         rw [hsmul' r' a, hsmul' r' (d a), d.map_smul] }, fun _ => rfl⟩
  have hd'0 : ∀ a : A, a ∈ coefficientRestrictGrade q hsmul 𝒜 0 → d' a = 0 := by
    intro a ha
    rw [hd' a]
    exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) ha
  have hd'grade : ∀ (n : ℕ) (a : A), a ∈ coefficientRestrictGrade q hsmul 𝒜 (n + 1) →
      d' a ∈ coefficientRestrictGrade q hsmul 𝒜 n := by
    intro n a ha
    rw [hd' a]
    exact IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) ha
  have hd'leibniz : ∀ (i j : ℕ) (a b : A), a ∈ coefficientRestrictGrade q hsmul 𝒜 i →
      b ∈ coefficientRestrictGrade q hsmul 𝒜 j →
      d' (a * b) = d' a * b + (-1 : R') ^ i • (a * d' b) := by
    intro i j a b ha hb
    rw [hd', hd', hd', hsmul', map_pow, map_neg, map_one]
    exact IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) ha hb
  have hd'dpow : ∀ (n : ℕ) (a : A), n ≠ 0 →
      a ∈ positiveEvenPart (coefficientRestrictGrade q hsmul 𝒜) →
      d' ((restrictDividedPowerStructure q hsmul 𝒜 γ).dpow n a) =
        d' a * (restrictDividedPowerStructure q hsmul 𝒜 γ).dpow (n - 1) a := by
    intro n a hn ha
    rw [restrictDividedPowerStructure_dpow, restrictDividedPowerStructure_dpow, hd', hd']
    exact IsCompatibleWithDifferential.d_dpow (γ := γ) hn
      ((mem_positiveEvenPart_coefficientRestrictGrade q hsmul 𝒜).mp ha)
  -- `π` as an `R'`-algebra map, with its clauses for the restricted grading
  obtain ⟨πa, hπa⟩ : ∃ πa : B →ₐ[R'] A, ∀ b : B, πa b = π b :=
    ⟨{ π with commutes' := fun r' => hπalg r' }, fun _ => rfl⟩
  have hπagrade : ∀ (n : ℕ) (b : B), b ∈ ℬ n → πa b ∈ coefficientRestrictGrade q hsmul 𝒜 n := by
    intro n b hb
    rw [hπa b]
    exact hπgrade n b hb
  have hπadpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ →
      πa (δ.dpow n b) = (restrictDividedPowerStructure q hsmul 𝒜 γ).dpow n (πa b) := by
    intro n b hb
    simp only [hπa, restrictDividedPowerStructure_dpow]
    exact hπdpow n b hb
  -- the three algebra maps
  obtain ⟨ΦB, hΦB, hΦBgrade, hΦBdpow⟩ :=
    exists_oddExtAlgHom_of_differential ℬ δ D hD0 hDgrade hDleibniz hDdpow
  obtain ⟨ΦA, hΦA, hΦAgrade, hΦAdpow⟩ :=
    exists_oddExtAlgHom_of_differential (coefficientRestrictGrade q hsmul 𝒜)
      (restrictDividedPowerStructure q hsmul 𝒜 γ) d' hd'0 hd'grade hd'leibniz hd'dpow
  obtain ⟨ρ, hρpair, hρgrade, hρdpow⟩ :=
    exists_oddExtMap (coefficientRestrictGrade q hsmul 𝒜) ℬ
      (restrictDividedPowerStructure q hsmul 𝒜 γ) δ
      πa hπagrade hπadpow
  -- the two composites, read in coefficients
  have key : ∀ b : B, ρ (ΦB b) =
      oddExtPair (coefficientRestrictGrade q hsmul 𝒜) (π b)
        (signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) 1 (π (D b))) := by
    intro b
    rw [hΦB b, hρpair, map_signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) ℬ πa hπagrade]
    simp only [hπa]
  have key' : ∀ b : B, ΦA (πa b) =
      oddExtPair (coefficientRestrictGrade q hsmul 𝒜) (π b)
        (signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) 1 (d (π b))) := by
    intro b
    rw [hΦA (πa b)]
    simp only [hπa, hd']
  -- the common coefficient map
  obtain ⟨fc, hfc⟩ : ∃ fc : MvPolynomial σ R' →ₐ[R']
      OddVariableExtension (coefficientRestrictGrade q hsmul 𝒜) 1,
      ∀ p' : MvPolynomial σ R',
        fc p' = oddExtPair (coefficientRestrictGrade q hsmul 𝒜) (π (ι' p')) 0 :=
    ⟨(OddVariableExtension.inclusionAlgHom (coefficientRestrictGrade q hsmul 𝒜) 1).comp
      (πa.comp ι'),
      fun p' => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply,
          OddVariableExtension.inclusionAlgHom_apply, hπa, oddExtPair_zero_right]⟩
  have hfcgrade : ∀ p' : MvPolynomial σ R',
      fc p' ∈ OddVariableExtension.grade (coefficientRestrictGrade q hsmul 𝒜) 1 0 := by
    intro p'
    rw [hfc p']
    exact oddExtPair_mem_grade_zero (coefficientRestrictGrade q hsmul 𝒜)
      (hπgrade 0 (ι' p') (hpolyB.coefficient_mem p'))
  have htW : ∀ j : Σ n : ℕ, hpolyB.indices n,
      oddExtPair (coefficientRestrictGrade q hsmul 𝒜) (π (hpolyB.generator j))
          (signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) 1 (d (π (hpolyB.generator j)))) ∈
        OddVariableExtension.grade (coefficientRestrictGrade q hsmul 𝒜) 1 (j.1 + 1) := by
    intro j
    refine oddExtPair_mem_grade_succ (coefficientRestrictGrade q hsmul 𝒜)
      (hπgrade (j.1 + 1) _ (hpolyB.generator_mem j)) ?_
    refine signRingEquiv_mem_grade (coefficientRestrictGrade q hsmul 𝒜) 1 ?_
    exact IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜)
      (hπgrade (j.1 + 1) _ (hpolyB.generator_mem j))
  have hπD : ∀ j : Σ n : ℕ, hpolyB.indices n,
      π (D (hpolyB.generator j)) = d (π (hpolyB.generator j)) := by
    intro j
    rw [hDt j, (ht j).choose_spec.2, hgenπ j]
  obtain ⟨g, -, hu⟩ :=
    existsUnique_gradedDividedPowerPolynomial_map ℬ δ ι' hpolyB
      (OddVariableExtension.grade (coefficientRestrictGrade q hsmul 𝒜) 1)
      (oddVariableDividedPowerStructure (coefficientRestrictGrade q hsmul 𝒜)
        (restrictDividedPowerStructure q hsmul 𝒜 γ) 1 Nat.one_pos odd_one)
      fc hfcgrade
      (fun j => oddExtPair (coefficientRestrictGrade q hsmul 𝒜) (π (hpolyB.generator j))
        (signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) 1 (d (π (hpolyB.generator j)))))
      htW
  have h1 : ρ.comp ΦB = ΦA.comp πa := by
    refine (hu _ ?_).trans (hu _ ?_).symm
    · refine ⟨fun p' => ?_, fun j => ?_, fun n b hb => ?_, fun n b hb => ?_⟩
      · rw [AlgHom.comp_apply, key (ι' p'), hfc p',
          hD0 (ι' p') (hpolyB.coefficient_mem p'), map_zero, map_zero]
      · rw [AlgHom.comp_apply, key (hpolyB.generator j), hπD j]
      · exact hρgrade n _ (hΦBgrade n b hb)
      · rw [AlgHom.comp_apply, AlgHom.comp_apply, hΦBdpow n b hb,
          hρdpow n _ (algHom_mem_positiveEvenPart ℬ
            (OddVariableExtension.grade ℬ 1) ΦB hΦBgrade hb)]
    · refine ⟨fun p' => ?_, fun j => ?_, fun n b hb => ?_, fun n b hb => ?_⟩
      · rw [AlgHom.comp_apply, key' (ι' p'), hfc p', hπcoeff p',
          IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜)
            (hpoly.coefficient_mem (MvPolynomial.map q p')), map_zero]
      · rw [AlgHom.comp_apply, key' (hpolyB.generator j)]
      · exact hΦAgrade n _ (hπagrade n b hb)
      · rw [AlgHom.comp_apply, AlgHom.comp_apply, hπadpow n b hb,
          hΦAdpow n _ (algHom_mem_positiveEvenPart ℬ (coefficientRestrictGrade q hsmul 𝒜) πa
            hπagrade hb)]
  intro b
  have hb := (key b).symm.trans
    ((congrArg (fun k : B →ₐ[R'] OddVariableExtension (coefficientRestrictGrade q hsmul 𝒜) 1 => k b)
      h1).trans (key' b))
  have h2 := congrArg (OddVariableExtension.coefficients (coefficientRestrictGrade q hsmul 𝒜) 1) hb
  rw [coefficients_oddExtPair, coefficients_oddExtPair] at h2
  have h4 := congrArg (signRingEquiv (coefficientRestrictGrade q hsmul 𝒜) 1) (congrArg Prod.snd h2)
  rwa [signRingEquiv_signRingEquiv, signRingEquiv_signRingEquiv] at h4

end Lift

end DividedPowers.TateResolution

end
