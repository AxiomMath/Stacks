module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDifferential

/-!
# The differential of a graded divided-power polynomial algebra

Let `A` be a strictly graded-commutative nonnegatively graded algebra with divided powers `γ`
on its positive even part, presented as a graded divided-power polynomial algebra over a
coefficient algebra `P`: a directed union of finite stages, each obtained from the previous one
by adjoining one homogeneous variable of positive degree. This file shows that an arbitrary
choice of a homogeneous element of degree `n` for each variable of degree `n + 1` determines a
differential on `A` — a degree-lowering `R`-linear map obeying the signed Leibniz rule and the
divided-power Leibniz rule — which vanishes on the coefficients and takes the prescribed value
on each variable.

This is the set-indexed, all-degrees form of
[Stacks, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM), which adjoins a single variable.
It is the step the source of
[Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS) omits with "we omit the details
(hint: proceed one variable at the time)", and it is what lifts a differential across a
surjection of coefficient rings once the lifted polynomial algebra is available.

## Main results

* `DividedPowers.TateResolution.exists_differential_gradedDividedPowerPolynomial` — the
  differential determined by its values on the variables.

## Implementation notes

No recursion over the variables appears. A degree-lowering map `D` obeying the two Leibniz rules
is the same thing as a grading- and divided-power-preserving algebra map into the odd-variable
extension `A⟨T⟩` of `A` by one variable `T` of degree one, namely `x ↦ x + T · D x`; and such a
map is exactly what the mapping property of a graded divided-power polynomial algebra
(`existsUnique_gradedDividedPowerPolynomial_map`) produces from a coefficient map and an image
for each variable. So the construction is one application of that mapping property, and the
Leibniz rules are read off from multiplicativity and divided-power preservation of the resulting
algebra map.

The bookkeeping is the Koszul sign. Writing elements of `A⟨T⟩` as `a + bT`, with the variable on
the *right*, multiplication reads `(a + bT)(a' + b'T) = aa' + (ab' + bσ(a'))T`, where `σ` is the
grading-sign automorphism `signRingEquiv 𝒜 1`. Multiplicativity of `x ↦ x + σ(D x) · T`
therefore says `σ(D (xy)) = x σ(D y) + σ(D x) σ(y)`, which after applying the involution `σ` to
both sides is precisely `D (xy) = D x · y + (-1) ^ i • (x · D y)` for `x` of degree `i`. So the
differential is the *twisted* second coefficient of the algebra map, not the second coefficient
itself.

That the first coefficient of the algebra map is the identity is not part of its construction:
it is forced by the uniqueness half of the same mapping property, applied to the composite with
the coefficient projection `A⟨T⟩ → A`, which is an algebra map preserving the grading and the
divided powers. The divided-power half of that uses the formula
`γₙ(a + bT) = γₙ(a) + γₙ₋₁(a) b T` of
[Stacks, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH), together with the observation
that both coefficients of an element of the positive even part of `A⟨T⟩` are homogeneous of the
expected parity — the first even, the second odd — which is what makes that formula applicable.

The divided-power Leibniz rule comes out as `D (γₙ(x)) = σ(γₙ₋₁(x)) · D x`; the factor
`γₙ₋₁(x)` is even, hence fixed by `σ` and central, which is how the stated form
`D (γₙ(x)) = D x · γₙ₋₁(x)` is reached. Squareness of the differential is not asserted and is
false in the intended application: in Tag 09PS the lifted differential has `D ∘ D ≠ 0`, and that
failure is the derivation the tag constructs. For the same reason the conclusion lists the
differential graded algebra axioms individually instead of using
`IsDifferentialGradedAlgebra`, which includes `d ∘ d = 0`.

## References

* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local implicit_reducible] TwistedModule

section OddExtOne

variable {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- The coefficient of `1` in the degree-one odd-variable extension, as an algebra map. -/
public def oddExtFst : OddVariableExtension 𝒜 1 →ₐ[R] A where
  toFun x := x.fst
  map_one' := rfl
  map_mul' x y := TrivSqZeroExt.fst_mul x y
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [IsStrictlyGradedComm 𝒜] in
/-- The grading sign is `R`-linear. -/
public theorem signRingEquiv_smul (d : ℕ) (r : R) (a : A) :
    signRingEquiv 𝒜 d (r • a) = r • signRingEquiv 𝒜 d a := by
  rw [Algebra.smul_def, map_mul, signRingEquiv_algebraMap, ← Algebra.smul_def]

omit [IsStrictlyGradedComm 𝒜] in
/-- The grading sign for `d = 1` fixes the even part. -/
public theorem signRingEquiv_one_of_mem_evenPart {y : A} (hy : y ∈ evenPart 𝒜) :
    signRingEquiv 𝒜 1 y = y := by
  induction hy using Submodule.iSup_induction' with
  | mem k y hy =>
      rw [signRingEquiv_of_mem 𝒜 1 (2 * k) hy, one_mul, pow_mul]
      simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz]

/-- An element of the even part is central. -/
public theorem mul_comm_of_mem_evenPart {y : A} (hy : y ∈ evenPart 𝒜) (z : A) :
    y * z = z * y := by
  induction hy using Submodule.iSup_induction' with
  | mem k y hy => exact mul_comm_of_mem_grade_even' 𝒜 hy z
  | zero => simp
  | add y y' _ _ hy hy' => rw [add_mul, mul_add, hy, hy']

omit [IsStrictlyGradedComm 𝒜] in
/-- The two coefficients of the canonical expression `a + bT`. -/
public theorem coefficients_inclusion_add_mul_generator (a b : A) :
    OddVariableExtension.coefficients 𝒜 1
        (OddVariableExtension.inclusion 𝒜 1 a +
          OddVariableExtension.inclusion 𝒜 1 b * OddVariableExtension.generator 𝒜 1) =
      (a, b) := by
  simp

omit [IsStrictlyGradedComm 𝒜] in
/-- The canonical expression of an element as `a + bT`. -/
public theorem inclusion_add_mul_generator_coefficients (x : OddVariableExtension 𝒜 1) :
    OddVariableExtension.inclusion 𝒜 1 (OddVariableExtension.coefficients 𝒜 1 x).1 +
        OddVariableExtension.inclusion 𝒜 1 (OddVariableExtension.coefficients 𝒜 1 x).2 *
          OddVariableExtension.generator 𝒜 1 = x :=
  OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator 𝒜 1 x

/-- Membership in a positive degree of the degree-one odd-variable extension, in terms of the
coefficients. -/
private theorem mem_grade_succ_iff_coefficients {R : Type u} {A : Type w} [CommRing R] [Ring A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ)
    (x : OddVariableExtension 𝒜 1) :
    x ∈ OddVariableExtension.grade 𝒜 1 (m + 1) ↔
      (OddVariableExtension.coefficients 𝒜 1 x).1 ∈ 𝒜 (m + 1) ∧
        (OddVariableExtension.coefficients 𝒜 1 x).2 ∈ 𝒜 m := by
  rw [OddVariableExtension.mem_grade_coefficients_iff,
    ite_eq_left (by omega : (1 : ℕ) ≤ m + 1), Nat.add_sub_cancel]

omit [IsStrictlyGradedComm 𝒜] in
/-- Both coefficients of an element of the positive even part of the degree-one odd-variable
extension are homogeneous of the expected parity. -/
public theorem mem_positiveEvenPart_oddExt
    {x : OddVariableExtension 𝒜 1}
    (hx : x ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1)) :
    (OddVariableExtension.coefficients 𝒜 1 x).1 ∈ positiveEvenPart 𝒜 ∧
      (OddVariableExtension.coefficients 𝒜 1 x).2 ∈ oddPart 𝒜 := by
  induction hx using Submodule.iSup_induction' with
  | mem k y hy =>
      obtain ⟨hy1, hy2⟩ := (mem_grade_succ_iff_coefficients 𝒜 (2 * k + 1) y).mp hy
      exact ⟨Submodule.mem_iSup_of_mem k hy1, Submodule.mem_iSup_of_mem k hy2⟩
  | zero => exact ⟨(positiveEvenPart 𝒜).zero_mem, (oddPart 𝒜).zero_mem⟩
  | add y z _ _ hy hz =>
      exact ⟨(positiveEvenPart 𝒜).add_mem hy.1 hz.1, (oddPart 𝒜).add_mem hy.2 hz.2⟩

/-- The two coefficients of a divided power in the degree-one odd-variable extension. -/
public theorem coefficients_dpow (γ : DividedPowerStructure 𝒜) (n : ℕ) (hn : n ≠ 0)
    {x : OddVariableExtension 𝒜 1}
    (hx : x ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1)) :
    OddVariableExtension.coefficients 𝒜 1
        ((oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow n x) =
      (γ.dpow n (OddVariableExtension.coefficients 𝒜 1 x).1,
        γ.dpow (n - 1) (OddVariableExtension.coefficients 𝒜 1 x).1 *
          (OddVariableExtension.coefficients 𝒜 1 x).2) := by
  obtain ⟨hfst, hsnd⟩ := mem_positiveEvenPart_oddExt 𝒜 hx
  rw [← inclusion_add_mul_generator_coefficients 𝒜 x,
    oddVariableDividedPowerStructure_dpow 𝒜 γ 1 Nat.one_pos odd_one n hn _ _ hfst hsnd,
    coefficients_inclusion_add_mul_generator, coefficients_inclusion_add_mul_generator]

/-- The first coefficient preserves divided powers. -/
public theorem oddExtFst_dpow (γ : DividedPowerStructure 𝒜) (n : ℕ)
    {x : OddVariableExtension 𝒜 1}
    (hx : x ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1)) :
    (OddVariableExtension.coefficients 𝒜 1
        ((oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow n x)).1 =
      γ.dpow n (OddVariableExtension.coefficients 𝒜 1 x).1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one).dpow_zero hx,
      γ.dpow_zero (mem_positiveEvenPart_oddExt 𝒜 hx).1]
    rfl
  rw [coefficients_dpow 𝒜 γ n (by omega) hx]

end OddExtOne

section Main

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)

/-- **The differential of a graded divided-power polynomial algebra, prescribed on the
variables.** -/
public theorem exists_differential_gradedDividedPowerPolynomial
    (h : GradedDividedPowerPolynomial 𝒜 γ ι)
    (t : (Σ n : ℕ, h.indices n) → A) (ht : ∀ j, t j ∈ 𝒜 j.1) :
    ∃ D : A →ₗ[R] A,
      (∀ p : P, D (ι p) = 0) ∧
      (∀ j : Σ n : ℕ, h.indices n, D (h.generator j) = t j) ∧
      (∀ x : A, x ∈ 𝒜 0 → D x = 0) ∧
      (∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 1) → D x ∈ 𝒜 n) ∧
      (∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
        D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) ∧
      (∀ (n : ℕ) (x : A), n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
        D (γ.dpow n x) = D x * γ.dpow (n - 1) x) := by
  classical
  have hσinv : ∀ a : A, signRingEquiv 𝒜 1 (signRingEquiv 𝒜 1 a) = a :=
    signRingHom_involutive 𝒜 1
  have hσmem : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → signRingEquiv 𝒜 1 a ∈ 𝒜 m := by
    intro m a ha
    rw [signRingEquiv_of_mem 𝒜 1 m ha]
    exact (𝒜 m).smul_mem _ ha
  -- the prescribed images of the variables in the degree-one odd-variable extension
  have ht' : ∀ j : Σ n : ℕ, h.indices n,
      OddVariableExtension.inclusion 𝒜 1 (h.generator j) +
        OddVariableExtension.inclusion 𝒜 1 (signRingEquiv 𝒜 1 (t j)) *
          OddVariableExtension.generator 𝒜 1 ∈
        OddVariableExtension.grade 𝒜 1 (j.1 + 1) := by
    intro j
    rw [mem_grade_succ_iff_coefficients, coefficients_inclusion_add_mul_generator]
    exact ⟨h.generator_mem j, hσmem j.1 (t j) (ht j)⟩
  obtain ⟨g, hg, -⟩ := existsUnique_gradedDividedPowerPolynomial_map 𝒜 γ ι h
    (OddVariableExtension.grade 𝒜 1)
    (oddVariableDividedPowerStructure 𝒜 γ 1 Nat.one_pos odd_one)
    ((OddVariableExtension.inclusionAlgHom 𝒜 1).comp ι)
    (fun p => OddVariableExtension.inclusion_mem_grade 𝒜 1 0 (h.coefficient_mem p)) _ ht'
  obtain ⟨hgc, hgt, hggrade, hgdpow⟩ := hg
  -- the first coefficient of `g` is the identity
  have hfst : ∀ a : A, (OddVariableExtension.coefficients 𝒜 1 (g a)).1 = a := by
    obtain ⟨gid, -, hu⟩ := existsUnique_gradedDividedPowerPolynomial_map 𝒜 γ ι h 𝒜 γ ι
      h.coefficient_mem h.generator h.generator_mem
    have h1 : (oddExtFst 𝒜).comp g = AlgHom.id R A := by
      refine (hu _ ?_).trans (hu _ ?_).symm
      · refine ⟨fun p => ?_, fun j => ?_, fun n a ha => ?_, fun n a ha => ?_⟩
        · change (OddVariableExtension.coefficients 𝒜 1 (g (ι p))).1 = ι p
          rw [hgc p]
          rfl
        · change (OddVariableExtension.coefficients 𝒜 1 (g (h.generator j))).1 =
            h.generator j
          rw [hgt j, coefficients_inclusion_add_mul_generator]
        · change (OddVariableExtension.coefficients 𝒜 1 (g a)).1 ∈ 𝒜 n
          exact ((OddVariableExtension.mem_grade_coefficients_iff 𝒜 1 n (g a)).mp
            (hggrade n a ha)).1
        · change (OddVariableExtension.coefficients 𝒜 1 (g (γ.dpow n a))).1 =
            γ.dpow n (OddVariableExtension.coefficients 𝒜 1 (g a)).1
          rw [hgdpow n a ha]
          exact oddExtFst_dpow 𝒜 γ n
            (algHom_mem_positiveEvenPart 𝒜 (OddVariableExtension.grade 𝒜 1) g hggrade ha)
      · exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ ha => ha, fun _ _ _ => rfl⟩
    intro a
    exact congrArg (fun k : A →ₐ[R] A => k a) h1
  -- the second coefficient, twisted by the grading sign, is the differential
  set D : A →ₗ[R] A := (signLinearMap 𝒜 1).comp ((LinearMap.snd R A A).comp
    ((OddVariableExtension.coefficients 𝒜 1).toLinearMap.comp g.toLinearMap))
  have hDapp : ∀ a : A,
      D a = signRingEquiv 𝒜 1 (OddVariableExtension.coefficients 𝒜 1 (g a)).2 := fun _ => rfl
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hDapp, hgc p]
    change signRingEquiv 𝒜 1 (OddVariableExtension.coefficients 𝒜 1
      (OddVariableExtension.inclusion 𝒜 1 (ι p))).2 = 0
    rw [OddVariableExtension.coefficients_inclusion]
    simp
  · intro j
    rw [hDapp, hgt j, coefficients_inclusion_add_mul_generator, hσinv]
  · intro x hx
    have hmem := ((OddVariableExtension.mem_grade_coefficients_iff 𝒜 1 0 (g x)).mp
      (hggrade 0 x hx)).2
    rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0), Submodule.mem_bot] at hmem
    rw [hDapp, hmem]
    simp
  · intro n x hx
    rw [hDapp]
    exact hσmem n _ ((mem_grade_succ_iff_coefficients 𝒜 n (g x)).mp (hggrade (n + 1) x hx)).2
  · intro i _ x y hx _
    rw [hDapp, hDapp, hDapp, map_mul, OddVariableExtension.coefficients_mul, hfst x, hfst y,
      map_add, map_mul, map_mul, hσinv, signRingEquiv_of_mem 𝒜 1 i hx, one_mul, smul_mul_assoc,
      add_comm]
  · intro n x hn hx
    have hgx : g x ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1) :=
      algHom_mem_positiveEvenPart 𝒜 (OddVariableExtension.grade 𝒜 1) g hggrade hx
    have heven : γ.dpow (n - 1) x ∈ evenPart 𝒜 := by
      rcases Nat.eq_zero_or_pos (n - 1) with hz | hp
      · rw [hz, γ.dpow_zero hx]
        exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
      · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem (by omega) hx)
    rw [hDapp, hDapp, hgdpow n x hx, coefficients_dpow 𝒜 γ n hn hgx, hfst x, map_mul,
      signRingEquiv_one_of_mem_evenPart 𝒜 heven, mul_comm_of_mem_evenPart 𝒜 heven]

end Main

end DividedPowers.TateResolution

end
