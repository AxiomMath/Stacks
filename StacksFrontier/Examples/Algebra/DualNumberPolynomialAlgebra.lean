module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# The differential graded algebra `k[x, y]/(y²)` with `d y = x² + x`

Over a commutative ring `R` and a commutative `R`-algebra `S`, the dual numbers `S[ε]` carry a
`ℤ`-grading with `S` in degree `0` and `S · ε` in degree `-1`, and for every `p : S` the map
`a + b ε ↦ p b` is a differential for that grading. Taking `S = k[x]` and `p = x² - x` over a
field `k` of characteristic two gives the algebra `A = k[x, y]/(y²)` of [Stacks, Tag 09R4], whose
derived category contains a compact object with no finite graded-projective model.

## Main definitions

* `Stacks.Examples.dualNumberGrading`: the grading of `S[ε]` with `S` in degree `0` and `S · ε`
  in degree `-1`.
* `Stacks.Examples.dualNumberDifferential`: the differential `a + b ε ↦ p b` attached to `p : S`.
* `Stacks.Examples.dualNumberDGAlgebra`: the resulting differential graded algebra.
* `Stacks.Examples.charTwoDualNumberDGAlgebra`: the algebra `k[x, y]/(y²)` of Tag 09R4, over
  `k = ZMod 2` and with `d y = x² + x`.
* `Stacks.Examples.dualNumberAugmentation`: the algebra map `S[ε] → k × k` evaluating the
  degree-zero part at the two roots of `x² - x`.

## Main results

* `Stacks.Examples.dualNumberDifferential_eq_zero_iff`: an element of `k[x][ε]` is a cocycle
  exactly when its `ε`-part vanishes.
* `Stacks.Examples.exists_cycle_dualNumberAugmentation` and
  `Stacks.Examples.exists_boundary_of_dualNumberAugmentation_eq_zero`: the augmentation computes
  the cohomology of the algebra, namely `H⁰(A) = k[x]/(x² - x) = k × k` and `Hⁿ(A) = 0` for
  `n ≠ 0`.

## Implementation notes

The grading is described by the two vanishing conditions "the degree-zero part vanishes unless
`n = 0`" and "the `ε`-part vanishes unless `n = -1`", which makes membership decidable by `omega`
on the degree and keeps the two interesting pieces equal to `S` on the nose.

Everything lives in a single universe: the base ring, the algebra and later its modules are all
taken in `Type 0`, which is the shape in which the chapter's differential graded interface
provides compactness of the regular module and the characterisation of compact objects.

## References

* [Stacks Project, Tag 09R4](https://stacks.math.columbia.edu/tag/09R4)
-/

@[expose] public section

namespace Stacks.Examples

/-! ### The grading of the dual numbers -/

/-- The degree-`n` piece of the dual numbers `S[ε]` for the grading putting `S` in degree `0` and
`S · ε` in degree `-1`: an element is homogeneous of degree `n` when its degree-zero part
vanishes unless `n = 0` and its `ε`-part vanishes unless `n = -1`. -/
def dualNumberGrading (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n : ℤ) :
    Submodule R (DualNumber S) where
  carrier := {a | (n ≠ 0 → a.fst = 0) ∧ (n ≠ -1 → a.snd = 0)}
  zero_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  add_mem' ha hb := ⟨fun h => by simp [ha.1 h, hb.1 h], fun h => by simp [ha.2 h, hb.2 h]⟩
  smul_mem' r a ha := ⟨fun h => by simp [ha.1 h], fun h => by simp [ha.2 h]⟩

/-- Membership in the degree-`n` piece of the graded dual numbers, unfolded. -/
theorem mem_dualNumberGrading {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (n : ℤ)
    (a : DualNumber S) :
    a ∈ dualNumberGrading R S n ↔ (n ≠ 0 → a.fst = 0) ∧ (n ≠ -1 → a.snd = 0) := Iff.rfl

/-- The decomposition of a dual number into its degree-zero and degree-`(-1)` parts. -/
def dualNumberDecompose (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    DualNumber S →+ DirectSum ℤ fun n : ℤ => dualNumberGrading R S n where
  toFun a := DirectSum.of (fun n : ℤ => dualNumberGrading R S n) 0
      ⟨TrivSqZeroExt.inl a.fst, by simp [mem_dualNumberGrading]⟩ +
    DirectSum.of (fun n : ℤ => dualNumberGrading R S n) (-1)
      ⟨TrivSqZeroExt.inr a.snd, by simp [mem_dualNumberGrading]⟩
  map_zero' := by
    change DirectSum.of (fun n : ℤ => dualNumberGrading R S n) 0 (0 : dualNumberGrading R S 0) +
      DirectSum.of (fun n : ℤ => dualNumberGrading R S n) (-1)
        (0 : dualNumberGrading R S (-1)) = 0
    simp only [map_zero, add_zero]
  map_add' a b := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    change DirectSum.of (fun n : ℤ => dualNumberGrading R S n) 0
        (⟨TrivSqZeroExt.inl a.fst, by simp [mem_dualNumberGrading]⟩ +
          ⟨TrivSqZeroExt.inl b.fst, by simp [mem_dualNumberGrading]⟩) +
      DirectSum.of (fun n : ℤ => dualNumberGrading R S n) (-1)
        (⟨TrivSqZeroExt.inr a.snd, by simp [mem_dualNumberGrading]⟩ +
          ⟨TrivSqZeroExt.inr b.snd, by simp [mem_dualNumberGrading]⟩) = _
    simp only [map_add]
    abel

/-- On a homogeneous element the decomposition is the single coprojection of its own degree. -/
theorem dualNumberDecompose_coe {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℤ) (a : dualNumberGrading R S n) :
    dualNumberDecompose R S a = DirectSum.of (fun n : ℤ => dualNumberGrading R S n) n a := by
  have ha := a.property
  rw [mem_dualNumberGrading] at ha
  by_cases h₀ : n = 0
  · subst n
    have h : a.val.snd = 0 := ha.2 (by decide)
    have e : TrivSqZeroExt.inl a.val.fst = a.val := TrivSqZeroExt.ext rfl h.symm
    dsimp only [dualNumberDecompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    simp [h, e, ← ZeroMemClass.zero_def]
  · by_cases h₁ : n = -1
    · subst n
      have h : a.val.fst = 0 := ha.1 (by decide)
      have e : TrivSqZeroExt.inr a.val.snd = a.val := TrivSqZeroExt.ext h.symm rfl
      dsimp only [dualNumberDecompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      simp only [h, TrivSqZeroExt.inl_zero, e]
      simp [← ZeroMemClass.zero_def]
    · have h : a = 0 := Subtype.ext (TrivSqZeroExt.ext (ha.1 h₀) (ha.2 h₁))
      subst a
      simp

/-- The grading of the dual numbers is a direct sum decomposition. -/
@[instance_reducible]
noncomputable def dualNumberGradingDecomposition (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : DirectSum.Decomposition (dualNumberGrading R S) :=
  DirectSum.Decomposition.ofAddHom _ (dualNumberDecompose R S)
    (by
      apply AddMonoidHom.ext
      intro a
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, dualNumberDecompose,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, DirectSum.coeAddMonoidHom_of]
      exact TrivSqZeroExt.inl_fst_add_inr_snd_eq a)
    (by
      apply DirectSum.addHom_ext
      intro n a
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      exact dualNumberDecompose_coe n a)

/-- The grading of the dual numbers is multiplicative. -/
theorem dualNumberGrading_mul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (i j : ℤ)
    (a b : DualNumber S) (ha : a ∈ dualNumberGrading R S i) (hb : b ∈ dualNumberGrading R S j) :
    a * b ∈ dualNumberGrading R S (i + j) := by
  rw [mem_dualNumberGrading] at ha hb ⊢
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hi : i = 0
    · have hj : j ≠ 0 := by omega
      simp [hb.1 hj]
    · simp [ha.1 hi]
  · rw [DualNumber.snd_mul]
    have h₁ : a.fst * b.snd = 0 := by
      by_cases hi : i = 0
      · have hj : j ≠ -1 := by omega
        simp [hb.2 hj]
      · simp [ha.1 hi]
    have h₂ : a.snd * b.fst = 0 := by
      by_cases hi : i = -1
      · have hj : j ≠ 0 := by omega
        simp [hb.1 hj]
      · simp [ha.2 hi]
    rw [h₁, h₂, add_zero]

/-- The dual numbers, graded with `S` in degree `0` and `S · ε` in degree `-1`, as a graded
algebra. -/
@[instance_reducible]
noncomputable def dualNumberGradedAlgebra (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    GradedAlgebra (dualNumberGrading R S) :=
  { dualNumberGradingDecomposition R S with
    one_mem := by simp [mem_dualNumberGrading]
    mul_mem := fun i j a b ha hb => dualNumberGrading_mul i j a b ha hb }

/-! ### The differential -/

/-- The differential `a + b ε ↦ p b` of the graded dual numbers attached to an element `p : S`.
It raises the degree by one because it sends `S · ε` into `S` and kills `S`. -/
def dualNumberDifferential (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : S) :
    DualNumber S →ₗ[R] DualNumber S where
  toFun a := TrivSqZeroExt.inl (p * a.snd)
  map_add' a b := by simp [mul_add]
  map_smul' r a := by simp

/-- `dualNumberDifferential R S p` sends `a + b ε` to `p b`. -/
@[simp] theorem dualNumberDifferential_apply {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : S) (a : DualNumber S) :
    dualNumberDifferential R S p a = TrivSqZeroExt.inl (p * a.snd) := rfl

/-- The differential of the graded dual numbers squares to zero. -/
theorem dualNumberDifferential_comp_self {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : S) : dualNumberDifferential R S p ∘ₗ dualNumberDifferential R S p = 0 := by
  ext a <;> simp

/-- The differential of the graded dual numbers raises the degree by one. -/
theorem dualNumberDifferential_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : S)
    (n : ℤ) (a : DualNumber S) (ha : a ∈ dualNumberGrading R S n) :
    dualNumberDifferential R S p a ∈ dualNumberGrading R S (n + 1) := by
  rw [mem_dualNumberGrading] at ha ⊢
  refine ⟨fun h => ?_, fun _ => rfl⟩
  have hn : n ≠ -1 := by omega
  simp [ha.2 hn]

/-- The differential of the graded dual numbers satisfies the graded Leibniz rule. -/
theorem dualNumberDifferential_leibniz {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : S) (n m : ℤ) (a b : DualNumber S) (ha : a ∈ dualNumberGrading R S n)
    (_hb : b ∈ dualNumberGrading R S m) :
    dualNumberDifferential R S p (a * b) = dualNumberDifferential R S p a * b +
      (n.negOnePow : ℤ) • (a * dualNumberDifferential R S p b) := by
  rw [mem_dualNumberGrading] at ha
  by_cases h₀ : n = 0
  · subst n
    have h : a.snd = 0 := ha.2 (by decide)
    apply TrivSqZeroExt.ext <;> simp [h]
    ring
  · by_cases h₁ : n = -1
    · subst n
      have h : a.fst = 0 := ha.1 (by decide)
      apply TrivSqZeroExt.ext <;> simp [h] <;> ring
    · have h : a = 0 := TrivSqZeroExt.ext (ha.1 h₀) (ha.2 h₁)
      simp [h]

/-- The differential graded algebra `S⟨y⟩ = S[y]/(y²)` with `y` of degree `-1` and `d y = p`:
the dual numbers over `S`, graded with `S` in degree `0` and `S · ε` in degree `-1`, with the
differential `a + b ε ↦ p b`. -/
@[implicit_reducible]
noncomputable def dualNumberDGAlgebra (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : S) : DifferentialGradedAlgebra R where
  A := DualNumber S
  grading := dualNumberGrading R S
  gradedAlg := dualNumberGradedAlgebra R S
  d := dualNumberDifferential R S p
  d_comp_d := dualNumberDifferential_comp_self p
  d_mem := dualNumberDifferential_mem p
  leibniz := dualNumberDifferential_leibniz p

/-- The grading of `dualNumberDGAlgebra R S p` is `dualNumberGrading R S`. -/
@[simp] theorem dualNumberDGAlgebra_grading {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : S) : (dualNumberDGAlgebra R S p).grading = dualNumberGrading R S := rfl

/-- The differential of `dualNumberDGAlgebra R S p` sends `a + b ε` to `p b`. -/
@[simp] theorem dualNumberDGAlgebra_d {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : S) (a : DualNumber S) :
    (dualNumberDGAlgebra R S p).d a = TrivSqZeroExt.inl (p * a.snd) := rfl

/-! ### Evaluation at the two roots of `x² - x` -/

/-- Evaluation of a polynomial at `0` and at `1`, as an algebra map `k[x] → k × k`. -/
def polynomialEvalZeroOne (K : Type*) [CommRing K] : Polynomial K →ₐ[K] K × K where
  toFun p := (p.eval 0, p.eval 1)
  map_zero' := by simp
  map_one' := by simp
  map_add' p q := by simp
  map_mul' p q := by simp
  commutes' r := by simp [algebraMap]

/-- `polynomialEvalZeroOne K p` is the pair `(p(0), p(1))`. -/
@[simp] theorem polynomialEvalZeroOne_apply {K : Type*} [CommRing K] (p : Polynomial K) :
    polynomialEvalZeroOne K p = (p.eval 0, p.eval 1) := rfl

/-- Evaluation at `0` and `1` is surjective: a pair of values is interpolated by a polynomial of
degree at most one. -/
theorem polynomialEvalZeroOne_surjective (K : Type*) [CommRing K] :
    Function.Surjective (polynomialEvalZeroOne K) := by
  rintro ⟨a, b⟩
  refine ⟨Polynomial.C a + Polynomial.C (b - a) * Polynomial.X, ?_⟩
  rw [polynomialEvalZeroOne_apply]
  apply Prod.ext <;> simp

/-- The kernel of evaluation at `0` and `1` is generated by `x² - x`. -/
theorem polynomialEvalZeroOne_eq_zero_iff {K : Type*} [CommRing K] (p : Polynomial K) :
    polynomialEvalZeroOne K p = 0 ↔ (Polynomial.X ^ 2 - Polynomial.X) ∣ p := by
  refine ⟨fun h => ?_, fun ⟨q, hq⟩ => by subst hq; ext <;> simp⟩
  have h₀ : p.eval 0 = 0 := congrArg Prod.fst h
  have h₁ : p.eval 1 = 0 := congrArg Prod.snd h
  obtain ⟨q, rfl⟩ : Polynomial.X ∣ p :=
    Polynomial.X_dvd_iff.mpr (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using h₀)
  obtain ⟨r, rfl⟩ : Polynomial.X - Polynomial.C (1 : K) ∣ q :=
    Polynomial.dvd_iff_isRoot.mpr (by simpa using h₁)
  exact ⟨r, by simp only [map_one]; ring⟩

/-- Evaluating `x` at `0` and `1` gives `(0, 1)`. -/
@[simp] theorem polynomialEvalZeroOne_X {K : Type*} [CommRing K] :
    polynomialEvalZeroOne K Polynomial.X = (0, 1) := by
  rw [polynomialEvalZeroOne_apply]
  simp

/-- The polynomial `x² - x` is monic, hence a nonzerodivisor. -/
theorem monic_X_sq_sub_X (K : Type*) [CommRing K] :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial K).Monic := by
  simpa only [Polynomial.C_1, mul_sub, mul_one, ← pow_two] using
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C (1 : K))

/-- An element of `k[x]⟨y⟩` is a cocycle exactly when its `ε`-part vanishes, because `x² - x` is
a nonzerodivisor. -/
theorem dualNumberDifferential_eq_zero_iff {K : Type*} [CommRing K]
    (a : DualNumber (Polynomial K)) :
    dualNumberDifferential K (Polynomial K) (Polynomial.X ^ 2 - Polynomial.X) a = 0 ↔
      a.snd = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hmul : (Polynomial.X ^ 2 - Polynomial.X) * a.snd = 0 := congrArg TrivSqZeroExt.fst h
  exact (monic_X_sq_sub_X K).mul_right_eq_zero_iff.mp hmul

/-- The augmentation `k[x]⟨y⟩ → k × k` of the algebra of Tag 09R4: evaluate the degree-zero part
at the two roots `0` and `1` of `x² - x`. -/
noncomputable def dualNumberAugmentation (K : Type*) [CommRing K] :
    DualNumber (Polynomial K) →ₐ[K] K × K :=
  (polynomialEvalZeroOne K).comp (TrivSqZeroExt.fstHom K (Polynomial K) (Polynomial K))

/-- `dualNumberAugmentation K a` evaluates the degree-zero part of `a` at `0` and `1`. -/
@[simp] theorem dualNumberAugmentation_apply {K : Type*} [CommRing K]
    (a : DualNumber (Polynomial K)) :
    dualNumberAugmentation K a = (a.fst.eval 0, a.fst.eval 1) := rfl

/-- The augmentation kills every coboundary. -/
theorem dualNumberAugmentation_differential {K : Type*} [CommRing K]
    (a : DualNumber (Polynomial K)) :
    dualNumberAugmentation K
      (dualNumberDifferential K (Polynomial K) (Polynomial.X ^ 2 - Polynomial.X) a) = 0 := by
  rw [dualNumberAugmentation_apply]
  apply Prod.ext <;> simp

/-- The augmentation is surjective. -/
theorem dualNumberAugmentation_surjective (K : Type*) [CommRing K] :
    Function.Surjective (dualNumberAugmentation K) := by
  intro z
  obtain ⟨p, hp⟩ := polynomialEvalZeroOne_surjective K z
  exact ⟨TrivSqZeroExt.inl p, hp⟩

/-- The kernel of the augmentation is the ideal generated by `x² - x` and `y`. -/
theorem dualNumberAugmentation_eq_zero_iff {K : Type*} [CommRing K]
    (a : DualNumber (Polynomial K)) (ha : dualNumberAugmentation K a = 0) :
    ∃ b c : DualNumber (Polynomial K),
      a = TrivSqZeroExt.inl (Polynomial.X ^ 2 - Polynomial.X) * b + DualNumber.eps * c := by
  obtain ⟨b, hb⟩ := (polynomialEvalZeroOne_eq_zero_iff a.fst).mp ha
  refine ⟨TrivSqZeroExt.inl b, TrivSqZeroExt.inl a.snd, ?_⟩
  apply TrivSqZeroExt.ext
  · simpa only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl,
      DualNumber.fst_eps, zero_mul, add_zero] using hb
  · simp

/-- Every element of `k × k` is the augmentation of a degree-zero cocycle. -/
theorem exists_cycle_dualNumberAugmentation {K : Type*} [CommRing K] (b : K × K) :
    ∃ a : DualNumber (Polynomial K), a ∈ dualNumberGrading K (Polynomial K) 0 ∧
      dualNumberDifferential K (Polynomial K) (Polynomial.X ^ 2 - Polynomial.X) a = 0 ∧
      dualNumberAugmentation K a = b := by
  obtain ⟨p, hp⟩ := polynomialEvalZeroOne_surjective K b
  exact ⟨TrivSqZeroExt.inl p, by simp [mem_dualNumberGrading], by simp, hp⟩

/-- A homogeneous cocycle killed by the augmentation is a coboundary; in degrees other than zero
every cocycle is a coboundary. This computes the cohomology of `k[x]⟨y⟩`. -/
theorem exists_boundary_of_dualNumberAugmentation_eq_zero {K : Type*} [CommRing K] (n : ℤ)
    (a : DualNumber (Polynomial K)) (ha : a ∈ dualNumberGrading K (Polynomial K) n)
    (hd : dualNumberDifferential K (Polynomial K) (Polynomial.X ^ 2 - Polynomial.X) a = 0)
    (hε : n = 0 → dualNumberAugmentation K a = 0) :
    ∃ c : DualNumber (Polynomial K), c ∈ dualNumberGrading K (Polynomial K) (n - 1) ∧
      dualNumberDifferential K (Polynomial K) (Polynomial.X ^ 2 - Polynomial.X) c = a := by
  have hsnd := (dualNumberDifferential_eq_zero_iff a).mp hd
  by_cases hn : n = 0
  · subst n
    have heval : polynomialEvalZeroOne K a.fst = 0 := hε rfl
    obtain ⟨p, hp⟩ := (polynomialEvalZeroOne_eq_zero_iff a.fst).mp heval
    refine ⟨TrivSqZeroExt.inr p, by simp [mem_dualNumberGrading], ?_⟩
    exact TrivSqZeroExt.ext hp.symm hsnd.symm
  · have hfst := ((mem_dualNumberGrading n a).mp ha).1 hn
    have h : a = 0 := TrivSqZeroExt.ext hfst hsnd
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero, h]⟩

/-- Multiplying by `x` multiplies the augmentation by `(0, 1)`, the idempotent that singles out
the second factor of `k × k`. -/
theorem dualNumberAugmentation_mul_X {K : Type*} [CommRing K] (a : DualNumber (Polynomial K)) :
    dualNumberAugmentation K ((TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial K)) * a) =
      (0, 1) * dualNumberAugmentation K a := by
  rw [map_mul]
  congr 1
  exact polynomialEvalZeroOne_X

/-! ### The algebra of Tag 09R4 -/

/-- **The differential graded algebra of [Stacks, Tag 09R4]**: `A = k[x, y]/(y²)` over the field
`k = ZMod 2` of characteristic two, with `x` of degree `0`, `y` of degree `-1`, `d x = 0` and
`d y = x² + x`. -/
noncomputable abbrev charTwoDualNumberDGAlgebra : DifferentialGradedAlgebra.{0, 0} (ZMod 2) :=
  dualNumberDGAlgebra (ZMod 2) (Polynomial (ZMod 2)) (Polynomial.X ^ 2 - Polynomial.X)

end Stacks.Examples

end
