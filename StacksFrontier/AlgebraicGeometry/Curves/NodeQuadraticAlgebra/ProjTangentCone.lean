module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.DegreeSeparable
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# The projectivized tangent cone of a node is the spectrum of its quadratic algebra

Let `(A, 𝔪, κ)` be a Noetherian nodal local algebra over a field. Its tangent cone is
`Spec` of the associated graded ring `⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹`, and the projectivized tangent cone is
`Proj` of that graded ring. This file shows the projectivized tangent cone is the spectrum of
the quadratic algebra `Stacks.Curves.quadraticAlgebra A`, the closed fibre of the
normalization — so a node has exactly two branches, counted with their residue field.

The proof is a chart computation. Writing the quadratic relation in lifted cotangent
coordinates as `a x² + b x y + c y² ∈ 𝔪³` with `a` a unit, the relation forces `𝔪² = y 𝔪`
(`Stacks.Curves.maximalIdeal_sq_eq_span_mul_of_quadratic_relation`). Hence the initial form
`ȳ ∈ 𝔪/𝔪²` is a nonzerodivisor on the associated graded ring in the strong sense that its
basic open `D₊(ȳ)` is the whole of `Proj`
(`Stacks.Curves.basicOpen_initialForm_eq_top`): any homogeneous prime missing `ȳ` would
contain the irrelevant ideal, which is impossible. So `Proj` is a *single* affine chart,
`Spec` of the degree-zero part `(G_𝔪(A))_{(ȳ)}` of the localization at `ȳ`.

That degree-zero part is computed by the same affine blow-up chart `A[x/y]` that computes the
normalization: `Stacks.Curves.stableIdealQuotientToChart` sends the class of `a/y` to the
fraction `ā/ȳ` of initial forms, and is a surjective ring map whose kernel is `𝔪 A[x/y]`
(`Stacks.Curves.stableIdealQuotientToChart_ker`). Since `A[x/y]` is the normalization
(`Stacks.Curves.eq_integralClosure_of_finite_of_radical_span`), its closed fibre is the
quadratic algebra.

## Main definitions

* `Stacks.Curves.initialForm` — the initial form homomorphism `𝔪ⁿ →+ G_𝔪(A)`, landing in
  degree `n`.
* `Stacks.Curves.tangentFraction` — the degree-zero fraction `ā/ȳⁿ` in the localization of
  `G_𝔪(A)` away from the degree-one initial form of `y`.
* `Stacks.Curves.stableIdealQuotientToChart` — the ring map from the affine blow-up chart to
  that localization.

## Main results

* `Stacks.Curves.proj_associatedGraded_iso_quadraticAlgebraSpec` — the projectivized tangent
  cone of a node is the spectrum of its quadratic algebra.
* `Stacks.Curves.basicOpen_initialForm_eq_top` — the basic open of the degree-one initial form
  of a generator of `𝔪²/𝔪` is all of `Proj`.
* `Stacks.Curves.stableIdealQuotientFibreEquivChart` — the closed fibre of the affine blow-up
  chart is the degree-zero part of the localized associated graded ring.

## Implementation notes

The grading on the associated graded ring is supplied as a hypothesis: the family
`𝒢 : ℕ → AddSubgroup (AssociatedGraded.gradedRing 𝔪)` together with `GradedRing 𝒢` and the
equation identifying `𝒢 n` with the range of the `n`-th canonical inclusion. That keeps the
statement independent of how the `GradedRing` instance is produced, which is what
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` requires in order to form `Proj`.

## References

* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Curves

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra k A]

section

open AssociatedGraded

/-! ### Initial forms -/

/-- **The initial form map `Iⁿ →+ G_I(R)`**, sending `a ∈ Iⁿ` to the class of `a` in the
degree-`n` summand `Iⁿ/Iⁿ⁺¹`. It is additive, not multiplicative: it multiplies degrees
(`Stacks.Curves.initialForm_mul`). -/
def initialForm {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    ↥(I ^ n) →+ gradedRing I where
  toFun a := DirectSum.of (fun n => piece (M := R) I n) n
    (mk I n ⟨a.1, by simpa only [ring_power_eq] using a.2⟩)
  map_zero' := by
    change (DirectSum.of (fun n => piece (M := R) I n) n) 0 = 0
    exact map_zero _
  map_add' a b := by
    change (DirectSum.of (fun n => piece (M := R) I n) n)
      (Submodule.Quotient.mk (⟨a.1, by simpa only [ring_power_eq] using a.2⟩ +
        ⟨b.1, by simpa only [ring_power_eq] using b.2⟩ : power I n)) = _
    rw [Submodule.Quotient.mk_add, map_add]
    rfl

/-- The initial form is multiplicative across degrees: the product of the initial forms of
`a ∈ Iⁱ` and `b ∈ Iʲ` is the initial form of `a * b ∈ Iⁱ⁺ʲ`. -/
theorem initialForm_mul {R : Type*} [CommRing R] (I : Ideal R)
    (i j : ℕ) (a : ↥(I ^ i)) (b : ↥(I ^ j)) :
    initialForm I i a * initialForm I j b =
      initialForm I (i + j) ⟨a.1 * b.1, by
        rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ := by
  simp only [initialForm, AddMonoidHom.coe_mk, ZeroHom.coe_mk, of_mul_of,
    homogeneousSMul_mk]
  rfl

/-- Initial forms of equal elements, taken in equal degrees, are equal. -/
theorem initialForm_congr {R : Type*} [CommRing R] (I : Ideal R)
    (i j : ℕ) (hij : i = j) (a : ↥(I ^ i)) (b : ↥(I ^ j)) (hab : a.1 = b.1) :
    initialForm I i a = initialForm I j b := by
  subst j
  exact congrArg (initialForm I i) (Subtype.ext hab)

/-- An element of `Iⁿ` has vanishing initial form in degree `n` exactly when it already lies
in `Iⁿ⁺¹`. -/
theorem initialForm_eq_zero_iff {R : Type*} [CommRing R] (I : Ideal R)
    (n : ℕ) (a : ↥(I ^ n)) :
    initialForm I n a = 0 ↔ a.1 ∈ I ^ (n + 1) := by
  show DirectSum.of (fun n => piece (M := R) I n) n _ = 0 ↔ _
  rw [← map_zero (DirectSum.of (fun n => piece (M := R) I n) n),
    (DirectSum.of_injective (i := n)).eq_iff]
  show Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  show a.1 ∈ power I (n + 1) ↔ _
  rw [ring_power_eq]

/-- The initial form of `1 ∈ I⁰` is `1`. -/
theorem initialForm_one {R : Type*} [CommRing R] (I : Ideal R) :
    initialForm I 0 ⟨1, by simp⟩ = 1 := rfl

/-- Initial forms in degree `n` are homogeneous of degree `n`. -/
theorem initialForm_mem {R : Type*} [CommRing R] (I : Ideal R)
    (𝒢 : ℕ → AddSubgroup (gradedRing I))
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n : ℕ) (a : ↥(I ^ n)) : initialForm I n a ∈ 𝒢 n := by
  rw [h𝒢]
  exact ⟨_, rfl⟩

/-- Every homogeneous element of degree `n` is the initial form of an element of `Iⁿ`. -/
theorem exists_initialForm_of_mem {R : Type*} [CommRing R] (I : Ideal R)
    (𝒢 : ℕ → AddSubgroup (gradedRing I))
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n : ℕ) {z : gradedRing I} (hz : z ∈ 𝒢 n) :
    ∃ a : ↥(I ^ n), initialForm I n a = z := by
  rw [h𝒢] at hz
  obtain ⟨a, rfl⟩ := hz
  induction a using Quotient.inductionOn with
  | _ a => exact ⟨⟨a.1, by simpa only [ring_power_eq] using a.2⟩, rfl⟩

/-- **An ideal with `I² = y I` has `Iⁿ⁺¹ = yⁿ I`.** -/
theorem pow_succ_eq_span_pow_mul_of_sq_eq_span_mul
    {R : Type*} [CommRing R] (I : Ideal R) (y : R)
    (hI : I * I = Ideal.span {y} * I) (n : ℕ) :
    I ^ (n + 1) = Ideal.span {y ^ n} * I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ I (n + 1), ih, mul_assoc, hI, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ]

/-- The `n`-th power of the degree-one initial form of `y ∈ I` is the initial form of
`yⁿ ∈ Iⁿ`. -/
theorem initialForm_pow {R : Type*} [CommRing R] (I : Ideal R) (y : I) (n : ℕ) :
    (initialForm I 1 ⟨y.1, by simpa only [pow_one] using y.2⟩) ^ n =
      initialForm I n ⟨y.1 ^ n, Ideal.pow_mem_pow y.2 n⟩ := by
  induction n with
  | zero => simpa only [pow_zero] using (initialForm_one I).symm
  | succ n ih =>
    rw [pow_succ, ih, initialForm_mul]
    congr 1
    exact Subtype.ext (pow_succ y.1 n).symm

/-- **An ideal with `I² = y I` has `Iⁿ⁺² = y Iⁿ⁺¹`.** -/
theorem pow_succ_eq_span_mul_pow_of_sq_eq_span_mul
    {R : Type*} [CommRing R] (I : Ideal R) (y : R)
    (hI : I * I = Ideal.span {y} * I) (n : ℕ) :
    I ^ (n + 1 + 1) = Ideal.span {y} * I ^ (n + 1) := by
  rw [pow_succ_eq_span_pow_mul_of_sq_eq_span_mul I y hI (n + 1),
    pow_succ_eq_span_pow_mul_of_sq_eq_span_mul I y hI n, ← mul_assoc,
    Ideal.span_singleton_mul_span_singleton, ← pow_succ']

/-- An element of `Iⁿ⁺¹` is `yⁿ b` for some `b ∈ I`, when `I² = y I`. -/
private theorem exists_eq_pow_mul_of_mem_pow_succ
    {R : Type*} [CommRing R] (I : Ideal R) (y : R)
    (hI : I * I = Ideal.span {y} * I) (n : ℕ) {a : R} (ha : a ∈ I ^ (n + 1)) :
    ∃ b ∈ I, y ^ n * b = a := by
  rw [pow_succ_eq_span_pow_mul_of_sq_eq_span_mul I y hI n] at ha
  exact Ideal.mem_span_singleton_mul.mp ha

/-- **When `I² = y I`, the basic open of the degree-one initial form of `y` is all of `Proj`.**
So `Proj G_I(R)` is covered by the single affine chart `D₊(ȳ)`. Indeed a homogeneous prime
avoiding `ȳ` contains every homogeneous element of positive degree, because `Iⁿ⁺² = y Iⁿ⁺¹`
makes the square of any such element divisible by `ȳ`; that is the irrelevant ideal, which no
point of `Proj` contains. -/
theorem basicOpen_initialForm_eq_top
    {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (hI : I * I = Ideal.span {y.1} * I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) :
    ProjectiveSpectrum.basicOpen 𝒢
      (initialForm I 1 ⟨y.1, by simpa only [pow_one] using y.2⟩) = ⊤ := by
  apply top_le_iff.mp
  intro p _
  show initialForm I 1 ⟨y.1, by simpa only [pow_one] using y.2⟩ ∉ p.asHomogeneousIdeal
  intro hy
  apply p.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi z hz
  obtain ⟨a, rfl⟩ := exists_initialForm_of_mem I 𝒢 h𝒢 i hz
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hsq : a.1 ^ 2 ∈ I ^ (n + n + 1 + 1) := by
    have h := Ideal.mul_mem_mul a.2 a.2
    rw [← pow_add] at h
    simpa only [pow_two, Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using h
  rw [pow_succ_eq_span_mul_pow_of_sq_eq_span_mul I y.1 hI (n + n)] at hsq
  obtain ⟨b, hb, he⟩ := Ideal.mem_span_singleton_mul.mp hsq
  have heq : initialForm I (n + 1) a ^ 2 =
      initialForm I 1 ⟨y.1, by simpa only [pow_one] using y.2⟩ *
        initialForm I (n + n + 1) ⟨b, hb⟩ := by
    rw [pow_two, initialForm_mul, initialForm_mul]
    exact initialForm_congr I _ _ (by omega) _ _
      ((pow_two a.1).symm.trans he.symm)
  apply p.isPrime.mem_of_pow_mem 2
  rw [heq]
  exact p.asHomogeneousIdeal.toIdeal.mul_mem_right _ hy

/-- **The degree-zero fraction `ā/ȳⁿ`** in the localization of `G_I(R)` away from the
degree-one initial form of `y`, for `a ∈ Iⁿ`. -/
def tangentFraction {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n : ℕ) (a : ↥(I ^ n)) :
    HomogeneousLocalization.Away 𝒢
      (initialForm I 1 ⟨y.1, by simp⟩) :=
  HomogeneousLocalization.Away.mk 𝒢 (initialForm_mem I 𝒢 h𝒢 1 _) n
    (initialForm I n a) (by simpa using initialForm_mem I 𝒢 h𝒢 n a)

/-- The degree-one initial form of `y`, the element `Proj` is localized away from. -/
abbrev tangentGenerator {R : Type*} [CommRing R] (I : Ideal R) (y : I) :
    gradedRing I :=
  initialForm I 1 ⟨y.1, by simpa only [pow_one] using y.2⟩

/-- The value of `Stacks.Curves.tangentFraction` in the localization of `G_I(R)` away from `ȳ`
is the fraction `ā/ȳⁿ`. -/
theorem tangentFraction_val {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n : ℕ) (a : ↥(I ^ n)) :
    (tangentFraction I y 𝒢 h𝒢 n a).val =
      IsLocalization.mk' (Localization (Submonoid.powers (tangentGenerator I y)))
        (initialForm I n a)
        ⟨(tangentGenerator I y) ^ n,
          (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩ :=
  Localization.mk_eq_mk'_apply _ _

/-- The fraction `ā/ȳⁿ` is additive in `a`. -/
theorem tangentFraction_add {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n : ℕ) (a b : ↥(I ^ n)) :
    tangentFraction I y 𝒢 h𝒢 n (a + b) =
      tangentFraction I y 𝒢 h𝒢 n a + tangentFraction I y 𝒢 h𝒢 n b := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, tangentFraction_val, map_add]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  rw [add_mul, IsLocalization.mk'_spec, IsLocalization.mk'_spec, map_add]

/-- The fractions `ā/ȳⁿ` and `b̄/ȳᵐ` are equal when `yⁿ b = yᵐ a`. -/
theorem tangentFraction_eq_of_mul_eq {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m))
    (h : y.1 ^ n * b.1 = y.1 ^ m * a.1) :
    tangentFraction I y 𝒢 h𝒢 n a = tangentFraction I y 𝒢 h𝒢 m b := by
  apply HomogeneousLocalization.val_injective
  simp only [tangentFraction_val]
  apply IsLocalization.mk'_eq_of_eq
  simp only [initialForm_pow, initialForm_mul]
  exact initialForm_congr I _ _ (Nat.add_comm _ _) _ _ h

/-- The fraction of a product is the product of the fractions:
`(ab)‾/ȳⁿ⁺ᵐ = (ā/ȳⁿ) · (b̄/ȳᵐ)` for `a ∈ Iⁿ` and `b ∈ Iᵐ`. -/
theorem tangentFraction_mul {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (n m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m)) :
    tangentFraction I y 𝒢 h𝒢 (n + m)
      ⟨a.1 * b.1, by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ =
    tangentFraction I y 𝒢 h𝒢 n a * tangentFraction I y 𝒢 h𝒢 m b := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, tangentFraction_val,
    ← IsLocalization.mk'_mul, initialForm_mul]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

/-- The fraction `ȳⁿ/ȳⁿ` is `1`. -/
theorem tangentFraction_self {R : Type*} [CommRing R] (I : Ideal R) (y : I)
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) (n : ℕ) :
    tangentFraction I y 𝒢 h𝒢 n ⟨y.1 ^ n, Ideal.pow_mem_pow y.2 n⟩ = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [tangentFraction_val, HomogeneousLocalization.val_one,
    ← initialForm_pow]
  exact IsLocalization.mk'_self _ _

/-- Multiplying an element `b` of the chart `R[I/y]` by `y` recovers, in `Q`, the element of
`I` that `b` is the quotient of by `y`. -/
theorem stableIdealQuotient_symm_apply_mul
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (b : stableIdealQuotient I y u hu hI) :
    algebraMap R Q ((stableIdealQuotientLinearEquiv I y u hu hI hinj).symm b).1 =
      (u : Q) * (b : Q) := by
  have h := congrArg Subtype.val
    ((stableIdealQuotientLinearEquiv I y u hu hI hinj).apply_symm_apply b)
  change ↑(u⁻¹) * algebraMap R Q _ = _ at h
  rw [← h]
  simp

/-- **The ring map from the affine blow-up chart `R[I/y]` to the degree-zero part of
`G_I(R)` localized away from `ȳ`**, sending `a/y` to `ā/ȳ`. It is surjective with kernel
`I R[I/y]`, so it identifies the closed fibre of the chart with the affine chart of `Proj`. -/
def stableIdealQuotientToChart
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) :
    stableIdealQuotient I y u hu hI →+*
      HomogeneousLocalization.Away 𝒢
        (initialForm I 1 ⟨y.1, by simp⟩) where
  toFun b := tangentFraction I y 𝒢 h𝒢 1
    ⟨((stableIdealQuotientLinearEquiv I y u hu hI hinj).symm b).1,
      by simp⟩
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [tangentFraction_val, HomogeneousLocalization.val_zero, map_zero]
    change IsLocalization.mk' _ ((initialForm I 1) 0) _ = 0
    rw [map_zero, IsLocalization.mk'_zero]
  map_one' := by
    have h : (stableIdealQuotientLinearEquiv I y u hu hI hinj).symm 1 = y := by
      apply Subtype.ext
      apply hinj
      rw [stableIdealQuotient_symm_apply_mul]
      simpa using hu
    simp only [h]
    convert tangentFraction_self I y 𝒢 h𝒢 1 using 1
    simp
  map_add' a b := by
    simp only [map_add, Submodule.coe_add]
    exact
      tangentFraction_add I y 𝒢 h𝒢 1
        ⟨((stableIdealQuotientLinearEquiv I y u hu hI hinj).symm a).1, by simp⟩
        ⟨((stableIdealQuotientLinearEquiv I y u hu hI hinj).symm b).1, by simp⟩
  map_mul' a b := by
    rw [← tangentFraction_mul]
    apply tangentFraction_eq_of_mul_eq
    apply hinj
    simp only [map_mul, map_pow, stableIdealQuotient_symm_apply_mul, ← hu]
    change (u : Q) ^ 1 * (↑u * (a : Q) * (↑u * (b : Q))) =
      (u : Q) ^ (1 + 1) * (↑u * ((a : Q) * (b : Q)))
    ring

/-- The fraction `ā/ȳ` vanishes exactly when `a ∈ I²`; this is what makes the kernel of
`Stacks.Curves.stableIdealQuotientToChart` the ideal `I R[I/y]`. -/
theorem tangentFraction_one_eq_zero_iff
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n))
    (a : ↥(I ^ 1)) :
    tangentFraction I y 𝒢 h𝒢 1 a = 0 ↔ a.1 ∈ I ^ 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hv := congrArg HomogeneousLocalization.val h
    simp only [tangentFraction_val, HomogeneousLocalization.val_zero,
      IsLocalization.mk'_eq_zero_iff] at hv
    obtain ⟨t, hn⟩ := hv
    obtain ⟨n, he⟩ := t.2
    change t.1 * initialForm I 1 a = 0 at hn
    rw [← he] at hn
    change (initialForm I 1 ⟨y.1, by simp⟩) ^ n *
      initialForm I 1 a = 0 at hn
    rw [initialForm_pow, initialForm_mul, initialForm_eq_zero_iff] at hn
    obtain ⟨b, hb, he⟩ := exists_eq_pow_mul_of_mem_pow_succ I y.1 hI (n + 1) hn
    have heq : a.1 = y.1 * b := by
      apply hinj
      apply (u ^ n).isUnit.mul_left_cancel
      have he' := congrArg (algebraMap R Q) he
      simp only [map_mul, map_pow, ← hu, pow_succ] at he'
      simpa only [Units.val_pow_eq_pow_val, mul_assoc, map_mul, ← hu] using he'.symm
    rw [heq, pow_two]
    exact Ideal.mul_mem_mul y.2 hb
  · apply HomogeneousLocalization.val_injective
    rw [tangentFraction_val, (initialForm_eq_zero_iff I 1 a).mpr h,
      IsLocalization.mk'_zero, HomogeneousLocalization.val_zero]

/-- The chart map sends the class `a/y` of `a ∈ I` to the fraction `ā/ȳ`. -/
theorem stableIdealQuotientToChart_apply
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) (a : I) :
    stableIdealQuotientToChart I y u hu hI hinj 𝒢 h𝒢
      (stableIdealQuotientLinearEquiv I y u hu hI hinj a) =
    tangentFraction I y 𝒢 h𝒢 1 ⟨a.1, by simp⟩ := by
  simp only [stableIdealQuotientToChart, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearEquiv.symm_apply_apply]

/-- **The chart map is surjective.** A fraction `ā/ȳⁿ` of degree zero has `a ∈ Iⁿ = yⁿ⁻¹ I`,
and dividing by `yⁿ⁻¹` produces a preimage in the chart. -/
theorem stableIdealQuotientToChart_surjective
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) :
    Function.Surjective (stableIdealQuotientToChart I y u hu hI hinj 𝒢 h𝒢) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒢
    (initialForm_mem I 𝒢 h𝒢 1 ⟨y.1, by simp⟩) z
  obtain ⟨a, rfl⟩ := exists_initialForm_of_mem I 𝒢 h𝒢 n (by simpa using ha)
  show ∃ b, stableIdealQuotientToChart I y u hu hI hinj 𝒢 h𝒢 b =
    tangentFraction I y 𝒢 h𝒢 n a
  cases n with
  | zero =>
    refine ⟨stableIdealQuotientLinearEquiv I y u hu hI hinj
      ⟨y.1 * a.1, I.mul_mem_right _ y.2⟩, ?_⟩
    rw [stableIdealQuotientToChart_apply]
    apply tangentFraction_eq_of_mul_eq
    simp
  | succ n =>
    obtain ⟨b, hb, he⟩ := exists_eq_pow_mul_of_mem_pow_succ I y.1 hI n a.2
    refine ⟨stableIdealQuotientLinearEquiv I y u hu hI hinj ⟨b, hb⟩, ?_⟩
    rw [stableIdealQuotientToChart_apply]
    apply tangentFraction_eq_of_mul_eq
    show y.1 ^ 1 * a.1 = y.1 ^ (n + 1) * b
    rw [← he]
    ring

/-- **The kernel of the chart map is the closed fibre ideal `I R[I/y]`.** -/
theorem stableIdealQuotientToChart_ker
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) :
    RingHom.ker (stableIdealQuotientToChart I y u hu hI hinj 𝒢 h𝒢) =
      I.map (algebraMap R (stableIdealQuotient I y u hu hI)) := by
  ext b
  obtain ⟨a, rfl⟩ := (stableIdealQuotientLinearEquiv I y u hu hI hinj).surjective b
  rw [RingHom.mem_ker, stableIdealQuotientToChart_apply,
    tangentFraction_one_eq_zero_iff I y u hu hI hinj 𝒢 h𝒢]
  conv_rhs => rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [← stableIdealQuotientCotangentEquiv_toCotangent I y u hu hI hinj,
    LinearEquiv.map_eq_zero_iff]
  exact (I.toCotangent_eq_zero a).symm

/-- **The closed fibre of the affine blow-up chart `R[I/y]` is the degree-zero part of
`G_I(R)` localized away from `ȳ`.** -/
noncomputable def stableIdealQuotientFibreEquivChart
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (hinj : Function.Injective (algebraMap R Q))
    (𝒢 : ℕ → AddSubgroup (gradedRing I)) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := R) I i) n)) :
    (stableIdealQuotient I y u hu hI ⧸
      I.map (algebraMap R (stableIdealQuotient I y u hu hI))) ≃+*
        HomogeneousLocalization.Away 𝒢
          (initialForm I 1 ⟨y.1, by simp⟩) :=
  (Ideal.quotientEquiv _ _ (RingEquiv.refl _)
    (by rw [stableIdealQuotientToChart_ker I y u hu hI hinj 𝒢 h𝒢]; exact (Ideal.map_id _).symm)).trans
    ((stableIdealQuotientToChart I y u hu hI hinj 𝒢 h𝒢).quotientKerEquivOfSurjective
      (stableIdealQuotientToChart_surjective I y u hu hI hinj 𝒢 h𝒢))

/-- **The quadratic algebra of a node is the affine chart `D₊(ȳ)` of its projectivized
tangent cone.** The blow-up chart `A[x/y]` is the normalization, its closed fibre is the
quadratic algebra, and that closed fibre is the chart of `Proj`. -/
theorem normalizationFibreEquivChart
    (hA : IsNodalAlgebra k A)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A))
      (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A) (ha : residue A a ≠ 0)
    (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hrelation : a * x.1 ^ 2 + b * x.1 * y.1 + c * y.1 ^ 2 ∈
      (maximalIdeal A) ^ 3)
    (𝒢 : ℕ → AddSubgroup (gradedRing (maximalIdeal A))) [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => piece (M := A) (maximalIdeal A) i) n)) :
    Nonempty (quadraticAlgebra A ≃+*
      HomogeneousLocalization.Away 𝒢
        (initialForm (maximalIdeal A) 1
          ⟨y.1, by simp⟩)) := by
  have hxy := maximalIdeal_eq_span_of_cotangent_basis x y e hx hy
  have hm := maximalIdeal_sq_eq_span_mul_of_quadratic_relation x y hxy a b c
    ((residue_ne_zero_iff_isUnit a).mp ha) hrelation
  have hy0 : y.1 ≠ 0 := by
    intro hz
    apply e.ne_zero ⟨1⟩
    rw [hy, show y = 0 from Subtype.ext hz, map_zero]
  have : IsReduced A := hA.2.1
  have hyr := mem_nonZeroDivisors_of_maximalIdeal_sq_eq_span_mul y.1 hy0 hm
  let Q := FractionRing A
  let u : Qˣ := (IsLocalization.map_units Q (⟨y.1, hyr⟩ : nonZeroDivisors A)).unit
  have hu : (u : Q) = algebraMap A Q y.1 := IsUnit.unit_spec _
  have hm' : maximalIdeal A * maximalIdeal A = Ideal.span {y.1} * maximalIdeal A := by
    simpa only [pow_two] using hm
  have hinj : Function.Injective (algebraMap A Q) := IsFractionRing.injective A Q
  let B := stableIdealQuotient (maximalIdeal A) y u hu hm'
  let J := (maximalIdeal A).map (algebraMap A B)
  let : Algebra (ResidueField A) (B ⧸ J) := residueFieldAlgebraQuotient
  obtain ⟨eB⟩ := stableIdealQuotient_fibre_equiv_adjoinRoot x y u hu hm' hinj
    e hx hy a b c ha hrelation
  have : IsReduced (AdjoinRoot (Polynomial.C (residue A a) * Polynomial.X ^ 2 +
    Polynomial.C (residue A b) * Polynomial.X + Polynomial.C (residue A c))) :=
    isReduced_adjoinRoot_quadratic _ _ _
      (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using hdisc)
  have hrad : (Ideal.span {algebraMap A B y.1}).IsRadical := by
    rw [← stableIdealQuotient_map_eq_span (maximalIdeal A) y u hu hm' hinj]
    exact (Ideal.isRadical_iff_quotient_reduced J).mpr (isReduced_of_injective eB eB.injective)
  have : Module.Finite A B := stableIdealQuotient_finite _ _ _ _ _
    (maximalIdeal A).fg_of_isNoetherianRing
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_maximalIdeal_sq_le_span y
    (hm.le.trans Ideal.mul_le_left)
  let eN : B ≃ₐ[A] integralClosure A Q :=
    Subalgebra.equivOfEq B _ (eq_integralClosure_of_finite_of_radical_span B y hyr hrad)
  let eF : (B ⧸ J) ≃ₐ[A]
      quadraticAlgebra A :=
    Ideal.quotientEquivAlg J _ eN (by
      dsimp only [J]
      rw [Ideal.map_map]
      congr 1)
  exact ⟨eF.toRingEquiv.symm.trans
    (stableIdealQuotientFibreEquivChart (maximalIdeal A) y u hu hm' hinj 𝒢 h𝒢)⟩

end

/-- The projectivized associated graded ring at a node is the spectrum of its normalization
fibre. The grading is the one by the powers of the maximal ideal. -/
@[stacks 0CBT "three_descriptions"]
public theorem proj_associatedGraded_iso_quadraticAlgebraSpec
    (hA : IsNodalAlgebra k A)
    (𝒢 : ℕ → AddSubgroup (AssociatedGraded.gradedRing (maximalIdeal A)))
    [GradedRing 𝒢]
    (h𝒢 : ∀ n, 𝒢 n = AddMonoidHom.range
      (DirectSum.of (fun i => AssociatedGraded.piece (M := A) (maximalIdeal A) i) n)) :
    Nonempty (Proj 𝒢 ≅ Spec (.of
      (quadraticAlgebra A))) := by
  obtain ⟨x, y, e, a, b, c, hx, hy, ha, hd, hr⟩ :=
    exists_nodalQuadraticRelation_nonzero k A hA
  obtain ⟨eF⟩ := normalizationFibreEquivChart k A hA x y e hx hy a b c ha hd hr 𝒢 h𝒢
  let f := initialForm (maximalIdeal A) 1
    (⟨y.1, by simp⟩ : ↥((maximalIdeal A) ^ 1))
  have hf : f ∈ 𝒢 1 := initialForm_mem (maximalIdeal A) 𝒢 h𝒢 1 _
  have hm' : maximalIdeal A * maximalIdeal A = Ideal.span {y.1} * maximalIdeal A := by
    simpa only [pow_two] using maximalIdeal_sq_eq_span_mul_of_quadratic_relation x y
      (maximalIdeal_eq_span_of_cotangent_basis x y e hx hy) a b c
      ((residue_ne_zero_iff_isUnit a).mp ha) hr
  exact ⟨(Scheme.topIso _).symm ≪≫
    (Scheme.isoOfEq _ (basicOpen_initialForm_eq_top (maximalIdeal A) y hm' 𝒢 h𝒢)).symm ≪≫
    Proj.basicOpenIsoSpec 𝒢 f hf (by decide) ≪≫
    Scheme.Spec.mapIso eF.toCommRingCatIso.op⟩

end Stacks.Curves

end
