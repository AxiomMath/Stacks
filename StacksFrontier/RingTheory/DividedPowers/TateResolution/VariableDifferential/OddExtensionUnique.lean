module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedDerivation

/-!
# Differentials on a one-variable extension

Let `𝒜` be a strictly graded-commutative nonnegative grading of an algebra `A`, carrying a
differential `dA` that lowers degrees by one and divided powers `γ` on its positive even part
compatible with `dA`.  Adjoining to `A` one variable `T` of positive degree `d` produces a new
graded algebra: for odd `d` the square-zero extension `A⟨T⟩ = A ⊕ AT`, and for even `d` the
divided-power polynomial algebra with the symbols `T⁽ⁿ⁾`.  This file shows that a cycle `f` of
degree `d - 1` in `A` determines exactly one differential on the extension which restricts to
`dA` on `A`, sends the new generator to `f`, and is again a divided-power differential graded
algebra.

In both cases the differential is written down explicitly.  For an odd variable an element of
`A ⊕ AT` is `a + bT` and the formula is `d (a + bT) = dA a + ε(b) f + (dA b) T`, with the sign
`ε` supplied by the grading-sign automorphism; for an even variable an element is a finite sum
`∑ aₙ T⁽ⁿ⁾` and the formula is `d (∑ aₙ T⁽ⁿ⁾) = ∑ (dA aₙ) T⁽ⁿ⁾ + ∑ (ε(aₙ) f) T⁽ⁿ⁻¹⁾`, which is
the expected `d T⁽ⁿ⁾ = f T⁽ⁿ⁻¹⁾` together with the Leibniz rule.  Uniqueness in each case comes
from the Leibniz rule: the two prescribed values determine the differential on the coefficients
and on the powers of the generator, and those span the extension.

## Implementation notes

The Koszul sign rule is applied through the grading-sign ring automorphism `signRingHom 𝒜 q`,
which multiplies the degree-`m` piece by `(-1) ^ (q * m)`, rather than by case distinction on
the parity of each homogeneous degree.  This keeps the formula for the differential a single
expression valid on all of `A` instead of only on homogeneous elements: `signRingHom` is a ring
homomorphism, so the twisted terms `signRingHom 𝒜 d b * f` are additive in `b` by construction
and the differential can be assembled directly as an `R`-linear map on the whole extension.  For
the odd variable this is moreover the same automorphism that twists the right action on the
square-zero summand, so the differential and the multiplication of `A⟨T⟩` are described by one
sign convention.

The Leibniz rule and the compatibility with divided powers are proved by reduction to
homogeneous elements.  Both statements carry a sign `(-1) ^ i` indexed by the degree of the left
factor, so as stated they are not additive in that factor; they become additive only once the
degree is fixed.  The arguments therefore run by induction over the direct-sum decomposition
(`DirectSum.Decomposition.inductionOn`, or `EvenVariableAlgebra.homogeneous_induction_on` for a
fixed degree of the extension), reducing to a pair of homogeneous elements where the sign is a
constant and the rule for `A` applies.  The sign-free consequences used along the way, such as
the commutation of even elements with everything and the Leibniz rule in the form
`dA (a * b) = dA a * b + signRingHom 𝒜 1 a * dA b`, are recorded separately so that the
homogeneous case is the only place a parity case distinction appears.

## References

* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
-/

@[expose] public section

namespace DividedPowers.TateResolution

attribute [local implicit_reducible] TwistedModule

universe u v

/-- The differential on coefficient pairs `(a, b)` of `a + bT`, sending it to
`(dA a + signRingHom 𝒜 d b * f, dA b)`. -/
noncomputable def oddCoefficientDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (d : ℕ) (f : A) : A × A →ₗ[R] A × A where
  toFun x := (dA x.1 + signRingHom 𝒜 d x.2 * f, dA x.2)
  map_add' x y := by
    ext <;> simp [map_add, add_mul, add_left_comm, add_assoc]
  map_smul' r x := by
    change (dA (r • x.1) + signRingHom 𝒜 d (r • x.2) * f, dA (r • x.2)) = _
    simp only [map_smul]
    have hs : signRingHom 𝒜 d (r • x.2) = r • signRingHom 𝒜 d x.2 := by
      calc
        signRingHom 𝒜 d (r • x.2) =
            signRingHom 𝒜 d (algebraMap R A r * x.2) := by rw [Algebra.smul_def]
        _ = signRingHom 𝒜 d (algebraMap R A r) * signRingHom 𝒜 d x.2 := map_mul _ _ _
        _ = algebraMap R A r * signRingHom 𝒜 d x.2 := by
          rw [signRingHom_of_mem 𝒜 d 0 (SetLike.algebraMap_mem_graded 𝒜 r)]
          simp
        _ = r • signRingHom 𝒜 d x.2 := (Algebra.smul_def _ _).symm
    rw [hs]
    simp [smul_add]

/-- The differential on the odd-variable extension `A⟨T⟩` extending `dA` and sending `T` to
`f`: in coefficients it is `a + bT ↦ dA a + signRingHom 𝒜 d b * f + (dA b) T`. -/
noncomputable def oddExtensionDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (d : ℕ) (f : A) :
    OddVariableExtension 𝒜 d →ₗ[R] OddVariableExtension 𝒜 d :=
  (OddVariableExtension.coefficients 𝒜 d).symm.toLinearMap.comp
    ((oddCoefficientDifferential 𝒜 dA d f).comp
      (OddVariableExtension.coefficients 𝒜 d).toLinearMap)

theorem oddExtensionDifferential_coefficients
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (d : ℕ) (f : A)
    (x : OddVariableExtension 𝒜 d) :
    OddVariableExtension.coefficients 𝒜 d
      (oddExtensionDifferential 𝒜 dA d f x) =
      (dA (OddVariableExtension.coefficients 𝒜 d x).1 +
        signRingHom 𝒜 d (OddVariableExtension.coefficients 𝒜 d x).2 * f,
       dA (OddVariableExtension.coefficients 𝒜 d x).2) := by
  rfl

/-- `oddExtensionDifferential` restricts to `dA` on the image of `A`. -/
public theorem oddExtensionDifferential_inclusion
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (d : ℕ) (f a : A) :
    oddExtensionDifferential 𝒜 dA d f (OddVariableExtension.inclusion 𝒜 d a) =
      OddVariableExtension.inclusion 𝒜 d (dA a) := by
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  rw [oddExtensionDifferential_coefficients, OddVariableExtension.coefficients_inclusion,
    OddVariableExtension.coefficients_inclusion]
  simp

/-- `oddExtensionDifferential` sends the adjoined variable `T` to `f`. -/
public theorem oddExtensionDifferential_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA] (d : ℕ) (f : A) :
    oddExtensionDifferential 𝒜 dA d f (OddVariableExtension.generator 𝒜 d) =
      OddVariableExtension.inclusion 𝒜 d f := by
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  have h1 : (1 : A) ∈ 𝒜 0 := SetLike.one_mem_graded 𝒜
  have hd1 : dA (1 : A) = 0 := IsGradedDerivation.d_grade_zero h1
  rw [oddExtensionDifferential_coefficients, OddVariableExtension.coefficients_generator,
    OddVariableExtension.coefficients_inclusion]
  simp [hd1]

/-- The coefficient pair of `a T` in `A⟨T⟩` is `(0, a)`. -/
private theorem coefficients_inclusion_mul_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ) (a : A) :
    OddVariableExtension.coefficients 𝒜 d
      (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) = (0, a) := by
  have hprod : OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d =
      TrivSqZeroExt.inr (show TwistedModule 𝒜 d from a) := by
    simp [OddVariableExtension.inclusion, OddVariableExtension.generator,
      TrivSqZeroExt.inl_mul_inr]
  rw [hprod]
  rfl

/-- For odd `q`, `signRingHom 𝒜 q` multiplies a degree-`k` element by `(-1) ^ k`. -/
private theorem signRingHom_of_mem_of_odd
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {q : ℕ} (hq : Odd q) {k : ℕ} {a : A}
    (ha : a ∈ 𝒜 k) :
    signRingHom 𝒜 q a = (-1 : R) ^ k • a := by
  rw [signRingHom_of_mem 𝒜 q k ha, pow_mul, hq.neg_one_pow]

private theorem oddExtensionDifferential_inclusion_mul_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd_odd : Odd d) (f a : A) {k : ℕ} (ha : a ∈ 𝒜 k) :
    oddExtensionDifferential 𝒜 dA d f
        (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) =
    oddExtensionDifferential 𝒜 dA d f (OddVariableExtension.inclusion 𝒜 d a) *
          OddVariableExtension.generator 𝒜 d +
        (-1 : R) ^ k •
          (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.inclusion 𝒜 d f) := by
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  rw [oddExtensionDifferential_coefficients, coefficients_inclusion_mul_generator, map_add,
    map_smul, OddVariableExtension.coefficients_mul, oddExtensionDifferential_inclusion,
    OddVariableExtension.coefficients_inclusion, OddVariableExtension.coefficients_generator,
    OddVariableExtension.coefficients_mul, OddVariableExtension.coefficients_inclusion,
    OddVariableExtension.coefficients_inclusion]
  simp [signRingHom_of_mem_of_odd 𝒜 hd_odd ha]

theorem oddExtensionDifferential_inclusion_mul_generator_any
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (d : ℕ) (f a : A) :
    oddExtensionDifferential 𝒜 dA d f
        (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) =
      OddVariableExtension.inclusion 𝒜 d (signRingHom 𝒜 d a * f) +
        OddVariableExtension.inclusion 𝒜 d (dA a) * OddVariableExtension.generator 𝒜 d := by
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  rw [oddExtensionDifferential_coefficients, coefficients_inclusion_mul_generator, map_add,
    OddVariableExtension.coefficients_inclusion, coefficients_inclusion_mul_generator]
  simp

private theorem oddExtensionDifferential_unique_on_inclusion_mul_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd_odd : Odd d) (f : A)
    (dExt : OddVariableExtension 𝒜 d →ₗ[R] OddVariableExtension 𝒜 d)
    [IsGradedDerivation (OddVariableExtension.grade 𝒜 d) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 d x) =
      OddVariableExtension.inclusion 𝒜 d (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 d) =
      OddVariableExtension.inclusion 𝒜 d f)
    {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    dExt (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) =
      oddExtensionDifferential 𝒜 dA d f
        (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) := by
  calc
    dExt (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) =
        dExt (OddVariableExtension.inclusion 𝒜 d a) * OddVariableExtension.generator 𝒜 d +
          (-1 : R) ^ k •
            (OddVariableExtension.inclusion 𝒜 d a *
              dExt (OddVariableExtension.generator 𝒜 d)) := by
      rw [IsGradedDerivation.leibniz
        (𝒜 := OddVariableExtension.grade 𝒜 d) (d := dExt)
        (OddVariableExtension.inclusion_mem_grade 𝒜 d k ha)
        (OddVariableExtension.generator_mem_grade 𝒜 d)]
    _ = oddExtensionDifferential 𝒜 dA d f
          (OddVariableExtension.inclusion 𝒜 d a) * OddVariableExtension.generator 𝒜 d +
          (-1 : R) ^ k •
            (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.inclusion 𝒜 d f) := by
      rw [hdExt, hT, oddExtensionDifferential_inclusion]
    _ = oddExtensionDifferential 𝒜 dA d f
          (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) :=
      (oddExtensionDifferential_inclusion_mul_generator
        𝒜 dA d hd_odd f a ha).symm

theorem oddExtensionDifferential_unique
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd_odd : Odd d) (f : A)
    (dExt : OddVariableExtension 𝒜 d →ₗ[R] OddVariableExtension 𝒜 d)
    [IsGradedDerivation (OddVariableExtension.grade 𝒜 d) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 d x) =
      OddVariableExtension.inclusion 𝒜 d (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 d) =
      OddVariableExtension.inclusion 𝒜 d f) :
    dExt = oddExtensionDifferential 𝒜 dA d f := by
  have hmul (a : A) :
      dExt (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) =
        oddExtensionDifferential 𝒜 dA d f
          (OddVariableExtension.inclusion 𝒜 d a * OddVariableExtension.generator 𝒜 d) := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous a =>
        exact oddExtensionDifferential_unique_on_inclusion_mul_generator
          𝒜 dA d hd_odd f dExt hdExt hT a.property
    | add a b ha hb =>
        simp [map_add, add_mul, ha, hb]
  apply LinearMap.ext
  intro x
  have hrepr := OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator
    𝒜 d x
  calc
    dExt x = dExt (OddVariableExtension.inclusion 𝒜 d x.fst +
        OddVariableExtension.inclusion 𝒜 d x.snd * OddVariableExtension.generator 𝒜 d) :=
      congrArg dExt hrepr.symm
    _ = dExt (OddVariableExtension.inclusion 𝒜 d x.fst) +
        dExt (OddVariableExtension.inclusion 𝒜 d x.snd * OddVariableExtension.generator 𝒜 d) :=
      map_add dExt _ _
    _ = oddExtensionDifferential 𝒜 dA d f (OddVariableExtension.inclusion 𝒜 d x.fst) +
        oddExtensionDifferential 𝒜 dA d f
          (OddVariableExtension.inclusion 𝒜 d x.snd * OddVariableExtension.generator 𝒜 d) := by
      rw [hdExt, hmul, oddExtensionDifferential_inclusion]
    _ = oddExtensionDifferential 𝒜 dA d f x := by
      calc
        _ = oddExtensionDifferential 𝒜 dA d f
            (OddVariableExtension.inclusion 𝒜 d x.fst +
              OddVariableExtension.inclusion 𝒜 d x.snd * OddVariableExtension.generator 𝒜 d) :=
          (map_add (oddExtensionDifferential 𝒜 dA d f) _ _).symm
        _ = oddExtensionDifferential 𝒜 dA d f x :=
          congrArg (oddExtensionDifferential 𝒜 dA d f) hrepr

/-- The grading-sign ring homomorphism `signRingHom 𝒜 q` as an `R`-linear map. -/
noncomputable def gradingSignLinearMap
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q : ℕ) : A →ₗ[R] A where
  toFun := signRingHom 𝒜 q
  map_add' := map_add _
  map_smul' r a := by
    calc
      signRingHom 𝒜 q (r • a) = signRingHom 𝒜 q (algebraMap R A r * a) := by
        rw [Algebra.smul_def]
      _ = signRingHom 𝒜 q (algebraMap R A r) * signRingHom 𝒜 q a := map_mul _ _ _
      _ = algebraMap R A r * signRingHom 𝒜 q a := by
        rw [signRingHom_of_mem 𝒜 q 0 (SetLike.algebraMap_mem_graded 𝒜 r)]
        simp
      _ = r • signRingHom 𝒜 q a := (Algebra.smul_def _ _).symm

theorem gradingSign_anticommutes_differential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA] (a : A) :
    signRingHom 𝒜 1 (dA a) + dA (signRingHom 𝒜 1 a) = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro m hm
  let x : 𝒜 m := DirectSum.decompose 𝒜 a m
  have hx : (x : A) ∈ 𝒜 m := x.property
  by_cases hm0 : m = 0
  · subst m
    have hdx : dA (x : A) = 0 := IsGradedDerivation.d_grade_zero hx
    simp [x, hdx, signRingHom_of_mem 𝒜 1 0 hx]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
    have hdx : dA (x : A) ∈ 𝒜 (m - 1) := by
      apply IsGradedDerivation.d_mem
      simp [hsub]
    rw [signRingHom_of_mem 𝒜 1 (m - 1) hdx,
      signRingHom_of_mem 𝒜 1 m hx, map_smul]
    have hsign : (-1 : R) ^ (m - 1) + (-1 : R) ^ m = 0 := by
      calc
        _ = (-1 : R) ^ (m - 1) + (-1 : R) ^ ((m - 1) + 1) := by rw [hsub]
        _ = 0 := by rw [pow_succ]; ring
    simp only [one_mul]
    rw [← add_smul, hsign, zero_smul]

theorem gradingSign_eq_odd
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q : ℕ) (hq : Odd q) (a : A) :
    signRingHom 𝒜 q a = signRingHom 𝒜 1 a := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  let x : 𝒜 m := DirectSum.decompose 𝒜 a m
  have hx : (x : A) ∈ 𝒜 m := x.property
  rw [signRingHom_of_mem_of_odd 𝒜 hq hx, signRingHom_of_mem_of_odd 𝒜 odd_one hx]

theorem gradingSignOdd_anticommutes_differential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (q : ℕ) (hq : Odd q) (a : A) :
    signRingHom 𝒜 q (dA a) + dA (signRingHom 𝒜 q a) = 0 := by
  rw [gradingSign_eq_odd 𝒜 q hq (dA a), gradingSign_eq_odd 𝒜 q hq a]
  exact gradingSign_anticommutes_differential 𝒜 dA a

theorem differential_mul_cycle
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    {k : ℕ} {f : A} (hf : f ∈ 𝒜 k) (hdf : dA f = 0) (a : A) :
    dA (a * f) = dA a * f := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [Finset.sum_mul]
  simp only [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  let x : 𝒜 m := DirectSum.decompose 𝒜 a m
  have hx : (x : A) ∈ 𝒜 m := x.property
  rw [IsGradedDerivation.leibniz hx hf, hdf]
  simp [x]

theorem differential_mul_sign
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA] (a b : A) :
    dA (a * b) = dA a * b + signRingHom 𝒜 1 a * dA b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | homogeneous b =>
          rw [signRingHom_of_mem 𝒜 1 _ a.property]
          simpa [smul_eq_mul] using
            (IsGradedDerivation.leibniz (𝒜 := 𝒜) (d := dA)
              a.property b.property)
      | add b c hb hc =>
          simp only [mul_add, map_add, hb, hc]
          abel
  | add a b ha hb =>
      simp only [add_mul, map_add, (signRingHom 𝒜 1).map_add, ha, hb]
      abel

private theorem signRingHom_eq_self_evenPartEarly
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {a : A} (ha : a ∈ evenPart 𝒜) :
    signRingHom 𝒜 1 a = a := by
  classical
  change a ∈ ⨆ e : ℕ, 𝒜 (2 * e) at ha
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e)) a).mp ha
  rw [← hfsum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [signRingHom_of_mem 𝒜 1 (2 * e) (hf e)]
  simp

private theorem differential_evenPart_oddPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    {a : A} (ha : a ∈ evenPart 𝒜) :
    dA a ∈ oddPart 𝒜 := by
  classical
  change a ∈ ⨆ e : ℕ, 𝒜 (2 * e) at ha
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e)) a).mp ha
  rw [oddPart, ← hfsum, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  by_cases he0 : e = 0
  · subst e
    have hz := IsGradedDerivation.d_grade_zero (𝒜 := 𝒜) (d := dA) (hf 0)
    simp [hz]
  · have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have hidx : 2 * e = (2 * (e - 1) + 1) + 1 := by omega
    have hfe := hf e
    rw [hidx] at hfe
    have hde := IsGradedDerivation.d_mem (𝒜 := 𝒜) (d := dA) hfe
    exact Submodule.mem_iSup_of_mem (e - 1) hde

theorem evenPart_mul_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {a b : A} (ha : a ∈ evenPart 𝒜)
    (hb : b ∈ evenPart 𝒜) : a * b ∈ evenPart 𝒜 := by
  change a ∈ ⨆ i : ℕ, 𝒜 (2 * i) at ha
  change b ∈ ⨆ j : ℕ, 𝒜 (2 * j) at hb
  rw [Submodule.iSup_eq_span] at ha hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
          exact Submodule.mem_iSup_of_mem (i + j) (by
            have hdeg : 2 * i + 2 * j = 2 * (i + j) := by omega
            simpa only [hdeg] using SetLike.mul_mem_graded hi hj)
      | zero => simp
      | add b c hb hc ihb ihc =>
          simpa only [mul_add] using (evenPart 𝒜).add_mem ihb ihc
      | smul r b hb ih =>
          simpa only [mul_smul_comm] using (evenPart 𝒜).smul_mem r ih
  | zero => simp
  | add a c ha hc ih ihc =>
      simpa only [add_mul] using (evenPart 𝒜).add_mem ih ihc
  | smul r a ha ih =>
      simpa only [smul_mul_assoc] using (evenPart 𝒜).smul_mem r ih

private theorem even_homogeneous_commute
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {i j : ℕ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) (hi : Even i) :
    a * b = b * a := by
  have hp : Even (i * j) := hi.mul_right j
  simpa [smul_eq_mul, hp.neg_one_pow] using
    (IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) ha hb)

theorem even_element_commute
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i) (b : A) :
    a * b = b * a := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous b => exact even_homogeneous_commute 𝒜 ha b.property hi
  | add b c hb hc => simp [hb, hc, add_mul, mul_add]

theorem differential_pow_even
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    {k : ℕ} {a : A} (ha : a ∈ 𝒜 (2 * k)) (n : ℕ) :
    dA (a ^ n) = n • (a ^ (n - 1) * dA a) := by
  induction n with
  | zero =>
      have hda1 : dA (1 : A) = 0 :=
        IsGradedDerivation.d_grade_zero (SetLike.one_mem_graded 𝒜)
      simp [hda1]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp only [Nat.zero_add, pow_one, Nat.succ_sub_one, one_smul,
          pow_zero, one_mul]
      · have heven : a ^ n ∈ evenPart 𝒜 :=
          evenPart_pow_mem 𝒜 (Submodule.mem_iSup_of_mem k ha) n
        have hdaComm : dA a * a = a * dA a :=
          (even_element_commute 𝒜 ha ⟨k, by ring⟩ (dA a)).symm
        rw [pow_succ, differential_mul_sign 𝒜 dA,
          signRingHom_eq_self_evenPartEarly 𝒜 heven, ih]
        have hterm : (a ^ (n - 1) * dA a) * a = a ^ n * dA a := by
          calc
            (a ^ (n - 1) * dA a) * a = a ^ (n - 1) * (dA a * a) := by ac_rfl
            _ = a ^ (n - 1) * (a * dA a) := by rw [hdaComm]
            _ = (a ^ (n - 1) * a) * dA a := by rw [← mul_assoc]
            _ = a ^ ((n - 1) + 1) * dA a := by rw [← pow_succ]
            _ = a ^ n * dA a := by
              rw [show (n - 1) + 1 = n by omega]
        rw [smul_mul_assoc, hterm, succ_nsmul, show n + 1 - 1 = n by omega]

end DividedPowers.TateResolution
