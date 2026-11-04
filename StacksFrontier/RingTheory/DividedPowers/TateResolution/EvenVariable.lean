module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-!
# Adjoining an even divided-power variable

Let `A` be a strictly graded-commutative graded algebra and let `d` be a positive even integer.
This file constructs the algebra obtained from `A` by adjoining one divided-power variable of
degree `d`.  Its elements are the finite sums `∑ aₙ T⁽ⁿ⁾` with `aₙ ∈ A`, realized as the finitely
supported families `ℕ →₀ A`, and its multiplication is determined by the divided-power rule
`T⁽ⁿ⁾ T⁽ᵐ⁾ = (n + m).choose n • T⁽ⁿ⁺ᵐ⁾`.

When `A` carries the grading `𝒜` and the new variable is given degree `d`, the degree-`m` piece of
the result is `𝒜 m ⊕ 𝒜 (m - d) T ⊕ 𝒜 (m - 2d) T⁽²⁾ ⊕ ⋯`; coefficients beyond the displayed finite
sum are forced to vanish.  These pieces form an internal grading, and they inherit strict graded
commutativity as soon as `d` is even, since then no new sign can appear.

The underlying coefficient algebra does not depend on the divided powers of `A`, and the grading is
defined for every natural degree, so the constructions here apply in particular to every positive
even degree of the source. Evenness enters only through the strict-commutativity instance, where it
is supplied as `Fact (Even d)`.

## Main definitions

* `DividedPowers.TateResolution.EvenVariableAlgebra` — the algebra of finite divided-power
  polynomials in one variable over `A`.
* `DividedPowers.TateResolution.EvenVariableAlgebra.monomial` — the divided-power monomial
  `a T⁽ⁿ⁾`.
* `DividedPowers.TateResolution.EvenVariableAlgebra.mul` — the binomially weighted product.
* `DividedPowers.TateResolution.EvenVariableAlgebra.grade` — the homogeneous pieces when the
  variable has degree `d`.

## Main results

* `DividedPowers.TateResolution.EvenVariableAlgebra.monomial_mul_monomial` — the defining
  multiplication rule for divided-power monomials.
* `DividedPowers.TateResolution.EvenVariableAlgebra.mem_grade_iff` — the homogeneous pieces are
  cut out coefficientwise.
* `DividedPowers.TateResolution.EvenVariableAlgebra.gradedAlgebra` — the internal direct-sum
  grading, hence Mathlib's `DirectSum.decompose` API.
* `DividedPowers.TateResolution.EvenVariableAlgebra.strictlyGradedComm` — strict graded
  commutativity for an even variable, including vanishing odd squares.

## References

* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

/-- The algebra of finite divided-power polynomials in one even variable over `A`.

The coefficient at `n` is the coefficient of the formal symbol `T⁽ⁿ⁾`. -/
@[ext, stacks 09PI "even_variable_algebra"]
public structure EvenVariableAlgebra (A : Type v) [Ring A] where
  /-- The finitely supported family of coefficients. -/
  coeff : ℕ →₀ A

namespace EvenVariableAlgebra

open scoped BigOperators DirectSum

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

noncomputable section

/-- The equivalence with finitely supported coefficient families. -/
public def coeffEquiv : EvenVariableAlgebra A ≃ (ℕ →₀ A) where
  toFun := coeff
  invFun := EvenVariableAlgebra.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive group structure transported from `ℕ →₀ A` along `coeffEquiv`. -/
public instance : AddCommGroup (EvenVariableAlgebra A) :=
  fast_instance% coeffEquiv.addCommGroup

/-- The divided-power monomial `a T⁽ⁿ⁾`. -/
public def monomial (n : ℕ) (a : A) : EvenVariableAlgebra A :=
  ⟨Finsupp.single n a⟩

/-- The coefficient family of `a T⁽ⁿ⁾` is `Finsupp.single n a`. -/
@[simp] public theorem coeff_monomial (n : ℕ) (a : A) :
    (monomial n a).coeff = Finsupp.single n a := rfl

/-- Each monomial constructor is injective on coefficients. -/
public theorem monomial_injective (n : ℕ) : Function.Injective (monomial (A := A) n) := by
  intro a b h
  simpa using congrArg (fun x : EvenVariableAlgebra A ↦ x.coeff n) h

/-- The coefficient family of `0` is `0`. -/
@[simp] public theorem coeff_zero : (0 : EvenVariableAlgebra A).coeff = 0 := rfl

/-- Coefficients of a sum are the sums of coefficients. -/
@[simp] public theorem coeff_add (x y : EvenVariableAlgebra A) :
    (x + y).coeff = x.coeff + y.coeff := rfl

/-- Coefficients of a negation are the negated coefficients. -/
@[simp] public theorem coeff_neg (x : EvenVariableAlgebra A) :
    (-x).coeff = -x.coeff := rfl

/-- The monomial with zero coefficient is zero. -/
@[simp] public theorem monomial_zero (n : ℕ) : monomial n (0 : A) = 0 := by
  ext
  simp [monomial]

/-- The monomial `(a + b) T⁽ⁿ⁾` is `a T⁽ⁿ⁾ + b T⁽ⁿ⁾`. -/
@[simp] public theorem monomial_add (n : ℕ) (a b : A) :
    monomial n (a + b) = monomial n a + monomial n b := by
  ext
  simp [monomial, Finsupp.single_add]

/-- Induction on finite sums of divided-power monomials. -/
@[elab_as_elim]
public theorem induction_on {P : EvenVariableAlgebra A → Prop} (x : EvenVariableAlgebra A)
    (zero : P 0) (add : ∀ n a y, P y → P (monomial n a + y)) : P x := by
  obtain ⟨x⟩ := x
  induction x using Finsupp.induction with
  | zero => exact zero
  | single_add n a f _ _ hf => exact add n a ⟨f⟩ hf

/-- The binomially weighted convolution product. -/
@[stacks 09PI "even_variable_algebra"]
public def mul (x y : EvenVariableAlgebra A) : EvenVariableAlgebra A :=
  ⟨x.coeff.sum fun n a ↦ y.coeff.sum fun m b ↦
    Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))⟩

/-- Multiplication is the binomially weighted convolution product `mul`. -/
public instance : Mul (EvenVariableAlgebra A) := ⟨mul⟩

/-- The unit is the constant monomial `1 T⁽⁰⁾`. -/
public instance : One (EvenVariableAlgebra A) := ⟨monomial 0 1⟩

/-- The divided-power rule `a T⁽ⁿ⁾ * b T⁽ᵐ⁾ = (n + m).choose n • (a * b) T⁽ⁿ⁺ᵐ⁾`. -/
@[simp] public theorem monomial_mul_monomial (n m : ℕ) (a b : A) :
    monomial n a * monomial m b =
      monomial (n + m) (Nat.choose (n + m) n • (a * b)) := by
  classical
  apply EvenVariableAlgebra.ext
  change
    (Finsupp.single n a).sum (fun n a ↦
      (Finsupp.single m b).sum fun m b ↦
        Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))) =
      Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))
  simp

private theorem choose_assoc (n m k : ℕ) :
    Nat.choose (n + m) n * Nat.choose (n + m + k) (n + m) =
      Nat.choose (m + k) m * Nat.choose (n + (m + k)) n := by
  simpa [Nat.add_sub_cancel_left, add_assoc, mul_comm] using
    (Nat.choose_mul (n := n + m + k) (k := n + m) (s := n) (Nat.le_add_right n m))

/-- Multiplication is biadditive and absorbs zero. -/
public instance : NonUnitalNonAssocRing (EvenVariableAlgebra A) where
  zero_mul x := by
    apply EvenVariableAlgebra.ext
    simp [HMul.hMul, Mul.mul, mul]
  mul_zero x := by
    apply EvenVariableAlgebra.ext
    simp [HMul.hMul, Mul.mul, mul]
  left_distrib := by
    intro x y z
    apply EvenVariableAlgebra.ext
    classical
    simp only [HMul.hMul, Mul.mul, mul, coeff_add]
    have h (n : ℕ) (a : A) :
        (y.coeff + z.coeff).sum (fun m b ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))) =
          y.coeff.sum (fun m b ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))) +
          z.coeff.sum (fun m b ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))) := by
      apply Finsupp.sum_add_index'
      · intro m
        simp
      · intro m b c
        simp [mul_add, Finsupp.single_add]
    calc
      _ = x.coeff.sum (fun n a ↦
          y.coeff.sum (fun m b ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b))) +
          z.coeff.sum (fun m b ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * b)))) :=
        Finsupp.sum_congr (fun n _ ↦ h n (x.coeff n))
      _ = _ := Finsupp.sum_add
  right_distrib := by
    intro x y z
    apply EvenVariableAlgebra.ext
    classical
    simp only [HMul.hMul, Mul.mul, mul, coeff_add]
    apply Finsupp.sum_add_index'
    · intro n
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro m hm
      change Finsupp.single (n + m) (Nat.choose (n + m) n • ((0 : A) * z.coeff m)) = 0
      rw [zero_mul, nsmul_zero, Finsupp.single_zero]
    · intro n a b
      calc
        _ = z.coeff.sum (fun m c ↦
            Finsupp.single (n + m) (Nat.choose (n + m) n • (a * c)) +
            Finsupp.single (n + m) (Nat.choose (n + m) n • (b * c))) := by
          apply Finsupp.sum_congr
          intro m hm
          change Finsupp.single (n + m) (Nat.choose (n + m) n • ((a + b) * z.coeff m)) = _
          rw [add_mul, nsmul_add, Finsupp.single_add]
        _ = _ := Finsupp.sum_add

private theorem one_mul_monomial (n : ℕ) (a : A) :
    (1 : EvenVariableAlgebra A) * monomial n a = monomial n a := by
  show monomial 0 1 * monomial n a = _
  simp

private theorem monomial_mul_one (n : ℕ) (a : A) :
    monomial n a * (1 : EvenVariableAlgebra A) = monomial n a := by
  show monomial n a * monomial 0 1 = _
  simp

/-- The constant monomial `1` is a two-sided unit. -/
public instance : NonAssocRing (EvenVariableAlgebra A) where
  one_mul := by
    intro x
    induction x using induction_on with
    | zero => exact mul_zero 1
    | add n a y hy => rw [mul_add, one_mul_monomial, hy]
  mul_one := by
    intro x
    induction x using induction_on with
    | zero => exact zero_mul 1
    | add n a y hy => rw [add_mul, monomial_mul_one, hy]

private theorem mul_assoc_monomial (n m k : ℕ) (a b c : A) :
    (monomial n a * monomial m b) * monomial k c =
      monomial n a * (monomial m b * monomial k c) := by
  rw [monomial_mul_monomial, monomial_mul_monomial,
    monomial_mul_monomial, monomial_mul_monomial]
  congr 1
  · simp [add_assoc]
  · simp only [nsmul_eq_mul]
    have hchoose :
        Nat.choose (n + m + k) (n + m) * Nat.choose (n + m) n =
          Nat.choose (n + (m + k)) n * Nat.choose (m + k) m := by
      simpa [mul_comm] using choose_assoc n m k
    have hcast :
        (Nat.choose (n + m + k) (n + m) : A) * (Nat.choose (n + m) n : A) =
          (Nat.choose (n + (m + k)) n : A) * (Nat.choose (m + k) m : A) := by
      simpa only [Nat.cast_mul] using congrArg (fun q : ℕ ↦ (q : A)) hchoose
    rw [← mul_assoc a (Nat.choose (m + k) m : A) (b * c),
      ← (Nat.cast_commute (Nat.choose (m + k) m) a).eq]
    simp only [← mul_assoc]
    rw [hcast]

private theorem mul_assoc_two_monomials (n m : ℕ) (a b : A)
    (z : EvenVariableAlgebra A) :
    (monomial n a * monomial m b) * z = monomial n a * (monomial m b * z) := by
  induction z using induction_on with
  | zero => rw [mul_zero, mul_zero, mul_zero]
  | add k c z hz =>
    rw [mul_add, mul_add, mul_add, hz, mul_assoc_monomial]

private theorem mul_assoc_left_monomial (n : ℕ) (a : A) (y z : EvenVariableAlgebra A) :
    (monomial n a * y) * z = monomial n a * (y * z) := by
  induction y using induction_on with
  | zero => rw [mul_zero, zero_mul, mul_zero]
  | add m b y hy =>
    rw [mul_add, add_mul, add_mul, mul_add, hy, mul_assoc_two_monomials]

/-- Multiplication is associative, so the even variable algebra is a ring. -/
public instance : Ring (EvenVariableAlgebra A) where
  mul_assoc := by
    intro x y z
    induction x using induction_on with
    | zero => exact (zero_mul z).trans (zero_mul (y * z)).symm
    | add n a x hx =>
      rw [add_mul, add_mul]
      rw [add_mul (monomial n a) x (y * z)]
      exact congrArg₂ (fun p q ↦ p + q) (mul_assoc_left_monomial n a y z) hx

/-- The inclusion of the coefficient ring as constant divided-power polynomials. -/
public def coeffEmbedding : A →+* EvenVariableAlgebra A where
  toFun := monomial 0
  map_zero' := monomial_zero 0
  map_one' := rfl
  map_add' := monomial_add 0
  map_mul' a b := by simp

/-- The coefficient inclusion sends `a` to the constant monomial `a T⁽⁰⁾`. -/
@[simp] public theorem coeffEmbedding_apply (a : A) : coeffEmbedding a = monomial 0 a := rfl

/-- The image of a scalar `r : R` under the coefficient inclusion is central. -/
public theorem algebraMap_commutes (r : R) (x : EvenVariableAlgebra A) :
    coeffEmbedding (algebraMap R A r) * x = x * coeffEmbedding (algebraMap R A r) := by
  induction x using induction_on with
  | zero => rw [mul_zero, zero_mul]
  | add n a x hx =>
    rw [mul_add, add_mul, hx]
    simp only [coeffEmbedding_apply, monomial_mul_monomial]
    simp only [zero_add, Nat.choose_zero_right, one_smul, add_zero, Nat.choose_self, add_left_inj]
    rw [Algebra.commutes]

/-- The `R`-algebra structure through the coefficient inclusion `A → EvenVariableAlgebra A`. -/
public noncomputable instance : Algebra R (EvenVariableAlgebra A) :=
  ((coeffEmbedding (A := A)).comp (algebraMap R A)).toAlgebra' algebraMap_commutes

/-- The structure map sends `r` to the constant monomial `algebraMap R A r`. -/
@[simp] public theorem algebraMap_apply (r : R) :
    algebraMap R (EvenVariableAlgebra A) r = monomial 0 (algebraMap R A r) := rfl

/-- The coefficient inclusion as an `R`-algebra homomorphism. -/
@[implicit_reducible]
public def coeffAlgHom : A →ₐ[R] EvenVariableAlgebra A where
  __ := coeffEmbedding
  commutes' _ := rfl

/-- The coefficient algebra homomorphism agrees with `coeffEmbedding`. -/
@[simp] public theorem coeffAlgHom_apply (a : A) :
    coeffAlgHom (R := R) a = coeffEmbedding a := rfl

/-- The coefficient inclusion is injective. -/
public theorem coeffEmbedding_injective : Function.Injective (coeffEmbedding (A := A)) :=
  monomial_injective 0

/-- Scalars act on the coefficient of a monomial: `r • a T⁽ⁿ⁾ = (r • a) T⁽ⁿ⁾`. -/
@[simp] public theorem smul_monomial (r : R) (n : ℕ) (a : A) :
    r • monomial n a = monomial n (r • a) := by
  rw [Algebra.smul_def, algebraMap_apply, monomial_mul_monomial]
  simp [Algebra.smul_def]

/-- Scalars act coefficientwise. -/
@[simp] public theorem coeff_smul (r : R) (x : EvenVariableAlgebra A) :
    (r • x).coeff = r • x.coeff := by
  induction x using induction_on with
  | zero => simp
  | add n a x hx =>
    rw [smul_add, coeff_add, coeff_add, hx, smul_monomial]
    ext k
    simp [monomial]

/-- The degree-`m` piece after adjoining an even variable of degree `d`.

Its coefficient of `T⁽ⁿ⁾` lies in `𝒜 (m - n * d)` when `n * d ≤ m`, and is zero
otherwise. -/
@[stacks 09PI "even_variable_algebra"]
public def grade (𝒜 : ℕ → Submodule R A) (d m : ℕ) :
    Submodule R (EvenVariableAlgebra A) where
  carrier := {x | ∀ n, x.coeff n ∈ if n * d ≤ m then 𝒜 (m - n * d) else ⊥}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro x y hx hy n
    rw [coeff_add, Finsupp.add_apply]
    split_ifs with h
    · have hxn : x.coeff n ∈ 𝒜 (m - n * d) := by simpa [h] using hx n
      have hyn : y.coeff n ∈ 𝒜 (m - n * d) := by simpa [h] using hy n
      exact Submodule.add_mem _ hxn hyn
    · have hxn : x.coeff n = 0 := by simpa [h] using hx n
      have hyn : y.coeff n = 0 := by simpa [h] using hy n
      simp [hxn, hyn]
  smul_mem' := by
    intro r x hx n
    rw [coeff_smul, Finsupp.smul_apply]
    split_ifs with h
    · have hxn : x.coeff n ∈ 𝒜 (m - n * d) := by simpa [h] using hx n
      exact Submodule.smul_mem _ r hxn
    · have hxn : x.coeff n = 0 := by simpa [h] using hx n
      simp [hxn]

/-- Membership in the displayed homogeneous piece is the coefficientwise degree condition. -/
public theorem mem_grade_iff (𝒜 : ℕ → Submodule R A) (d m : ℕ)
    (x : EvenVariableAlgebra A) :
    x ∈ grade 𝒜 d m ↔
      ∀ n, x.coeff n ∈ if n * d ≤ m then 𝒜 (m - n * d) else ⊥ :=
  Iff.rfl

/-- The monomial constructor as a linear map on coefficients. -/
public def monomialLinearMap (n : ℕ) : A →ₗ[R] EvenVariableAlgebra A where
  toFun := monomial n
  map_add' := monomial_add n
  map_smul' r a := (smul_monomial r n a).symm

/-- The linear map `monomialLinearMap n` sends `a` to `a T⁽ⁿ⁾`. -/
@[simp] public theorem monomialLinearMap_apply (n : ℕ) (a : A) :
    monomialLinearMap (R := R) n a = monomial n a := rfl

/-- Expansion in divided-power monomials. -/
public theorem sum_monomial (x : EvenVariableAlgebra A) :
    ∑ n ∈ x.coeff.support, monomial n (x.coeff n) = x := by
  apply EvenVariableAlgebra.ext
  show (show EvenVariableAlgebra A →+ (ℕ →₀ A) from
    { toFun := coeff, map_zero' := coeff_zero, map_add' := coeff_add }) _ = _
  simp only [map_sum]
  exact Finsupp.sum_single x.coeff

/-- The monomial `a T⁽ⁿ⁾` has degree `m` if and only if `a ∈ 𝒜 (m - n * d)` when `n * d ≤ m`,
and `a = 0` otherwise. -/
@[simp] public theorem monomial_mem_grade_iff (𝒜 : ℕ → Submodule R A)
    (d m n : ℕ) (a : A) :
    monomial n a ∈ grade 𝒜 d m ↔
      a ∈ if n * d ≤ m then 𝒜 (m - n * d) else ⊥ := by
  rw [mem_grade_iff]
  refine ⟨fun h ↦ by simpa using h n, fun h k ↦ ?_⟩
  by_cases hk : n = k
  · subst k
    simpa using h
  · simp [Ne.symm hk]

/-- Multiplying by `T⁽ⁿ⁾` shifts the coefficient degree by `n * d`. -/
public theorem monomial_mem_grade (𝒜 : ℕ → Submodule R A) (d n k : ℕ)
    {a : A} (ha : a ∈ 𝒜 k) : monomial n a ∈ grade 𝒜 d (k + n * d) := by
  simpa using (monomial_mem_grade_iff 𝒜 d (k + n * d) n a).2 (by simpa using ha)

/-- The formal symbol `T⁽ⁿ⁾` has degree `n * d`. -/
public theorem monomial_one_mem_grade (𝒜 : ℕ → Submodule R A)
    [SetLike.GradedMonoid 𝒜] (d n : ℕ) : monomial n 1 ∈ grade 𝒜 d (n * d) := by
  simpa using monomial_mem_grade 𝒜 d n 0 (SetLike.one_mem_graded 𝒜)

/-- A constant `a` has degree `m` in the even variable algebra if and only if `a ∈ 𝒜 m`. -/
public theorem coeffEmbedding_mem_grade_iff (𝒜 : ℕ → Submodule R A)
    (d m : ℕ) (a : A) : coeffEmbedding a ∈ grade 𝒜 d m ↔ a ∈ 𝒜 m := by
  simp

/-- Induction within a homogeneous piece by its homogeneous monomials. -/
@[elab_as_elim]
public theorem homogeneous_induction_on {𝒜 : ℕ → Submodule R A} {d m : ℕ}
    {P : EvenVariableAlgebra A → Prop} {x : EvenVariableAlgebra A}
    (hx : x ∈ grade 𝒜 d m) (zero : P 0)
    (monomial : ∀ n a, n * d ≤ m → a ∈ 𝒜 (m - n * d) → P (monomial n a))
    (add : ∀ x y, x ∈ grade 𝒜 d m → y ∈ grade 𝒜 d m → P x → P y → P (x + y)) :
    P x := by
  classical
  have h := Finset.sum_induction (s := x.coeff.support)
    (fun n ↦ EvenVariableAlgebra.monomial n (x.coeff n))
    (fun y ↦ y ∈ grade 𝒜 d m ∧ P y)
    (fun y z hy hz ↦ ⟨Submodule.add_mem _ hy.1 hz.1, add y z hy.1 hz.1 hy.2 hz.2⟩)
    ⟨Submodule.zero_mem _, zero⟩ (fun n hn ↦ ?_)
  · rw [sum_monomial] at h
    exact h.2
  · have hn' := (mem_grade_iff 𝒜 d m x).1 hx n
    have hle : n * d ≤ m := by
      by_contra hle
      have : x.coeff n = 0 := by simpa [hle] using hn'
      exact Finsupp.mem_support_iff.mp hn this
    have ha : x.coeff n ∈ 𝒜 (m - n * d) := by simpa [hle] using hn'
    exact ⟨(monomial_mem_grade_iff 𝒜 d m n _).2 hn', monomial n _ hle ha⟩

/-- The homogeneous pieces `grade 𝒜 d` form a graded monoid. -/
public instance gradedMonoid (𝒜 : ℕ → Submodule R A) [SetLike.GradedMonoid 𝒜]
    (d : ℕ) : SetLike.GradedMonoid (grade 𝒜 d) where
  one_mem := by
    change monomial 0 1 ∈ grade 𝒜 d 0
    simpa using (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    intro i j x y hx hy
    refine homogeneous_induction_on hx ?_ ?_ ?_
    · simp
    · intro n a hn ha
      refine homogeneous_induction_on hy ?_ ?_ ?_
      · simp
      · intro k b hk hb
        rw [monomial_mul_monomial, monomial_mem_grade_iff]
        have hle : (n + k) * d ≤ i + j := by
          rw [add_mul]
          omega
        have heq : i + j - (n + k) * d = (i - n * d) + (j - k * d) := by
          rw [add_mul]
          omega
        rw [ite_eq_left hle, heq]
        exact nsmul_mem (SetLike.mul_mem_graded ha hb) _
      · intro y z hy hz hy' hz'
        simpa [mul_add] using Submodule.add_mem _ hy' hz'
    · intro x z hx hz hx' hz'
      simpa [add_mul] using Submodule.add_mem _ hx' hz'

private def decomposeMonomial (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d n : ℕ) : A →+ ⨁ m, grade 𝒜 d m :=
  (DirectSum.toAddMonoid fun k ↦
    { toFun := fun a : 𝒜 k ↦ DirectSum.of (fun m ↦ grade 𝒜 d m) (k + n * d)
        ⟨monomial n a, monomial_mem_grade 𝒜 d n k a.2⟩
      map_zero' := by
        change DirectSum.of (fun m ↦ grade 𝒜 d m) (k + n * d) ⟨monomial n 0, _⟩ = _
        rw [show (⟨monomial n 0, _⟩ : grade 𝒜 d (k + n * d)) = 0 from
          Subtype.ext (monomial_zero n), map_zero]
      map_add' := by
        intro a b
        rw [← map_add]
        congr 1
        exact Subtype.ext (monomial_add n (a : A) (b : A)) }).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

private def decomposeAddHom (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : ℕ) : EvenVariableAlgebra A →+ ⨁ m, grade 𝒜 d m :=
  (Finsupp.liftAddHom (decomposeMonomial 𝒜 d)).comp
    { toFun := coeff, map_zero' := coeff_zero, map_add' := coeff_add }

private theorem decomposeAddHom_monomial (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d n k : ℕ) {a : A} (ha : a ∈ 𝒜 k) :
    decomposeAddHom 𝒜 d (monomial n a) =
      DirectSum.of (fun m ↦ grade 𝒜 d m) (k + n * d)
        ⟨monomial n a, monomial_mem_grade 𝒜 d n k ha⟩ := by
  show (Finsupp.liftAddHom (decomposeMonomial 𝒜 d)) (Finsupp.single n a) = _
  rw [Finsupp.liftAddHom_apply_single]
  show DirectSum.toAddMonoid (fun k ↦ _) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

private theorem recompose_decompose (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : ℕ) (x : EvenVariableAlgebra A) :
    DirectSum.coeAddMonoidHom (grade 𝒜 d) (decomposeAddHom 𝒜 d x) = x := by
  induction x using induction_on with
  | zero => simp
  | add n a x hx =>
    rw [map_add, map_add, hx]
    congr 1
    refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ a
    · simp
    · intro k a
      rw [decomposeAddHom_monomial 𝒜 d n k a.2, DirectSum.coeAddMonoidHom_of]
    · intro a b ha hb
      simp only [monomial_add, map_add, ha, hb]

private theorem decomposeAddHom_of_mem (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d m : ℕ) {x : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d m) :
    decomposeAddHom 𝒜 d x = DirectSum.of (fun m ↦ grade 𝒜 d m) m ⟨x, hx⟩ := by
  refine homogeneous_induction_on (P := fun x ↦ ∀ hx : x ∈ grade 𝒜 d m,
    decomposeAddHom 𝒜 d x = DirectSum.of (fun m ↦ grade 𝒜 d m) m ⟨x, hx⟩) hx ?_ ?_ ?_ hx
  · intro h
    show decomposeAddHom 𝒜 d 0 = DirectSum.of _ m 0
    simp
  · intro n a hn ha h
    generalize hk : m - n * d = k at ha
    have hm : m = k + n * d := by omega
    subst m
    exact decomposeAddHom_monomial 𝒜 d n k ha
  · intro x y hx hy hx' hy' h
    rw [map_add, hx' hx, hy' hy, ← map_add]
    rfl

private theorem isInternal_grade (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : ℕ) : DirectSum.IsInternal (grade 𝒜 d) := by
  let : DirectSum.Decomposition (grade 𝒜 d) :=
    { decompose' := decomposeAddHom 𝒜 d
      left_inv := recompose_decompose 𝒜 d
      right_inv := by
        suffices (decomposeAddHom 𝒜 d).comp (DirectSum.coeAddMonoidHom (grade 𝒜 d)) =
            AddMonoidHom.id _ from DFunLike.congr_fun this
        apply DirectSum.addHom_ext
        intro m x
        simpa using decomposeAddHom_of_mem 𝒜 d m x.2 }
  exact DirectSum.Decomposition.isInternal _

/-- The shifted homogeneous pieces give an internal grading of the coefficient algebra. -/
@[stacks 09PI "even_variable_algebra"]
public instance gradedAlgebra (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : ℕ) : GradedAlgebra (grade 𝒜 d) where
  toDecomposition := DirectSum.IsInternal.chooseDecomposition _ (by exact isInternal_grade 𝒜 d)

private theorem sub_mul_mod_two (d i n : ℕ) (hd : Even d) (hn : n * d ≤ i) :
    (i - n * d) % 2 = i % 2 := by
  have hnd : (n * d) % 2 = 0 := by simp [Nat.mul_mod, Nat.even_iff.mp hd]
  omega

private theorem graded_comm_of_even (𝒜 : ℕ → Submodule R A)
    [IsStrictlyGradedComm 𝒜] (d : ℕ) (hd : Even d) {i j : ℕ}
    {x y : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d i) (hy : y ∈ grade 𝒜 d j) :
    x * y = (-1 : R) ^ (i * j) • (y * x) := by
  refine homogeneous_induction_on hx ?_ ?_ ?_
  · simp
  · intro n a hn ha
    refine homogeneous_induction_on hy ?_ ?_ ?_
    · simp
    · intro k b hk hb
      have hsign : (-1 : R) ^ ((i - n * d) * (j - k * d)) = (-1 : R) ^ (i * j) := by
        rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (i * j)]
        simp only [Nat.mul_mod, Nat.mod_mod, sub_mul_mod_two d i n hd hn,
          sub_mul_mod_two d j k hd hk]
      rw [monomial_mul_monomial, monomial_mul_monomial, smul_monomial,
        IsStrictlyGradedComm.graded_comm ha hb, hsign]
      have hchoose : Nat.choose (n + k) n = Nat.choose (k + n) k := by
        rw [Nat.choose_symm_add, Nat.add_comm]
      rw [hchoose, smul_comm, Nat.add_comm n k]
    · intro y z hy hz hy' hz'
      simp only [mul_add, add_mul, smul_add, hy', hz']
  · intro x z hx hz hx' hz'
    simp only [mul_add, add_mul, smul_add, hx', hz']

private theorem odd_sq_zero_of_even (𝒜 : ℕ → Submodule R A)
    [IsStrictlyGradedComm 𝒜] (d : ℕ) (hd : Even d) {i : ℕ}
    {x : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d (2 * i + 1)) : x ^ 2 = 0 := by
  refine homogeneous_induction_on hx ?_ ?_ ?_
  · simp
  · intro n a hn ha
    have hpar := sub_mul_mod_two d (2 * i + 1) n hd hn
    have heq : 2 * ((2 * i + 1 - n * d) / 2) + 1 = 2 * i + 1 - n * d := by omega
    have hs : a ^ 2 = 0 := IsStrictlyGradedComm.odd_sq_zero (𝒜 := 𝒜)
      (d := (2 * i + 1 - n * d) / 2) (by simpa only [heq] using ha)
    rw [pow_two, monomial_mul_monomial, ← pow_two, hs, nsmul_zero, monomial_zero]
  · intro x y hx hy hx' hy'
    have hc : x * y = -(y * x) := by
      have hsign : (-1 : R) ^ ((2 * i + 1) * (2 * i + 1)) = -1 := by
        rw [neg_one_pow_eq_pow_mod_two]
        simp [Nat.add_mod, Nat.mul_mod]
      simpa only [hsign, neg_one_smul] using graded_comm_of_even 𝒜 d hd hx hy
    rw [pow_two, add_mul, mul_add, mul_add, ← pow_two x, ← pow_two y, hx', hy', hc]
    simp

/-- An even variable preserves strict graded commutativity, including vanishing odd squares. -/
@[stacks 09PI "even_variable_algebra"]
public instance strictlyGradedComm (𝒜 : ℕ → Submodule R A) [IsStrictlyGradedComm 𝒜]
    (d : ℕ) [Fact (Even d)] : IsStrictlyGradedComm (grade 𝒜 d) where
  graded_comm := graded_comm_of_even 𝒜 d Fact.out
  odd_sq_zero := odd_sq_zero_of_even 𝒜 d Fact.out

end

end EvenVariableAlgebra

end DividedPowers.TateResolution
