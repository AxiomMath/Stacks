module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import StacksCore.Tactic.StacksAttribute

/-!
# Commutative differential graded algebras

A graded algebra is graded-commutative when homogeneous elements commute up to the
Koszul sign. It is strictly graded-commutative when, in addition, every homogeneous
element of odd degree has square zero.

The differential does not occur in either condition, so the classes concern only the
homogeneous pieces. Degrees range over any semiring with decidable parity; in particular,
the same interface applies directly to both natural- and integer-graded algebras. The
Koszul sign is written by cases on the parity of the two degrees.

## Main definitions

* `DifferentialGraded.IsGradedCommutative` expresses commutativity up to the Koszul sign.
* `DifferentialGraded.IsStrictlyGradedCommutative` additionally requires odd-degree squares
  to vanish.

## Main results

* `DifferentialGraded.isGradedCommutative_iff` and
  `DifferentialGraded.isStrictlyGradedCommutative_iff` characterize the two classes.
* `DifferentialGraded.isGradedCommutative_nat_iff` and
  `DifferentialGraded.isGradedCommutative_int_iff` recover the usual power formulas. For
  integer degrees the second identifies the parity condition with the source's formula
  using `Int.negOnePow`; the natural-degree version is stated with the scalar action
  customary for graded algebras.

## References

* [Stacks Project, Tag 061W](https://stacks.math.columbia.edu/tag/061W)
-/

@[expose] public section

universe u v w

namespace DifferentialGraded

/-- A grading on a ring is *graded-commutative* when two homogeneous elements
commute unless both degrees are odd, in which case they anticommute. -/
@[stacks 061W "commutativity"]
public class IsGradedCommutative {ι : Type w} [Semiring ι]
    [DecidablePred (Odd : ι → Prop)] {A : Type u} [Ring A]
    {S : Type v} [Membership A S] (𝒜 : ι → S) : Prop where
  /-- Homogeneous elements commute with their Koszul sign. -/
  graded_comm : ∀ {i j : ι} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
    x * y = if Odd i ∧ Odd j then -(y * x) else y * x

/-- A grading is *strictly graded-commutative* when it is graded-commutative and
every homogeneous element of odd degree has square zero. -/
@[stacks 061W "strict commutativity", sga "6 VII 2.1"]
public class IsStrictlyGradedCommutative {ι : Type w} [Semiring ι]
    [DecidablePred (Odd : ι → Prop)] {A : Type u} [Ring A]
    {S : Type v} [Membership A S] (𝒜 : ι → S) extends IsGradedCommutative 𝒜 where
  /-- An odd-degree homogeneous element has square zero. -/
  odd_sq_zero : ∀ {i : ι} {x : A}, x ∈ 𝒜 i → Odd i → x ^ 2 = 0

/-- The elementwise characterization of graded commutativity. -/
public theorem isGradedCommutative_iff {ι : Type w} [Semiring ι]
    [DecidablePred (Odd : ι → Prop)] {A : Type u} [Ring A]
    {S : Type v} [Membership A S] (𝒜 : ι → S) :
    IsGradedCommutative 𝒜 ↔
      ∀ {i j : ι} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
        x * y = if Odd i ∧ Odd j then -(y * x) else y * x :=
  ⟨fun h ↦ h.graded_comm, fun h ↦ ⟨h⟩⟩

/-- Strict graded commutativity consists of graded commutativity and the
square-zero condition in odd degrees. -/
public theorem isStrictlyGradedCommutative_iff {ι : Type w} [Semiring ι]
    [DecidablePred (Odd : ι → Prop)] {A : Type u} [Ring A]
    {S : Type v} [Membership A S] (𝒜 : ι → S) :
    IsStrictlyGradedCommutative 𝒜 ↔
      IsGradedCommutative 𝒜 ∧
        ∀ {i : ι} {x : A}, x ∈ 𝒜 i → Odd i → x ^ 2 = 0 :=
  ⟨fun h ↦ ⟨h.toIsGradedCommutative, h.odd_sq_zero⟩,
    fun ⟨hcomm, hsquare⟩ ↦ { toIsGradedCommutative := hcomm, odd_sq_zero := hsquare }⟩

/-- For natural degrees in an algebra, the parity form of graded commutativity is
the usual formula with the scalar Koszul sign `(-1)^(i * j)`. -/
public theorem isGradedCommutative_nat_iff {R : Type w} [CommRing R]
    {A : Type u} [Ring A] [Algebra R A]
    {S : Type v} [Membership A S] (𝒜 : ℕ → S) :
    IsGradedCommutative 𝒜 ↔
      ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
        x * y = (-1 : R) ^ (i * j) • (y * x) := by
  rw [isGradedCommutative_iff]; constructor <;>
    (intro h i j x y hx hy; rw [h hx hy]; by_cases hij : Odd (i * j))
  all_goals first | rw [hij.neg_one_pow] | rw [(Nat.not_odd_iff_even.mp hij).neg_one_pow]
  all_goals (simp only [Nat.odd_mul] at hij; simp [hij])

/-- For integer degrees, the parity form of graded commutativity is exactly the
usual formula with the Koszul sign `(-1)^(i * j)`. -/
public theorem isGradedCommutative_int_iff {A : Type u} [Ring A]
    {S : Type v} [Membership A S] (𝒜 : ℤ → S) :
    IsGradedCommutative 𝒜 ↔
      ∀ {i j : ℤ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
        x * y = (((i * j).negOnePow : ℤ) • (y * x)) := by
  rw [isGradedCommutative_iff]; constructor <;>
    (intro h i j x y hx hy; rw [h hx hy]; by_cases hij : Odd (i * j))
  all_goals first | rw [Int.negOnePow_odd _ hij] |
    rw [Int.negOnePow_even _ (Int.not_odd_iff_even.mp hij)]
  all_goals (simp only [Int.odd_mul] at hij; simp [hij])

end DifferentialGraded
