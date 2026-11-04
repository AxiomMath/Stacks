module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Divided powers on a strictly graded-commutative algebra

Let `A` be a nonnegatively graded algebra over a commutative ring `R`, with homogeneous pieces
`𝒜 i`. The grading is *strictly graded-commutative* when homogeneous elements commute up to the
Koszul sign and every homogeneous element of odd degree squares to zero. On such an algebra the
positive even part `⨆ d, 𝒜 (2 * (d + 1))` is a commutative ideal of the even part, and a
*divided power structure* on it is a system of operations `γₙ` behaving like `xⁿ / n!`: they
multiply degrees, satisfy the binomial and composition identities, turn sums into the
convolution product, and kill `n`-th powers (`n > 1`) of products of two odd elements.

Such a structure is *compatible with a differential* `d` when `d (γₙ x) = d x · γₙ₋₁ x`, which is
the condition appearing in the construction of Tate resolutions.

## Main definitions

* `DividedPowers.TateResolution.evenPart` and
  `DividedPowers.TateResolution.positiveEvenPart` — the even and positive even parts of a
  nonnegatively graded algebra, as suprema of homogeneous pieces.
* `DividedPowers.TateResolution.IsStrictlyGradedComm` — graded commutativity together with
  square-zero odd homogeneous elements.
* `DividedPowers.TateResolution.DividedPowerStructure` — divided powers on the positive even
  part, compatible with the grading and with products of odd homogeneous elements.
* `DividedPowers.TateResolution.IsCompatibleWithDifferential` — compatibility of divided powers
  with a differential.

## Main results

* `DividedPowers.TateResolution.evenPart_mul_comm`: an element of the even part is central.
* `DividedPowers.TateResolution.DividedPowerStructure.dpowOnPositive` recovers the source's
  positive-indexed maps on the positive even part, and
  `DividedPowers.TateResolution.DividedPowerStructure.dpow_eq_dpowZeroExtension` characterizes
  the ambient operation as the zero extension of those maps.
* `DividedPowers.TateResolution.DividedPowerStructure.ext`: divided power structures are
  determined by their divided power operations;
  `DividedPowers.TateResolution.DividedPowerStructure.ext_on_positive` gives the corresponding
  source-domain criterion.
* `DividedPowers.TateResolution.dpow_mem_evenPart`: every divided power of a positive even
  element is even.
* `DividedPowers.TateResolution.isCompatibleWithDifferential_iff` characterizes compatibility
  with a differential by the defining formula.

## Implementation notes

The even and positive even parts are expressed as suprema of the corresponding homogeneous
submodules. Following Mathlib's `DividedPowers`, the divided power maps are totalized to the
ambient algebra by assigning zero away from the positive even part. This gives downstream users
an operation with the source's notation while retaining exactly the source's domain.

The compatibility condition with a differential is kept separate from the remaining differential
graded algebra axioms: it takes the underlying linear differential as an argument, while the
grading, strict graded commutativity, and divided power axioms are supplied by the structures
above. This lets the condition be used with any equivalent model of a differential graded
algebra. We use the homological, nonnegative grading convention throughout.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 09PJ](https://stacks.math.columbia.edu/tag/09PJ)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The even part of a nonnegatively graded algebra. -/
public abbrev evenPart (𝒜 : ℕ → Submodule R A) : Submodule R A :=
  ⨆ d : ℕ, 𝒜 (2 * d)

/-- The positive even part of a nonnegatively graded algebra. -/
public abbrev positiveEvenPart (𝒜 : ℕ → Submodule R A) : Submodule R A :=
  ⨆ d : ℕ, 𝒜 (2 * (d + 1))

/-- The positive even part is contained in the even part. -/
public theorem positiveEvenPart_le_evenPart (𝒜 : ℕ → Submodule R A) :
    positiveEvenPart 𝒜 ≤ evenPart 𝒜 :=
  iSup_le fun d ↦ le_iSup_of_le (d + 1) le_rfl

/-- A homogeneous element of positive even degree lies in the positive even part. -/
public theorem mem_positiveEvenPart_of_mem_grade (𝒜 : ℕ → Submodule R A) {d : ℕ} {x : A}
    (hd : 0 < d) (hx : x ∈ 𝒜 (2 * d)) : x ∈ positiveEvenPart 𝒜 := by
  refine Submodule.mem_iSup_of_mem (d - 1) ?_
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hx

/-- The positive even part is stable under multiplication by the even part. -/
public theorem evenPart_mul_positiveEvenPart (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x y : A} (hx : x ∈ evenPart 𝒜) (hy : y ∈ positiveEvenPart 𝒜) :
    x * y ∈ positiveEvenPart 𝒜 := by
  revert y hy
  induction hx using Submodule.iSup_induction' with
  | mem d x hx =>
      intro y hy
      induction hy using Submodule.iSup_induction' with
      | mem e y hy =>
          refine Submodule.mem_iSup_of_mem (d + e) ?_
          have hm : x * y ∈ 𝒜 (2 * d + 2 * (e + 1)) := SetLike.GradedMul.mul_mem hx hy
          rwa [show 2 * d + 2 * (e + 1) = 2 * (d + e + 1) by omega] at hm
      | zero => simp
      | add y y' _ _ ih ih' =>
          rw [mul_add]
          exact Submodule.add_mem _ ih ih'
  | zero =>
      intro y hy
      simp
  | add x x' _ _ ih ih' =>
      intro y hy
      rw [add_mul]
      exact Submodule.add_mem _ (ih hy) (ih' hy)

/-- A graded algebra is strictly graded commutative if homogeneous elements commute with the
Koszul sign and every homogeneous element of odd degree has square zero. -/
@[sga "6 VII 2.1"]
public class IsStrictlyGradedComm (𝒜 : ℕ → Submodule R A) : Prop where
  graded_comm : ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
    x * y = (-1 : R) ^ (i * j) • (y * x)
  odd_sq_zero : ∀ {d : ℕ} {x : A}, x ∈ 𝒜 (2 * d + 1) → x ^ 2 = 0

/-- **An element of the even part of a strictly graded-commutative algebra is central.** The
Koszul sign on a product with a homogeneous element is `(-1) ^ (2 * k * j)`, which is `1`; the
general case follows by decomposing the second factor. -/
public theorem evenPart_mul_comm (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] {x : A} (hx : x ∈ evenPart 𝒜) (y : A) : x * y = y * x := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j y =>
      simpa [show 2 * k * j = 2 * (k * j) by ring] using
        IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) hx y.property
    | add y y' hy hy' => rw [mul_add, add_mul, hy, hy']
  | zero => simp
  | add x x' _ _ ihx ihx' => rw [add_mul, mul_add, ihx, ihx']

/-- A divided power structure on the positive even part of a strictly graded-commutative graded
algebra. -/
@[stacks 09PG]
public structure DividedPowerStructure (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] where
  /-- The `n`th divided power, totalized by zero outside the positive even part. -/
  dpow : ℕ → A → A
  /-- The totalized operation vanishes outside its domain. -/
  dpow_null : ∀ {n : ℕ} {x : A}, x ∉ positiveEvenPart 𝒜 → dpow n x = 0
  /-- The zeroth divided power is one on the positive even part. -/
  dpow_zero : ∀ {x : A}, x ∈ positiveEvenPart 𝒜 → dpow 0 x = 1
  /-- The first divided power is the identity. -/
  dpow_one : ∀ {x : A}, x ∈ positiveEvenPart 𝒜 → dpow 1 x = x
  /-- Positive divided powers preserve the positive even part. -/
  dpow_mem : ∀ {n : ℕ} {x : A}, n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
    dpow n x ∈ positiveEvenPart 𝒜
  /-- Divided powers multiply the degree of a positive even homogeneous element. -/
  dpow_mem_grade : ∀ {n d : ℕ} {x : A}, n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
    x ∈ 𝒜 (2 * d) → dpow n x ∈ 𝒜 (2 * n * d)
  /-- Two divided powers of the same element satisfy the binomial coefficient identity. -/
  dpow_mul : ∀ {m n : ℕ} {x : A}, x ∈ positiveEvenPart 𝒜 →
    dpow n x * dpow m x = (Nat.choose (n + m) n : A) * dpow (n + m) x
  /-- An even factor can be extracted from a divided power. -/
  dpow_mul_even : ∀ {n : ℕ} {x y : A}, n ≠ 0 → x ∈ evenPart 𝒜 →
    y ∈ positiveEvenPart 𝒜 → dpow n (x * y) = x ^ n * dpow n y
  /-- Higher divided powers vanish on products of two odd homogeneous elements. -/
  dpow_mul_odd : ∀ {n d e : ℕ} {x y : A}, 1 < n → x ∈ 𝒜 (2 * d + 1) →
    y ∈ 𝒜 (2 * e + 1) → dpow n (x * y) = 0
  /-- Divided powers turn sums into the convolution product. -/
  dpow_add : ∀ {n : ℕ} {x y : A}, x ∈ positiveEvenPart 𝒜 →
    y ∈ positiveEvenPart 𝒜 →
    dpow n (x + y) = ∑ ij ∈ Finset.antidiagonal n, dpow ij.1 x * dpow ij.2 y
  /-- Iterated divided powers satisfy the standard factorial identity. -/
  dpow_dpow : ∀ {m n : ℕ} {x : A}, m ≠ 0 → n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
    dpow n (dpow m x) =
      (((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : A) * dpow (n * m) x

attribute [simp] DividedPowerStructure.dpow_zero DividedPowerStructure.dpow_one

namespace DividedPowerStructure

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- The source-domain `n`th divided power map, for a positive index `n`. -/
@[implicit_reducible]
public def dpowOnPositive (γ : DividedPowerStructure 𝒜) (n : ℕ+) :
    positiveEvenPart 𝒜 → positiveEvenPart 𝒜 :=
  fun x => ⟨γ.dpow n x, γ.dpow_mem n.ne_zero x.2⟩

/-- Coercing a source-domain divided power to the algebra recovers the ambient operation. -/
@[simp]
public theorem coe_dpowOnPositive (γ : DividedPowerStructure 𝒜) (n : ℕ+)
    (x : positiveEvenPart 𝒜) : (γ.dpowOnPositive n x : A) = γ.dpow n x := rfl

open Classical in
/-- Extend a source-domain divided power map by zero to the ambient algebra. -/
public noncomputable def dpowZeroExtension (γ : DividedPowerStructure 𝒜) (n : ℕ+) (x : A) : A :=
  if hx : x ∈ positiveEvenPart 𝒜 then γ.dpowOnPositive n ⟨x, hx⟩ else 0

/-- The zero extension agrees with the source-domain map on the positive even part. -/
@[simp]
public theorem dpowZeroExtension_of_mem (γ : DividedPowerStructure 𝒜) (n : ℕ+) {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) : γ.dpowZeroExtension n x = γ.dpow n x := by
  simp [dpowZeroExtension, hx]

/-- The zero extension vanishes away from the positive even part. -/
@[simp]
public theorem dpowZeroExtension_of_not_mem (γ : DividedPowerStructure 𝒜) (n : ℕ+) {x : A}
    (hx : x ∉ positiveEvenPart 𝒜) : γ.dpowZeroExtension n x = 0 := by
  simp [dpowZeroExtension, hx]

/-- For a positive index, the ambient divided power operation is the zero extension of its
restriction to the positive even part. -/
public theorem dpow_eq_dpowZeroExtension (γ : DividedPowerStructure 𝒜) (n : ℕ+) :
    γ.dpow n = γ.dpowZeroExtension n := by
  funext x
  by_cases hx : x ∈ positiveEvenPart 𝒜
  · exact (γ.dpowZeroExtension_of_mem n hx).symm
  · exact (γ.dpow_null hx).trans (γ.dpowZeroExtension_of_not_mem n hx).symm

/-- Two divided power structures are equal if their operations agree. -/
@[ext]
public theorem ext {γ δ : DividedPowerStructure 𝒜} (h : γ.dpow = δ.dpow) : γ = δ := by
  cases γ
  cases δ
  cases h
  rfl

/-- Two divided power structures are equal if their positive-indexed maps on the positive even
part agree. -/
public theorem ext_on_positive {γ δ : DividedPowerStructure 𝒜}
    (h : ∀ n : ℕ+, γ.dpowOnPositive n = δ.dpowOnPositive n) : γ = δ := by
  ext n x
  by_cases hx : x ∈ positiveEvenPart 𝒜
  · cases n with
    | zero => exact (γ.dpow_zero hx).trans (δ.dpow_zero hx).symm
    | succ n =>
      exact congrArg Subtype.val (congrFun (h ⟨n + 1, Nat.succ_pos n⟩) ⟨x, hx⟩)
  · exact (γ.dpow_null hx).trans (δ.dpow_null hx).symm

end DividedPowerStructure

/-- The divided powers of a positive even element lie in the even part. The zeroth one is `1`,
which is even because it is homogeneous of degree zero; a positive one stays in the positive
even part by `DividedPowerStructure.dpow_mem`. -/
public theorem dpow_mem_evenPart (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) (n : ℕ) {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) : γ.dpow n x ∈ evenPart 𝒜 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [γ.dpow_zero hx]
    exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
  · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem hn.ne' hx)

/-- A divided power structure is compatible with a differential if the differential of every
positive divided power has the expected divided-power derivative. -/
@[stacks 09PJ]
public class IsCompatibleWithDifferential {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A) : Prop where
  /-- The differential of `γₙ(x)` is `d(x) γₙ₋₁(x)`. -/
  d_dpow : ∀ {n : ℕ} {x : A}, n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
    d (γ.dpow n x) = d x * γ.dpow (n - 1) x

/-- Compatibility of divided powers with a differential is equivalent to the defining
differential formula. -/
public theorem isCompatibleWithDifferential_iff {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A) :
    IsCompatibleWithDifferential γ d ↔ ∀ {n : ℕ} {x : A}, n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
      d (γ.dpow n x) = d x * γ.dpow (n - 1) x :=
  ⟨fun h => h.d_dpow, fun h => ⟨h⟩⟩

end DividedPowers.TateResolution
