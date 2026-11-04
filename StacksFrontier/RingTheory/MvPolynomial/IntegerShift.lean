module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The integer shift of a polynomial ring with a two-sided family of variables

Write `R = K[y, x_n : n ∈ ℤ]` for the polynomial ring over a commutative ring `K` on the
index type `Option ℤ`, with `y` the variable indexed by `none` and `x_n` the variable
indexed by `some n`. The assignment `y ↦ y - 1`, `x_n ↦ x_{n - 1}` is a `K`-algebra
automorphism of `R`; it generates an action of the integers on `R`, hence on `Spec R`.

The *tail primes* of `R` are the primes `p_n = (x_n, x_{n + 1}, \ldots)`, realised here as
the kernels of the `K`-algebra endomorphisms killing exactly the variables `x_j` with
`j ≥ n`. They form a strictly decreasing chain, so that `p_n` specializes to `p_m` for
`m ≤ n`, and the shift moves the chain by one step. This is the algebra behind the example
of Stacks 06UK: on `Spec R` the integer action is free while two points of one orbit are
related by a specialization.

## Main definitions

* `MvPolynomial.shiftDown` and `MvPolynomial.shiftUp` are the two mutually inverse shift
  endomorphisms, lowering and raising the index of each `x_n` while translating `y`.
* `MvPolynomial.tailHom` is the endomorphism killing the variables `x_j` with `j ≥ n`, and
  `MvPolynomial.tailPrime` is its kernel, the `n`-th tail prime.

## Main results

* `MvPolynomial.tailPrime_le_tailPrime_of_le` and
  `MvPolynomial.tailPrime_specializes_of_le`: the tail primes decrease, so a later one
  specializes to an earlier one in the prime spectrum.
* `MvPolynomial.tailPrime_injective`: distinct indices give distinct tail primes.
* `MvPolynomial.comap_shiftDown_tailPrime`: the shift carries the `n`-th tail prime to the
  `(n + 1)`-st, so all tail primes lie in a single orbit of the integer action.

## Implementation notes

The tail prime `p_n` is defined as a kernel rather than as a span of variables: primality is
then immediate from `RingHom.ker_isPrime`, and the two facts needed about the chain — the
inclusion `p_n ⊆ p_m` for `m ≤ n` and the behaviour under the shift — are both witnessed by
a factorisation of one endomorphism through another, so they reduce to `MvPolynomial.aeval`
computations on the variables.

## References

* [Stacks Project, Tag 06UK](https://stacks.math.columbia.edu/tag/06UK)
-/

@[expose] public noncomputable section

universe u

namespace MvPolynomial

variable (K : Type u) [CommRing K]

/-! ### The shift endomorphisms -/

/-- The `K`-algebra endomorphism of `K[y, x_n : n ∈ ℤ]` sending `y` to `y - 1` and `x_n` to
`x_{n - 1}`. It is an automorphism, inverse to `MvPolynomial.shiftUp`, and generates the
integer action of Stacks 06UK. -/
def shiftDown : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K :=
  aeval fun i ↦ match i with
    | none => X none - 1
    | some n => X (some (n - 1))

/-- The `K`-algebra endomorphism of `K[y, x_n : n ∈ ℤ]` sending `y` to `y + 1` and `x_n` to
`x_{n + 1}`, inverse to `MvPolynomial.shiftDown`. -/
def shiftUp : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K :=
  aeval fun i ↦ match i with
    | none => X none + 1
    | some n => X (some (n + 1))

/-- Raising after lowering is the identity. -/
theorem shiftUp_comp_shiftDown : (shiftUp K).comp (shiftDown K) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  cases i <;> simp [shiftUp, shiftDown]

/-- Lowering after raising is the identity. -/
theorem shiftDown_comp_shiftUp : (shiftDown K).comp (shiftUp K) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  cases i <;> simp [shiftUp, shiftDown]

/-- Raising is a left inverse of lowering. -/
theorem shiftUp_shiftDown (f : MvPolynomial (Option ℤ) K) :
    shiftUp K (shiftDown K f) = f := by
  simpa using congrArg (fun φ : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K ↦ φ f)
    (shiftUp_comp_shiftDown K)

/-- The shift is injective. -/
theorem shiftDown_injective : Function.Injective (shiftDown K) :=
  Function.LeftInverse.injective (shiftUp_shiftDown K)

/-! ### The tail primes -/

/-- The `K`-algebra endomorphism of `K[y, x_n : n ∈ ℤ]` fixing `y` and every `x_j` with
`j < n` and killing every `x_j` with `j ≥ n`. Its kernel is the `n`-th tail prime. -/
def tailHom (n : ℤ) : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K :=
  aeval fun i ↦ match i with
    | none => X none
    | some j => if j < n then X (some j) else 0

/-- The endomorphism of `K[y, x_n : n ∈ ℤ]` fixing `y` and every `x_j` outside the interval
`[m, n)` and killing every `x_j` inside it. It exhibits `MvPolynomial.tailHom` at `m` as a
factor of `MvPolynomial.tailHom` at `n`. -/
private def intervalHom (m n : ℤ) :
    MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K :=
  aeval fun i ↦ match i with
    | none => X none
    | some j => if m ≤ j ∧ j < n then 0 else X (some j)

private theorem intervalHom_comp_tailHom {m n : ℤ} (h : m ≤ n) :
    (intervalHom K m n).comp (tailHom K n) = tailHom K m := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none => simp [intervalHom, tailHom]
  | some j =>
      by_cases hjn : j < n
      · by_cases hjm : j < m
        · simp [intervalHom, tailHom, hjn, hjm]
        · have hin : m ≤ j ∧ j < n := by omega
          simp [intervalHom, tailHom, hjn, hjm, hin]
      · have hjm : ¬ j < m := by omega
        simp [intervalHom, tailHom, hjn, hjm]

/-- Shifting and then truncating at `n` is truncating at `n + 1` and then shifting. -/
theorem tailHom_comp_shiftDown (n : ℤ) :
    (tailHom K n).comp (shiftDown K) = (shiftDown K).comp (tailHom K (n + 1)) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none => simp [tailHom, shiftDown]
  | some j =>
      by_cases hj : j < n + 1
      · have hj' : j - 1 < n := by omega
        simp [tailHom, shiftDown, hj, hj']
      · have hj' : ¬ j - 1 < n := by omega
        simp [tailHom, shiftDown, hj, hj']

variable [IsDomain K]

/-- The `n`-th *tail prime* of `K[y, x_n : n ∈ ℤ]`, the prime ideal
`(x_n, x_{n + 1}, \ldots)` presented as the kernel of `MvPolynomial.tailHom`. -/
def tailPrime (n : ℤ) : PrimeSpectrum (MvPolynomial (Option ℤ) K) :=
  ⟨RingHom.ker (tailHom K n).toRingHom, RingHom.ker_isPrime (tailHom K n).toRingHom⟩

/-- Membership in the `n`-th tail prime means vanishing under `MvPolynomial.tailHom`. -/
private theorem mem_tailPrime_iff {n : ℤ} {p : MvPolynomial (Option ℤ) K} :
    p ∈ (tailPrime K n).asIdeal ↔ tailHom K n p = 0 :=
  RingHom.mem_ker

/-- The tail primes decrease: `p_n ⊆ p_m` whenever `m ≤ n`. -/
theorem tailPrime_le_tailPrime_of_le {m n : ℤ} (h : m ≤ n) :
    tailPrime K n ≤ tailPrime K m := fun p hp ↦ by
  rw [mem_tailPrime_iff] at hp ⊢
  rw [← intervalHom_comp_tailHom K h, AlgHom.comp_apply, hp, map_zero]

/-- A later tail prime specializes to an earlier one. -/
theorem tailPrime_specializes_of_le {m n : ℤ} (h : m ≤ n) :
    tailPrime K n ⤳ tailPrime K m :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (tailPrime_le_tailPrime_of_le K h)

/-- Tail primes at different indices are different: the variable `x_m` lies in the `m`-th
but not in the `n`-th for `m < n`. -/
theorem tailPrime_ne_of_lt {m n : ℤ} (h : m < n) : tailPrime K m ≠ tailPrime K n := by
  intro hmn
  have hmem : X (some m) ∈ (tailPrime K m).asIdeal := by
    rw [mem_tailPrime_iff]
    simp [tailHom]
  have hnotmem : X (some m) ∉ (tailPrime K n).asIdeal := by
    rw [mem_tailPrime_iff]
    simp [tailHom, h]
  exact hnotmem (hmn ▸ hmem)

/-- The tail primes are pairwise distinct. -/
theorem tailPrime_injective : Function.Injective (tailPrime K) := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (tailPrime_ne_of_lt K hlt)
  · exact heq
  · exact absurd h.symm (tailPrime_ne_of_lt K hgt)

/-- The shift carries the `n`-th tail prime to the `(n + 1)`-st: all tail primes lie in one
orbit of the integer action. -/
theorem comap_shiftDown_tailPrime (n : ℤ) :
    PrimeSpectrum.comap (shiftDown K).toRingHom (tailPrime K n) = tailPrime K (n + 1) := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal]
  change Ideal.comap (shiftDown K).toRingHom (RingHom.ker (tailHom K n).toRingHom) =
    RingHom.ker (tailHom K (n + 1)).toRingHom
  rw [RingHom.comap_ker, show (tailHom K n).toRingHom.comp (shiftDown K).toRingHom =
      (shiftDown K).toRingHom.comp (tailHom K (n + 1)).toRingHom from
    congrArg AlgHom.toRingHom (tailHom_comp_shiftDown K n)]
  exact RingHom.ker_comp_of_injective _ (shiftDown_injective K)

end MvPolynomial

end
