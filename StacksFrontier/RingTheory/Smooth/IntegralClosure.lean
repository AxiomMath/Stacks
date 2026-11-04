module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.CoeffMem
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# The derivative trick: `f' h` has integral coefficients, of degree `< deg f`

Let `R` be a ring, let `S` be an `R`-algebra, let `f ∈ S[x]` be monic with all coefficients
integral over `R`, and present `B = S[x]/(f)` by a surjection `φ : S[x] →ₐ[R] B` with kernel
`(f)`. This file proves Stacks 03GD: if `y ∈ B` is integral over `R`, then `f' y` is the class of
a polynomial `g ∈ S[x]` whose coefficients are all integral over `R` and whose degree is
`< deg f`.

Mathlib's `exists_derivative_mul_eq_and_isIntegral_coeff` proves this without the degree bound, by
the source's own argument: a finite free extension `S ⊂ S'` splitting `f` as `∏ (x - α_i)`, the
Lagrange identity `f' y = ∑_i y(α_i) ∏_{j ≠ i} (x - α_j)` modulo `f`, and descent of the
coefficients along the basis `1, x, …, x^{d-1}`. The bound is obtained here by reducing the
polynomial `g` that argument produces: `g %ₘ f` has the same class in `B` because `φ f = 0`, its
degree is `< deg f` because `f` is monic, and its coefficients are still integral because division
with remainder does not leave a subalgebra containing the coefficients of the dividend and of the
divisor — here the integral closure of `R` in `S`.

## Main results

* `Stacks.Smooth.DerivativeTrick.solution`: the statement of Stacks 03GD.

## Implementation notes

Those three properties of the reduced representative are the three lemmas of this file, and only
one of them is upstream in a usable form.

*A subalgebra of coefficients is preserved by division with remainder.* What Mathlib has is the
quantitative `Polynomial.coeff_modByMonic_mem_pow_natDegree_mul`, placing `(p %ₘ q).coeff i` in
`M_q ^ deg p * M_p` for any submodules containing `1` and the coefficients of `q` and of `p`.
Taking both to be a subalgebra `A` collapses the target to `A` itself, because the underlying
submodule of a subalgebra is idempotent (`Subalgebra.isIdempotentElem_toSubmodule`); this is
`Stacks.Smooth.DerivativeTrick.coeff_modByMonic_mem`, which needs neither monicity of the divisor
nor nontriviality of `S`.

*The bound is stated with `(f.natDegree : WithBot ℕ)`, not `f.degree`.* Over the zero ring `f = 1`
and `f.degree = ⊥`, so `g.degree < f.degree` is false there while the coerced form is still true.
Accordingly `Polynomial.degree_modByMonic_lt` assumes `Nontrivial`, and its coerced form
`Stacks.Smooth.DerivativeTrick.degree_modByMonic_lt_natDegree` does not: the zero ring is the case
`p %ₘ q = 0`, of degree `⊥`. `Nat.cast_withBot` is the bridge between the coercion
`ℕ → WithBot ℕ`, which elaborates through `Nat.cast`, and `WithBot.some`.

*Lemma 03HS is not used on this route.* The source's proof needs the finite free faithfully flat
extension splitting `f`; ours inherits it through Mathlib's sibling, whose proof uses
`Polynomial.Monic.exists_splits_map` for the same purpose.

## References

* [StacksProject 03GD](https://stacks.math.columbia.edu/tag/03GD), Lemma 10.150.9
* [StacksProject 03HS](https://stacks.math.columbia.edu/tag/03HS), Lemma 10.136.16, the splitting
  extension the source's proof uses
-/

namespace Stacks.Smooth.DerivativeTrick

open Polynomial

/-- Reduction modulo `f` does not change the image under a ring map killing `f`: if `ψ f = 0`
then `ψ (p %ₘ f) = ψ p`. In the presentation `B = S[x]/(f)` this says that a class in `B` is
represented by the remainder of any of its representatives. -/
private lemma map_modByMonic_of_map_eq_zero {S B F : Type*} [Ring S] [Ring B] [FunLike F S[X] B]
    [RingHomClass F S[X] B] (ψ : F) {f : S[X]} (hf : ψ f = 0) (p : S[X]) : ψ (p %ₘ f) = ψ p := by
  rw [modByMonic_eq_sub_mul_div p f, map_sub, map_mul, hf, zero_mul, sub_zero]

/-- The remainder of `p` on division by a monic `q` has degree `< deg q`, in the coerced form
`(q.natDegree : WithBot ℕ)`, which unlike `Polynomial.degree_modByMonic_lt` needs no
`Nontrivial` hypothesis: over the zero ring `p %ₘ q = 0` has degree `⊥`. -/
private lemma degree_modByMonic_lt_natDegree {S : Type*} [Ring S] (p : S[X]) {q : S[X]}
    (hq : q.Monic) : (p %ₘ q).degree < (q.natDegree : WithBot ℕ) := by
  cases subsingleton_or_nontrivial S with
  | inl _ => simp [Subsingleton.elim (p %ₘ q) 0, Nat.cast_withBot]
  | inr _ =>
    refine (degree_modByMonic_lt p hq).trans_le ?_
    rw [degree_eq_natDegree hq.ne_zero, Nat.cast_withBot]

/-- Division with remainder does not leave a subalgebra of coefficients: if all coefficients of
`p` and of `q` lie in a subalgebra `A` of `S`, then so do all coefficients of `p %ₘ q`. -/
private lemma coeff_modByMonic_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A : Subalgebra R S) {p q : S[X]} (hp : ∀ i, p.coeff i ∈ A) (hq : ∀ i, q.coeff i ∈ A) (i : ℕ) :
    (p %ₘ q).coeff i ∈ A := by
  have h :=
    coeff_modByMonic_mem_pow_natDegree_mul (R := R) p q A.toSubmodule hp A.one_mem A.toSubmodule hq
      A.one_mem i
  rwa [← pow_succ, (Subalgebra.isIdempotentElem_toSubmodule A).pow_succ_eq] at h

/-- **Stacks 03GD**: the unbounded representative of
Mathlib's `exists_derivative_mul_eq_and_isIntegral_coeff`, reduced modulo `f`. -/
public theorem solution {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B]
    [Algebra R B] {φ : S[X] →ₐ[R] B} (hφ : Function.Surjective φ) {f : S[X]} (hf : f.Monic)
    (hf' : ∀ i, IsIntegral R (f.coeff i)) (hfx : RingHom.ker φ.toRingHom = Ideal.span {f}) {y : B}
    (hy : IsIntegral R y) :
    ∃ g : S[X],
      φ (derivative f) * y = φ g ∧
        (∀ i, IsIntegral R (g.coeff i)) ∧ g.degree < (f.natDegree : WithBot ℕ) := by
  obtain ⟨g, hg, hgi⟩ := exists_derivative_mul_eq_and_isIntegral_coeff hφ hf hf' hfx hy
  have hφf : φ f = 0 := hfx.ge (Ideal.mem_span_singleton_self f)
  exact
    ⟨g %ₘ f, hg.trans (map_modByMonic_of_map_eq_zero φ hφf g).symm,
      coeff_modByMonic_mem (integralClosure R S) hgi hf', degree_modByMonic_lt_natDegree g hf⟩

end Stacks.Smooth.DerivativeTrick

/-!
# The derivative trick: `f' h` has integral coefficients

Let `R` be a ring, let `f` be a monic polynomial whose coefficients are integral over `R`, and let
`B` be presented as `S[x]/(f)` for an `R`-algebra `S`. If `h ∈ B` is integral over `R`, then `h`
itself need not be represented by a polynomial with integral coefficients, but `f' h` is: there is
`g ∈ S[x]` of degree `< deg f`, all of whose coefficients are integral over `R`, whose class in `B`
is `f' h`. Here `f'` is the derivative of `f`, and the point of the lemma is that inverting the
single element `f'` — which is exactly what a standard étale algebra `S[x]_{f'}/(f)` does — makes
the integral closure of `R` in `B` visible coefficientwise. This is the computational heart of
"integral closure commutes with étale base change" (03GE, 03GG).

The source's proof is the classical Lagrange-interpolation identity for the derivative: after a
finite free faithfully flat extension `S ⊂ S'` over which `f = (x - α_1) ⋯ (x - α_d)` (03HS), one
has the universal identity
`f' h = ∑_{i} h(α_i) ∏_{j ≠ i} (x - α_j)` in `S'[x]/(f)`.
Each `α_i` is integral over `R` because `f` stays monic with integral coefficients, and each
`h(α_i)` is integral over `R` because it is the image of `h` under an `R`-algebra map `B → S'`, so
the right-hand side has integral coefficients; the coefficients then descend from `S'` to `S`
because `1, x, …, x^{d-1}` is an `S'`-basis of `S'[x]/(f)`.

## Main results

* `exists_derivative_mul_eq_and_isIntegral_coeff_and_degree_lt`: the statement above, 03GD.

## Implementation notes

The Stacks Project takes `f ∈ R[x]` monic, `B` the target of a ring map `R → B`, and states the
conclusion as `f' h = ∑_i b_i x^i` in `B[x]/(f)`. Three departures, none of them weakenings:

* The coefficient ring is an arbitrary `R`-algebra `S` (the source's `B`) and `f : S[x]` is only
  required to be monic with coefficients integral over `R`, rather than to come from `R[x]`; the
  proof uses nothing else about `f`.
* The quotient is presented abstractly: `B` is any `R`-algebra together with a surjection
  `φ : S[x] →ₐ[R] B` whose kernel is `Ideal.span {f}`, rather than the chosen model `S[x] ⧸ (f)`.
  So `AdjoinRoot f`, `S[x] ⧸ Ideal.span {f}` and any localization-free presentation are all
  instances, and no user has to transport along a chosen isomorphism.
* `f' h = ∑_i b_i x^i` is spelled as `φ (derivative f) * y = φ g` with `g : S[x]`: naming the
  polynomial `g` rather than its coefficient family is what the consumers use, and
  `g.coeff i` recovers the `b_i`.

The degree bound `g.degree < f.natDegree` is the one piece of genuinely new content relative to
Mathlib's `exists_derivative_mul_eq_and_isIntegral_coeff`, which proves this statement with the
bound omitted (its source file records the omission as a deliberate `TODO`). The bound is what the
source's proof actually produces — the source writes `f' h ≡ ∑_{j = 0}^{d - 1} b'_j x^j` — and
it is what makes `g` unique, since `f` is monic. It is stated with the coerced natural number
`g.degree < (f.natDegree : WithBot ℕ)` rather than `g.degree < f.degree`, so that it is also true
when `S` is the zero ring, where `f.degree = ⊥`; the two agree as soon as `S` is nontrivial. The
declaration sits in the root namespace, beside the Mathlib sibling whose name it mutates.

Faithfulness against the source:

1. Every hypothesis is used: without `hφ` the conclusion fails (take `S = R = ℤ`, `f = x`,
   `B = ℤ[i]` with `φ` evaluation at `0`, `y = i`); `hf`, `hf'` and `hfx` are what make the roots
   of `f` integral and `φ f = 0`; `hy` is the hypothesis on `h`.
2. Integrality is over the source's base ring `R` throughout, never over `S` or `B`.
3. The canonical map is pinned: the projection `B[x] → B[x]/(f)` is the given `φ`, and the
   conclusion is an equation between `φ (derivative f) * y` and `φ g`, not a bare existence claim.
4. Not degenerate: `S := B`, `B := AdjoinRoot (f.map (algebraMap R B))`, `φ := AdjoinRoot.mk` with
   `f ∈ R[x]` monic is the source's own instance.

## References

* [Stacks Project, Tag 03GD](https://stacks.math.columbia.edu/tag/03GD)
-/

@[expose] public section

/-- **Stacks 03GD.** Let `S` be an `R`-algebra and let `f : S[x]` be monic with all coefficients
integral over `R`. Let `φ : S[x] →ₐ[R] B` be surjective with kernel `(f)`, so `B = S[x]/(f)`. If
`y ∈ B` is integral over `R`, then `f' y` is the class of a polynomial `g : S[x]` of degree
`< deg f` all of whose coefficients are integral over `R`. -/
public alias exists_derivative_mul_eq_and_isIntegral_coeff_and_degree_lt :=
    Stacks.Smooth.DerivativeTrick.solution

end
