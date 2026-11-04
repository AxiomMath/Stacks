module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwistQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperVanishing

/-!
# The Hilbert polynomial of a high twist is the dimension of its global sections

For a coherent sheaf `ℱ` on projective space over a field, the Hilbert polynomial evaluated at
a sufficiently large integer `d` is `dim_k H⁰(ℙⁿ, ℱ(d))`: all the higher cohomology of `ℱ(d)`
vanishes once `d` is large, so the alternating sum defining the Hilbert polynomial collapses to
its degree-zero term. This is [Stacks, Tag 08AE]. Here projective space is the model
`AlgebraicGeometry.projectiveSpaceOverRing`, and the vanishing of [Stacks, Tag 01YS] is a
hypothesis.

## Main results

* `AlgebraicGeometry.finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero`: an
  alternating sum of dimensions of cohomology collapses to its degree-zero term when all the
  positive-degree cohomology vanishes.
* `AlgebraicGeometry.exists_forall_isZero_cohomologyOverField_projectiveTwist`: finitely many
  separate vanishing bounds give one bound valid in every positive degree at once.
* `AlgebraicGeometry.hilbertPolynomial_eq_finrank_cohomologyOverField_zero`: the Hilbert
  polynomial at a twist with no higher cohomology is the dimension of the global sections of
  that twist.
* `AlgebraicGeometry.exists_hilbertPolynomial_eval_eq_finrank_zero`: the statement of
  [Stacks, Tag 08AE], from a uniform vanishing bound.
* `AlgebraicGeometry.exists_hilbertPolynomial_eval_eq_finrank_zero_of_lt`: the same with the
  vanishing needed only in the finitely many positive degrees below the affine covering number.
* `AlgebraicGeometry.exists_hilbertPolynomial_eval_eq_finrank_zero_of_isZero_hgroup`: the same
  from the conclusion of [Stacks, Tag 01YS] assertion (4), stated for the cohomology `Hgroup`.

## References

* [Stacks Project, Tag 08AE](https://stacks.math.columbia.edu/tag/08AE)
* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/


@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- **An alternating sum of dimensions of cohomology collapses to its degree-zero term** when
all the positive-degree cohomology vanishes. -/
public theorem finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)
    (hvan : ∀ i : ℕ, 0 < i → IsZero (cohomologyOverField k f F i)) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k f F i) : ℤ)) =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) := by
  classical
  have hs : Function.support
      (fun i : ℕ => (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k f F i) : ℤ)) ⊆
      ({0} : Finset ℕ) := by
    intro i hi
    by_contra hi0
    have := ModuleCat.subsingleton_of_isZero (hvan i (Nat.pos_of_ne_zero (by simpa using hi0)))
    simp [Function.mem_support, Module.finrank_zero_of_subsingleton] at hi
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp

variable (k : Type u) [Field k] (n : ℕ)

/-- **One vanishing bound in every positive degree at once.** If for each positive degree below
`N` the cohomology of the twists vanishes from some degree `d₀ i` on, and from degree `N` on it
vanishes for every twist, then there is a single `d₀` beyond which every positive-degree
cohomology group of the twist vanishes. -/
public theorem exists_forall_isZero_cohomologyOverField_projectiveTwist
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (N : ℕ)
    (hlt : ∀ i : ℕ, 0 < i → i < N → ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i))
    (hge : ∀ i : ℕ, N ≤ i → ∀ d : ℤ,
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i) := by
  classical
  let b : ℕ → ℤ := fun i => if h : 0 < i ∧ i < N then (hlt i h.1 h.2).choose else 0
  refine ⟨((Finset.Ico 1 N).sup fun i => (b i).toNat : ℕ), fun d hd i hi => ?_⟩
  by_cases hiN : i < N
  · refine (hlt i hi hiN).choose_spec d (le_trans ?_ hd)
    rw [show (hlt i hi hiN).choose = b i by simp [b, hi, hiN]]
    exact (Int.self_le_toNat (b i)).trans <| mod_cast
      Finset.le_sup (f := fun j : ℕ => (b j).toNat) (Finset.mem_Ico.2 ⟨hi, hiN⟩)
  · exact hge i (by lia) d

/-- **The Hilbert polynomial at a twist with no higher cohomology** is the dimension over the
ground field of the global sections of that twist. -/
public theorem hilbertPolynomial_eq_finrank_cohomologyOverField_zero
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (d : ℤ)
    (hvan : ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i)) :
    hilbertPolynomial k n F d =
      (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) 0) : ℤ) :=
  finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k _ _ hvan

/-- **[Stacks, Tag 08AE] from a uniform vanishing bound.** Let `ℱ` be a coherent sheaf on
projective space over a field and let `P` be a rational polynomial agreeing with its Hilbert
polynomial at every integer. If beyond some twist degree all the positive-degree cohomology of
the twists vanishes — the content of [Stacks, Tag 01YS] — then beyond that degree `P(d)` is the
dimension over the ground field of the global sections of the `d`-th twist. -/
public theorem exists_hilbertPolynomial_eval_eq_finrank_zero
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (hvan : ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i))
    (P : Polynomial ℚ) (hP : ∀ d : ℤ, P.eval (d : ℚ) = (hilbertPolynomial k n F d : ℚ)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      P.eval (d : ℚ) = (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) 0) : ℚ) := by
  obtain ⟨d₀, hd₀⟩ := hvan
  refine ⟨d₀, fun d hd => ?_⟩
  rw [hP d, hilbertPolynomial_eq_finrank_cohomologyOverField_zero k n F d (hd₀ d hd)]
  norm_cast

/-- **[Stacks, Tag 08AE] with the vanishing needed only below the affine covering number.** Let
`ℱ` be a coherent sheaf on projective space over a field and let `P` be a rational polynomial
agreeing with its Hilbert polynomial at every integer. If in each positive degree below the affine
covering number of projective space the cohomology of the twists vanishes from some twist degree
on, then beyond some twist degree `P(d)` is the dimension over the ground field of the global
sections of the `d`-th twist. -/
public theorem exists_hilbertPolynomial_eval_eq_finrank_zero_of_lt
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (hlt : ∀ i : ℕ, 0 < i → i < (projectiveSpaceOverRing n (.of k)).affineCoverNum ⊤ →
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
        IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
          (projectiveTwist n F d) i))
    (P : Polynomial ℚ) (hP : ∀ d : ℤ, P.eval (d : ℚ) = (hilbertPolynomial k n F d : ℚ)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      P.eval (d : ℚ) = (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) 0) : ℚ) :=
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exists_hilbertPolynomial_eval_eq_finrank_zero k n F
    (exists_forall_isZero_cohomologyOverField_projectiveTwist k n F _ hlt
      fun i hi d => isZero_cohomologyOverField_of_affineCoverNum_le k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) i hi)
    P hP

/-- **[Stacks, Tag 08AE] from [Stacks, Tag 01YS] assertion (4) stated verbatim.** Let `ℱ` be a
coherent sheaf on projective space over a field and let `P` be a rational polynomial agreeing
with the Hilbert polynomial of `ℱ` at every integer. Suppose that in each positive degree `i`
the cohomology group `Hⁱ(ℙⁿ, ℱ(d))` vanishes for all `d` large, which is the conclusion of
[Stacks, Tag 01YS] assertion (4). Then beyond some twist degree `P(d)` is the dimension over the
ground field of the global sections of `ℱ(d)`. -/
public theorem exists_hilbertPolynomial_eval_eq_finrank_zero_of_isZero_hgroup
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (hvan : ∀ i : ℕ, 0 < i → ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of k)).ringCatSheaf ⊤ i
        (projectiveTwist n F d)))
    (P : Polynomial ℚ) (hP : ∀ d : ℤ, P.eval (d : ℚ) = (hilbertPolynomial k n F d : ℚ)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      P.eval (d : ℚ) = (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) 0) : ℚ) :=
  exists_hilbertPolynomial_eval_eq_finrank_zero_of_lt k n F
    (fun i hi _ =>
      let ⟨d₀, hd₀⟩ := hvan i hi
      ⟨d₀, fun d hd =>
        (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ i).2 (hd₀ d hd)⟩)
    P hP

end AlgebraicGeometry

end
