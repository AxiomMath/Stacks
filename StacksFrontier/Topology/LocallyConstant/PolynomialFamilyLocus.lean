module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Loci of prescribed values of polynomial families of locally constant functions

Let `χ : X → ℤ → ℤ` be a family of functions on a topological space, each `x ↦ χ x n` locally
constant.  The locus `{x | ∀ n, χ x n = P n}` is always closed, being an intersection of fibres of
locally constant functions; in general it is not open.  It is open when, near every point, the
functions `n ↦ χ x n` are given by rational polynomials of uniformly bounded degree `d`: two such
functions agreeing at `0, …, d` agree everywhere, so near a point of the locus it is cut out by
the finitely many conditions `χ x n = χ x₀ n` for `n ≤ d`.

This is the argument by which the condition of having a prescribed Hilbert polynomial is open
and closed in a family: the twisted Euler characteristics `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are
polynomials of degree at most the dimension of the support of `𝓕_t`, and that dimension is
locally bounded on the base.

## Main definitions

* `IsPolynomialOfDegreeLE`: a function `ℤ → ℤ` given by a rational polynomial of degree at
  most `d`.

## Main results

* `IsPolynomialOfDegreeLE.eq_of_forall_range`: two such functions agreeing at
  `0, …, d` are equal.
* `isClopen_setOf_forall_eq_of_locally_isPolynomialOfDegreeLE` and
  `isClopen_setOf_forall_eq_of_isPolynomialOfDegreeLE_of_locallyBounded`: the locus of
  prescribed values of a family of locally constant functions which is locally polynomial of
  bounded degree is open and closed.
-/

@[expose] public section

open Polynomial Topology

/-- A function `f : ℤ → ℤ` is *polynomial of degree at most `d`* when it is the restriction to
the integers of a rational polynomial of degree at most `d`. -/
def IsPolynomialOfDegreeLE (f : ℤ → ℤ) (d : ℕ) : Prop :=
  ∃ p : ℚ[X], p.natDegree ≤ d ∧ ∀ n : ℤ, (f n : ℚ) = p.eval (n : ℚ)

/-- Being polynomial of degree at most `d` is monotone in `d`. -/
theorem IsPolynomialOfDegreeLE.mono {f : ℤ → ℤ} {d e : ℕ} (hf : IsPolynomialOfDegreeLE f d)
    (hde : d ≤ e) : IsPolynomialOfDegreeLE f e :=
  let ⟨p, hp, hfp⟩ := hf
  ⟨p, hp.trans hde, hfp⟩

/-- **Two functions which are polynomial of degree at most `d` and agree at `0, …, d` are
equal**: the two polynomials agree at `d + 1` distinct points. -/
theorem IsPolynomialOfDegreeLE.eq_of_forall_range {f g : ℤ → ℤ} {d : ℕ}
    (hf : IsPolynomialOfDegreeLE f d) (hg : IsPolynomialOfDegreeLE g d)
    (h : ∀ n < d + 1, f n = g n) : f = g := by
  obtain ⟨p, hp, hfp⟩ := hf
  obtain ⟨q, hq, hgq⟩ := hg
  let s : Finset ℚ := (Finset.range (d + 1)).image fun n : ℕ => (n : ℚ)
  have hdeg : ∀ r : ℚ[X], r.natDegree ≤ d → r.degree < s.card := fun r hr => by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact (degree_le_of_natDegree_le hr).trans_lt (WithBot.coe_lt_coe.2 d.lt_succ_self)
  obtain rfl : p = q := by
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (hdeg p hp) (hdeg q hq) fun x hx => ?_
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    have h1 := hfp n
    have h2 := hgq n
    push_cast at h1 h2
    rw [← h1, ← h2, h n (Finset.mem_range.1 hn)]
  funext n
  exact_mod_cast (hfp n).trans (hgq n).symm

variable {X : Type*} [TopologicalSpace X]

/-- **The locus of prescribed values of a locally polynomial family of locally constant functions
is open and closed.**  Let `χ : X → ℤ → ℤ` be such that each `x ↦ χ x n` is locally constant and
that near every point the functions `n ↦ χ x n` are polynomial of uniformly bounded degree.  Then
for every `P : ℤ → ℤ` the locus `{x | ∀ n, χ x n = P n}` is open and closed. -/
theorem isClopen_setOf_forall_eq_of_locally_isPolynomialOfDegreeLE {χ : X → ℤ → ℤ}
    (hχ : ∀ n, IsLocallyConstant fun x => χ x n)
    (hdeg : ∀ x, ∃ U ∈ 𝓝 x, ∃ d : ℕ, ∀ y ∈ U, IsPolynomialOfDegreeLE (χ y) d) (P : ℤ → ℤ) :
    IsClopen {x | ∀ n, χ x n = P n} := by
  refine ⟨?_, isOpen_iff_mem_nhds.2 fun x hx => ?_⟩
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun n => ((hχ n).isClopen_fiber (P n)).isClosed
  · obtain ⟨U, hU, d, hd⟩ := hdeg x
    have hV : {y | ∀ n < d + 1, χ y n = χ x n} ∈ 𝓝 x := by
      have : {y | ∀ n < d + 1, χ y n = χ x n} =
          ⋂ n ∈ Finset.range (d + 1), {y | χ y n = χ x n} := by
        ext y
        simp
      rw [this, Filter.biInter_finset_mem]
      exact fun n _ => ((hχ n).isClopen_fiber (χ x n)).isOpen.mem_nhds rfl
    filter_upwards [hU, hV] with y hyU hyV
    intro n
    rw [IsPolynomialOfDegreeLE.eq_of_forall_range (hd y hyU) (hd x (mem_of_mem_nhds hU)) hyV]
    exact hx n

/-- **The locus of prescribed values is open and closed when the degree is bounded by a locally
bounded function.**  This is the form in which the bound by the dimension of the support of a
fibre, which is locally bounded on the base, is used. -/
theorem isClopen_setOf_forall_eq_of_isPolynomialOfDegreeLE_of_locallyBounded {χ : X → ℤ → ℤ}
    (hχ : ∀ n, IsLocallyConstant fun x => χ x n) {δ : X → ℕ}
    (hpoly : ∀ x, IsPolynomialOfDegreeLE (χ x) (δ x))
    (hδ : ∀ x, ∃ U ∈ 𝓝 x, ∃ d : ℕ, ∀ y ∈ U, δ y ≤ d) (P : ℤ → ℤ) :
    IsClopen {x | ∀ n, χ x n = P n} :=
  isClopen_setOf_forall_eq_of_locally_isPolynomialOfDegreeLE hχ
    (fun x => let ⟨U, hU, d, hd⟩ := hδ x; ⟨U, hU, d, fun y hy => (hpoly y).mono (hd y hy)⟩) P
