module

public import Mathlib.FieldTheory.Normal.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFiniteSupportStrong

/-!
# Normal finite residue extensions absorb every conjugate

The finite-support reduction in Epp's degree-prime argument must work in every field factor of a
separable base change, not only in the factor selected by one embedding.  The elementary reason a
single finite extension can do this is normality: once a normal extension contains one root of a
minimal polynomial, it contains every conjugate root.

This file records that field-theoretic step independently of the valuation-ring bookkeeping.  It
does not assert that a finite set exhausts a perfect core, and it does not descend a weak solution
from a distinguished factor.
-/

@[expose] public section

namespace Stacks.EppTheorem

open Polynomial

universe u v w z

/-- A normal extension contains, in every common overfield, every conjugate of each of its
elements.  This is the pointwise mechanism needed to make finite coefficient absorption uniform
over all reduced tensor factors. -/
theorem mem_fieldRange_of_normal_of_minpoly_eq
    {k : Type u} {N : Type v} {Ω : Type w}
    [Field k] [Field N] [Field Ω]
    [Algebra k N] [Algebra k Ω] [Algebra N Ω] [IsScalarTower k N Ω]
    [Normal k N]
    (x : Ω) (hx : IsIntegral k x) (y : N)
    (hmin : minpoly k y = minpoly k x) :
    x ∈ (algebraMap N Ω).fieldRange := by
  rw [RingHom.mem_fieldRange]
  exact hx.mem_range_algebraMap_of_minpoly_splits (hmin ▸ Normal.splits ‹_› y)

/-- A finite family of separable coefficients is absorbed in every common factor once a normal
base extension contains one representative of each minimal polynomial.  The `K → Ω` map may be
any conjugate factor map; no distinguished embedding is selected. -/
theorem finset_maps_mem_fieldRange_of_normal
    {k : Type u} {K : Type z} {N : Type v} {Ω : Type w}
    [Field k] [Field K] [Field N] [Field Ω]
    [Algebra k K] [Algebra k N] [Algebra k Ω]
    [Algebra K Ω] [Algebra N Ω]
    [IsScalarTower k K Ω] [IsScalarTower k N Ω]
    [Normal k N]
    (s : Finset K)
    (hrep : ∀ x ∈ s, IsIntegral k x ∧ ∃ y : N, minpoly k y = minpoly k x) :
    ∀ x ∈ s, algebraMap K Ω x ∈ (algebraMap N Ω).fieldRange := by
  intro x hx
  obtain ⟨hint, y, hmin⟩ := hrep x hx
  exact mem_fieldRange_of_normal_of_minpoly_eq _ (hint.map (IsScalarTower.toAlgHom k K Ω)) y
    (hmin.trans (minpoly.algebraMap_eq (algebraMap K Ω).injective x).symm)

/-- A `p ^ d`-th root taken in `K` is transported into a normal base extension `N`.

If `r : K` satisfies `r ^ p ^ d = x` and some `y : N` has the same minimal polynomial over `k` as
`r`, then `x` already has a `p ^ d`-th root in the image of `N`.  The conjugate `algebraMap K Ω r`
lies in the range of `algebraMap N Ω` by normality, and raising the witness to the `p ^ d` is what
turns that range membership into the root statement.

Only the two towers `k → K → Ω` and `k → N → Ω` are used, so `Ω` is arbitrary: no factor of a
reduced base change is distinguished, nothing is assumed complete, and `Ω` is not algebraically
closed. -/
theorem exists_pow_eq_algebraMap_of_normal
    {k : Type u} {K : Type z} {N : Type v} {Ω : Type w}
    [Field k] [Field K] [Field N] [Field Ω]
    [Algebra k K] [Algebra k N] [Algebra k Ω]
    [Algebra K Ω] [Algebra N Ω]
    [IsScalarTower k K Ω] [IsScalarTower k N Ω]
    [Normal k N]
    (p d : ℕ) (r x : K) (hr : r ^ p ^ d = x) (hint : IsIntegral k r)
    (y : N) (hmin : minpoly k y = minpoly k r) :
    ∃ z : N, algebraMap N Ω z ^ p ^ d = algebraMap K Ω x := by
  obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp <| finset_maps_mem_fieldRange_of_normal (Ω := Ω) {r}
    (by simpa using ⟨hint, y, hmin⟩) r (by simp)
  exact ⟨z, by rw [hz, ← map_pow, hr]⟩

/-- A finite family of elements, each supplied with a `p ^ d`-th root in `K` paired with a
representative of that root's minimal polynomial in a normal `N`, acquires `p ^ d`-th roots from
`N` in *every* common overfield `Ω`.

The hypothesis is exactly a family of paired root representatives: for each `x ∈ s` a root
`r : K` of `X ^ p ^ d - x` together with a `y : N` conjugate to it.  The conclusion is stated
pointwise over `s` and for a variable `Ω`, so a single normal `N` — for instance the one produced
by `exists_normal_finite_minpoly_representatives` applied to the roots — serves all reduced
factors of a base change simultaneously, with no factor selected. -/
theorem finset_exists_pow_eq_algebraMap_of_normal
    {k : Type u} {K : Type z} {N : Type v} {Ω : Type w}
    [Field k] [Field K] [Field N] [Field Ω]
    [Algebra k K] [Algebra k N] [Algebra k Ω]
    [Algebra K Ω] [Algebra N Ω]
    [IsScalarTower k K Ω] [IsScalarTower k N Ω]
    [Normal k N]
    (p d : ℕ) (s : Finset K)
    (hrep : ∀ x ∈ s, ∃ r : K, r ^ p ^ d = x ∧ IsIntegral k r ∧
      ∃ y : N, minpoly k y = minpoly k r) :
    ∀ x ∈ s, ∃ z : N, algebraMap N Ω z ^ p ^ d = algebraMap K Ω x := by
  intro x hx
  obtain ⟨r, hr, hint, y, hmin⟩ := hrep x hx
  exact exists_pow_eq_algebraMap_of_normal p d r x hr hint y hmin

/-- **A finite set of integral elements has a single finite normal extension realising all of its
minimal polynomials.**

Take `p` to be the product of the minimal polynomials of the elements of `s` and `N` its splitting
field.  Then `N / k` is finite and normal, and each `minpoly k x` for `x ∈ s`, dividing `p`, splits
in `N` and so is the minimal polynomial of some `y : N`.

This is the finite-coefficient input to `finset_maps_mem_fieldRange_of_normal`: one extension,
built from the finitely many coefficients actually in play, which then absorbs every one of them in
*every* conjugate factor at once.  In particular no statement is made — and none is needed — about
a perfect core being exhausted by a finite set, which would be false in general since the perfect
core need not be finite over `k`.

Only normality of `N` is used, so separability of `s` is not assumed; when the elements of `s` are
separable the same `N` is Galois over `k`. -/
theorem exists_normal_finite_minpoly_representatives
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Finset K) (hint : ∀ x ∈ s, IsIntegral k x) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : Normal k N), ∀ x ∈ s, ∃ y : N, minpoly k y = minpoly k x := by
  classical
  have hp0 : (∏ x ∈ s, minpoly k x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hint x hx)
  refine ⟨(∏ x ∈ s, minpoly k x).SplittingField, inferInstance, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_⟩
  set N := (∏ x ∈ s, minpoly k x).SplittingField
  have hsplit : ((minpoly k x).map (algebraMap k N)).Splits :=
    (Polynomial.IsSplittingField.splits (L := N) (∏ x ∈ s, minpoly k x)).of_dvd
      (Polynomial.map_ne_zero hp0)
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ hx))
  have hdeg : ((minpoly k x).map (algebraMap k N)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap k N).injective]
    exact (minpoly.degree_pos (hint x hx)).ne'
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdeg
  refine ⟨y, (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (hint x hx)) ?_
    (minpoly.monic (hint x hx))).symm⟩
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map]

end Stacks.EppTheorem

end
