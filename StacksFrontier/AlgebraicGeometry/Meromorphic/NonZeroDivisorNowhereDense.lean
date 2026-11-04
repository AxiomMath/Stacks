module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Topology.NowhereDense.Defs

/-!
# The vanishing locus of a nonzerodivisor is nowhere dense

Let `X` be a scheme, `U` an affine open of `X` and `b ∈ Γ(X, U)` a nonzerodivisor. Then the
locus in `U` where `b` vanishes is nowhere dense in `X`. This is the topological input of the
support clauses of Stacks Tag 02P0: there the denominator ideal `I` of a regular meromorphic
section satisfies `(b) ⊆ I` on a suitable affine open, so `V(I) ⊆ V(b)` is nowhere dense.

## Main results

* `AlgebraicGeometry.inf_basicOpen_ne_bot_of_mem_nonZeroDivisors`: on an affine open, the basic
  open of a nonzerodivisor meets every nonempty open subset. Equivalently, that basic open is
  dense in the affine open.
* `AlgebraicGeometry.isNowhereDense_sdiff_basicOpen_of_mem_nonZeroDivisors`: the complement of
  that basic open inside the affine open is nowhere dense in `X`.

## Implementation notes

The ring-theoretic content is a single line: if `b` is a nonzerodivisor and `f * b` is
nilpotent then `f` is nilpotent, because `fⁿ bⁿ = 0` and `bⁿ` is again a nonzerodivisor. The
translation into geometry is
`AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`
— which needs only quasi-compactness of `U` — together with
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`, which needs `U` affine and supplies a
basic open of `U` inside a given open neighbourhood.

Nowhere density is then proved by hand rather than through a subspace argument. Writing
`Z = U \ X.basicOpen b`, the set `Z` is closed in `U` because `X.basicOpen b ≤ U`, so
`closure Z ∩ U = Z`; and a point of `interior (closure Z)` lies in `closure U`, so its
neighbourhood `interior (closure Z)` meets `U` in a nonempty open subset of `U` disjoint from
`X.basicOpen b`, contradicting density.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A power of a nonzerodivisor only annihilates what the element itself annihilates: if `f * b`
is nilpotent and `b` is a nonzerodivisor, then `f` is nilpotent. -/
theorem isNilpotent_of_isNilpotent_mul_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {f b : R} (hb : b ∈ R⁰) (h : IsNilpotent (f * b)) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, (mem_nonZeroDivisors_iff_right.mp (pow_mem hb n)) _ ?_⟩
  rw [← mul_pow]
  exact hn

/-- On an affine open `U` of a scheme, the basic open set of a nonzerodivisor `b ∈ Γ(X, U)` meets
every nonempty open subset of `U`: it is dense in `U`. -/
theorem inf_basicOpen_ne_bot_of_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U)
    {b : Γ(X, U)} (hb : b ∈ (Γ(X, U))⁰) {W : X.Opens} (hWU : W ≤ U) (hW : W ≠ ⊥) :
    W ⊓ X.basicOpen b ≠ ⊥ := by
  obtain ⟨x, hx⟩ := W.ne_bot_iff_nonempty.mp hW
  obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWU hx)
  have hnil := Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU.isCompact
  have hmul : X.basicOpen (f * b) ≠ ⊥ := fun hbot =>
    (X.basicOpen f).ne_bot_iff_nonempty.mpr ⟨x, hxf⟩ ((hnil f).mp
      (isNilpotent_of_isNilpotent_mul_of_mem_nonZeroDivisors hb ((hnil _).mpr hbot)))
  refine fun hbot => hmul (le_bot_iff.mp ?_)
  rw [← hbot, X.basicOpen_mul]
  exact inf_le_inf_right _ hfW

/-- **The vanishing locus of a nonzerodivisor is nowhere dense.** On an affine open `U` of a
scheme, the part of `U` where a nonzerodivisor `b ∈ Γ(X, U)` vanishes is a nowhere dense subset
of `X`. -/
theorem isNowhereDense_sdiff_basicOpen_of_mem_nonZeroDivisors {U : X.Opens}
    (hU : IsAffineOpen U) {b : Γ(X, U)} (hb : b ∈ (Γ(X, U))⁰) :
    IsNowhereDense ((U : Set X) \ (X.basicOpen b : Set X)) := by
  set Z : Set X := (U : Set X) \ (X.basicOpen b : Set X) with hZdef
  have hcl : closure Z ⊆ (X.basicOpen b : Set X)ᶜ :=
    closure_minimal (fun y hy => hy.2) (X.basicOpen b).isOpen.isClosed_compl
  rw [IsNowhereDense, Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxU : x ∈ closure (U : Set X) :=
    closure_mono (fun y hy => hy.1) (interior_subset hx)
  obtain ⟨y, hyInt, hyU⟩ := mem_closure_iff.mp hxU _ isOpen_interior hx
  set W : X.Opens := ⟨interior (closure Z) ∩ (U : Set X),
    isOpen_interior.inter U.isOpen⟩ with hWdef
  have hWU : W ≤ U := fun z hz => hz.2
  have hWne : W ≠ ⊥ := W.ne_bot_iff_nonempty.mpr ⟨y, hyInt, hyU⟩
  obtain ⟨z, hzW, hzb⟩ :=
    (W ⊓ X.basicOpen b).ne_bot_iff_nonempty.mp
      (inf_basicOpen_ne_bot_of_mem_nonZeroDivisors hU hb hWU hWne)
  exact hcl (interior_subset hzW.1) hzb

end AlgebraicGeometry
