module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction

/-!
# The cycle presented by a locally finite family of closed subschemes

A locally finite family `(W_j)_j` of closed subschemes of a scheme `X` locally of finite type
over the base of a Chow situation, together with integer coefficients `n_j`, determines the
coefficient function `x ↦ ∑_j n_j [W_j]_k(x)`. This file shows that this function is the
coefficient function of an actual `k`-cycle, so that a presentation `α = ∑_j n_j [W_j]_k` of a
cycle by closed subschemes may be read in the other direction: the family *defines* a cycle.

Together with the translation of a relative dimension condition at the generic points of an
irreducible scheme into a statement about its delta-dimension, this is what turns the family
produced by Stacks 02S4 part (4) into input for the Gysin maps of Stacks 0B6Z, whose component
formula is stated against a presentation by integral closed subschemes of delta-dimension
`k + 1`.

## Main results

* `Stacks.Chow.exists_integralFamilyCycle` — the cycle presented by a locally finite family of
  closed subschemes with integer coefficients.
* `Stacks.Chow.schemeDeltaDimension_of_relativeDimension_genericPoints` — on an irreducible
  scheme a relative dimension known at all generic points is the delta-dimension.

## Implementation notes

The grading needs no dimension hypothesis on the members of the family: each `[W_j]_k` is a
`k`-cycle by construction (Stacks 02QU), so at a point where the sum is nonzero some summand is
nonzero, and that summand already forces the delta-dimension to be `k`. Local finiteness of the
support is `Stacks.Chow.locallyFiniteSupport_finsum_of_locallyFinite`, applied with the supports
of the members as the containing family.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Delta-dimension from the generic points -/

/-- On an irreducible scheme the delta-dimension of chapter 42 is the relative dimension at the
generic point, so a relative dimension known at every generic point determines it. -/
theorem schemeDeltaDimension_of_relativeDimension_genericPoints (C : ChowSituation.{u})
    {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q] [IrreducibleSpace (Z : Type u)]
    (m : ℤ)
    (h : ∀ ξ : genericPoints (Z : Type u),
      relativeDimension C.dimensionFunction q ξ.1 = m) :
    schemeDeltaDimension C q = ((m : ℤ) : EInt) := by
  have hmem : genericPoint (Z : Type u) ∈ genericPoints (Z : Type u) := by
    rw [genericPoints_eq_singleton]
    rfl
  rw [schemeDeltaDimension_eq_genericPoint C q, h ⟨genericPoint (Z : Type u), hmem⟩]

/-! ### The cycle presented by a family -/

/-- **The cycle presented by a locally finite family of closed subschemes.** Given a locally
finite family `(W_j)_j` of closed subschemes of `X` and integers `n_j`, the function
`x ↦ ∑_j n_j [W_j]_k(x)` is the coefficient function of a `k`-cycle on `X`.

Each summand is a `k`-cycle by Stacks 02QU, which gives the grading, and the supports of the
members bound the supports of the summands, which gives local finiteness of the support. -/
theorem exists_integralFamilyCycle (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {J : Type u} (W : J → X.IdealSheafData)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ) :
    ∃ β : CycleGroup C p k, ∀ x : X, β.1 x =
      ∑ᶠ j : J, n j * (cycleAssociatedToClosedSubscheme C p (W j).subschemeι k).1 x := by
  let c := fun j ↦ cycleAssociatedToClosedSubscheme C p (W j).subschemeι k
  have hsub : ∀ j, Function.support (fun x ↦ n j * (c j).1 x) ⊆ ((W j).support : Set X) := by
    intro j x hx
    have h := support_cycleAssociatedToClosedSubscheme_subset C p (W j).subschemeι k
      (right_ne_zero_of_mul hx)
    rwa [Scheme.IdealSheafData.range_subschemeι] at h
  have hlfs : ∀ j, LocallyFiniteSupport (fun x ↦ n j * (c j).1 x) := by
    intro j z
    obtain ⟨t, ht, hfin⟩ := (c j).1.locallyFiniteSupport z
    exact ⟨t, ht, hfin.subset (Set.inter_subset_inter_right _ fun x hx ↦
      right_ne_zero_of_mul hx)⟩
  have hloc := locallyFiniteSupport_finsum_of_locallyFinite
    (fun j ↦ ((W j).support : Set X)) hLocal (fun j x ↦ n j * (c j).1 x) hsub hlfs
  refine ⟨⟨⟨fun x ↦ ∑ᶠ j : J, n j * (c j).1 x, by simp, fun z _ ↦ hloc z⟩, ?_⟩, fun _ ↦ rfl⟩
  intro Z hZ
  obtain ⟨j, hj⟩ : ∃ j, n j * (c j).1 Z.isIrreducible.genericPoint ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hZ (finsum_eq_zero_of_forall_eq_zero h)
  exact (mem_cyclesOfDimension C p k _).1 (c j).2 Z (right_ne_zero_of_mul hj)

end Stacks.Chow

end
