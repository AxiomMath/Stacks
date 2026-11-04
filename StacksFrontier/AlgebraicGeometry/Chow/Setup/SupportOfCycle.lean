module

public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CycleSupport
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a cycle

Let `(S, δ)` be a Chow situation and let `X` be locally of finite type over `S`. A cycle on `X`
is a locally finite formal sum `α = ∑ n_Z [Z]` over the integral closed subschemes `Z ⊆ X`, and
its support is the union of those `Z` whose coefficient is nonzero. This file defines that union
and identifies it with Mathlib's topological support of the cycle.

In this library a cycle is `AlgebraicGeometry.AlgebraicCycle X ℤ`, that is a function
`X → ℤ` with locally finite support, the coefficient of the integral closed subscheme
`Z = closure {x}` being recorded at its generic point `x`; an integral closed subscheme is
represented by its underlying irreducible closed subset, as in `Stacks.Chow.deltaDimension` and
`Stacks.Chow.cyclesOfDimension`. The coefficient `n_Z` of `Z : IrreducibleCloseds X` in a cycle
`α` is therefore `α Z.isIrreducible.genericPoint`, and `Supp(α) = ⋃_{n_Z ≠ 0} Z` is the
definition `Stacks.Chow.cycleSupport` below.

## Main definitions

* `Stacks.Chow.cycleSupport` — the support of a cycle, as the union of the integral closed
  subschemes occurring in it with a nonzero coefficient (Stacks 0H46).

## Main results

* `Stacks.Chow.cycleSupport_eq_biUnion_closure_singleton` — the same union, indexed by the
  points carrying a nonzero coefficient rather than by integral closed subschemes.
* `Stacks.Chow.cycleSupport_eq_tsupport` — the support of a cycle is its topological support,
  so the generic `tsupport` API applies to it. This is the bridge that makes the registration
  of 0H46 on `tsupport` meaningful.
* `Stacks.Chow.isClosed_cycleSupport` — the support of a cycle is closed.
* `Stacks.Chow.cycleSupport_eq_biUnion_deltaDimension` — for a `k`-cycle the integral closed
  subschemes occurring in the union all have delta-dimension `k`.

## Implementation notes

For a general function `c : X → R` on a topological space the union `⋃_{c x ≠ 0} closure {x}`
is strictly smaller than `tsupport c = closure {x | c x ≠ 0}` — take for instance the function
on `Spec ℤ` which is `1` at every closed point and `0` at the generic point, whose topological
support is everything while the union of the closures of its support is the set of closed
points. The two agree as soon as the family of closures of the points of the support is locally
finite, which is `Stacks.Chow.tsupport_eq_biUnion_closure_singleton`. Local finiteness of the
support is part of the datum of a cycle, so for cycles the identification
`Stacks.Chow.cycleSupport_eq_tsupport` holds with no further hypothesis: that is exactly the
local finiteness condition imposed on `∑ n_Z [Z]` in Stacks 02QR.

The support of a cycle depends neither on the base situation `(S, δ)`, nor on the structure
morphism `X ⟶ S`, nor on the dimension `k` of the cycle, so `cycleSupport` is defined for every
cycle on every scheme; `cycleSupport_eq_biUnion_deltaDimension` records what the grading of
Stacks 02QR adds for a cycle in `Z_k(X)`.

## References

* [Stacks Project, Tag 0H46](https://stacks.math.columbia.edu/tag/0H46)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The support of a cycle -/

/-- **Stacks 0H46.** The support of a cycle `α = ∑ n_Z [Z]` on `X`, namely the union
`Supp(α) = ⋃_{n_Z ≠ 0} Z` of the integral closed subschemes occurring in `α` with a nonzero
coefficient.

An integral closed subscheme of `X` is given by its underlying irreducible closed subset
`Z : IrreducibleCloseds X`, and a cycle is a locally finitely supported function on the points
of `X` which records the coefficient of `Z` at the generic point of `Z`, so that
`n_Z = α Z.isIrreducible.genericPoint`. -/
@[stacks 0H46 "support of a cycle", ega "IV 21.6.1"]
def cycleSupport (α : AlgebraicCycle X ℤ) : Set X :=
  ⋃ Z ∈ {Z : IrreducibleCloseds X | α Z.isIrreducible.genericPoint ≠ 0}, (Z : Set X)

/-- A point lies in the support of a cycle exactly when it lies on an integral closed subscheme
occurring in the cycle with a nonzero coefficient. -/
theorem mem_cycleSupport_iff {α : AlgebraicCycle X ℤ} {x : X} :
    x ∈ cycleSupport α ↔
      ∃ Z : IrreducibleCloseds X, α Z.isIrreducible.genericPoint ≠ 0 ∧ x ∈ (Z : Set X) := by
  simp [cycleSupport]

/-- The support of a cycle, indexed by points instead of by integral closed subschemes: the
integral closed subscheme carrying the coefficient at `x` is `closure {x}`. -/
@[ega "IV 21.6.1" "more general"]
theorem cycleSupport_eq_biUnion_closure_singleton (α : AlgebraicCycle X ℤ) :
    cycleSupport α = ⋃ x ∈ Function.support (α : X → ℤ), closure {x} := by
  refine subset_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · obtain ⟨Z, hZ, hyZ⟩ := mem_cycleSupport_iff.mp hy
    refine mem_iUnion₂.mpr ⟨Z.isIrreducible.genericPoint, Function.mem_support.mpr hZ, ?_⟩
    rwa [Z.isIrreducible.closure_genericPoint Z.isClosed]
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    set Z : IrreducibleCloseds X :=
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ with hZdef
    have hpt : Z.isIrreducible.genericPoint = x :=
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq (isGenericPoint_closure (x := x))
    exact mem_cycleSupport_iff.mpr ⟨Z, by rw [hpt]; exact hx, hyx⟩

/-- A point lies in the support of a cycle exactly when it is a specialization of a point
carrying a nonzero coefficient. -/
theorem mem_cycleSupport_iff_exists_point {α : AlgebraicCycle X ℤ} {y : X} :
    y ∈ cycleSupport α ↔ ∃ x : X, α x ≠ 0 ∧ y ∈ closure ({x} : Set X) := by
  rw [cycleSupport_eq_biUnion_closure_singleton]
  simp [Function.mem_support]

/-- **The support of a cycle is its topological support.** Mathlib's `tsupport` is the closure
of the set of points carrying a nonzero coefficient, whereas `Supp(α)` is the union of the
integral closed subschemes occurring in `α`; the two agree because the local finiteness built
into a cycle makes that union closed. -/
@[ega "IV 21.6.1" "more general"]
theorem cycleSupport_eq_tsupport (α : AlgebraicCycle X ℤ) :
    cycleSupport α = tsupport (α : X → ℤ) := by
  have h : LocallyFiniteSupport (α : X → ℤ) := Function.locallyFinsupp.locallyFiniteSupport α
  rw [cycleSupport_eq_biUnion_closure_singleton, tsupport_eq_biUnion_closure_singleton h]

/-- The support of a cycle is a closed subset of `X`. -/
theorem isClosed_cycleSupport (α : AlgebraicCycle X ℤ) : IsClosed (cycleSupport α) := by
  rw [cycleSupport_eq_tsupport]
  exact isClosed_tsupport _

/-- Every point carrying a nonzero coefficient lies in the support. -/
theorem support_subset_cycleSupport (α : AlgebraicCycle X ℤ) :
    Function.support (α : X → ℤ) ⊆ cycleSupport α := by
  rw [cycleSupport_eq_tsupport]
  exact subset_tsupport _

/-- The zero cycle has empty support. -/
@[simp]
theorem cycleSupport_zero : cycleSupport (0 : AlgebraicCycle X ℤ) = ∅ := by
  rw [cycleSupport_eq_tsupport]
  simp

/-- A cycle vanishes at every point outside its support. -/
theorem eq_zero_of_notMem_cycleSupport {α : AlgebraicCycle X ℤ} {x : X}
    (hx : x ∉ cycleSupport α) : α x = 0 :=
  Function.notMem_support.mp fun h ↦ hx (support_subset_cycleSupport α h)

/-! ### The support of a cycle of a fixed delta-dimension -/

/-- For a `k`-cycle in the sense of Stacks 02QR, the integral closed subschemes whose union is
the support all have delta-dimension `k`. -/
theorem cycleSupport_eq_biUnion_deltaDimension (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (α : CycleGroup C f k) :
    cycleSupport (α : AlgebraicCycle X ℤ) =
      ⋃ Z ∈ {Z : IrreducibleCloseds X |
          (α : AlgebraicCycle X ℤ) Z.isIrreducible.genericPoint ≠ 0 ∧
            deltaDimension C f Z = k}, (Z : Set X) := by
  have hmem := (mem_cyclesOfDimension C f k (α : AlgebraicCycle X ℤ)).mp α.2
  have hS : {Z : IrreducibleCloseds X |
        (α : AlgebraicCycle X ℤ) Z.isIrreducible.genericPoint ≠ 0} =
      {Z : IrreducibleCloseds X |
        (α : AlgebraicCycle X ℤ) Z.isIrreducible.genericPoint ≠ 0 ∧
          deltaDimension C f Z = k} :=
    Set.ext fun Z ↦ ⟨fun h ↦ ⟨h, hmem Z h⟩, And.left⟩
  rw [cycleSupport, hS]

end Stacks.Chow
