module

public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Prime divisors and Weil divisors on an algebraic space

A *prime divisor* of an algebraic space `X` is an integral closed subspace `Z ⊆ X` of
codimension one, that is, one whose generic point is a point of codimension one of `X`. A
*Weil divisor* is a formal sum `D = ∑ n_Z Z` over prime divisors whose nonzero part has
locally finite support in `|X|`. These form a group `Div(X)` under coefficientwise addition.

## Main definitions

* `AlgebraicGeometry.Space.subspacePointSet` is the set of points of `X` underlying a
  subfunctor of `X`.
* `AlgebraicGeometry.Space.PrimeDivisor` is the type of prime divisors of `X`.
* `AlgebraicGeometry.Space.WeilDivisor` is the group of Weil divisors of `X`, as the additive
  subgroup of locally finitely supported integer coefficient families on prime divisors.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isGenericPoint_genericPoint` and
  `AlgebraicGeometry.Space.PrimeDivisor.codimension_genericPoint`: the generic point of a
  prime divisor is generic in its point set and has codimension one.
* `AlgebraicGeometry.Space.mem_weilDivisor_iff` is the membership criterion for the group of
  Weil divisors.

## Implementation notes

The point set underlying a subspace is the image of its points in the ambient space, and
codimension is `codimension` of Stacks 02I3 applied to the closure of the generic point for
the canonical topology `AlgebraicGeometry.Space.pointTopology` on `|X|`. The generic point of
a prime divisor is recorded existentially in the structure, so that a prime divisor does not
carry a choice of point as data; `AlgebraicGeometry.Space.PrimeDivisor.genericPoint` extracts
one when needed.

The source states the definitions for a locally Noetherian integral algebraic space, which is
the situation in which they are used; they are stated here for an arbitrary presheaf on the
big fppf site over `S`, the extra hypotheses being carried by the clients that need them.

Local finiteness is tested on the point sets of exactly the prime divisors with nonzero
coefficient, as in the source. Presenting the Weil divisors as an `AddSubgroup` of the
coefficient families gives the group structure of `Div(X)` with no further work.

## References

* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The set of points of `X` underlying a subfunctor of `X`, that is, the image of the points
of the subfunctor under the inclusion. -/
abbrev subspacePointSet (Z : Subfunctor X) : Set (points B S hS X) :=
  Set.range (pointsMap B S hS Z.toFunctor Z.ι)

/-- **Stacks 0ENJ, part (1).** A *prime divisor* of `X` is an integral closed subspace of `X`
whose generic point has codimension one in `X`. -/
@[stacks 0ENJ "part (1): prime divisors"]
structure PrimeDivisor where
  /-- The underlying subfunctor of `X`. -/
  subspace : Subfunctor X
  /-- The subfunctor is a closed subspace of `X`. -/
  closed : IsClosedSubspace B S hS subspace
  /-- The closed subspace is an integral algebraic space. -/
  integral : IsIntegralSpace B S hS subspace.toFunctor
  /-- The generic point of the closed subspace has codimension one in `X`. -/
  codimension_one : letI := pointTopology B S hS X
    ∃ ξ : points B S hS X, IsGenericPoint ξ (subspacePointSet B S hS X subspace) ∧
      codimension (IrreducibleCloseds.closureSingleton ξ) = 1

/-- The set of points of `X` underlying a prime divisor. -/
abbrev PrimeDivisor.support (Z : PrimeDivisor B S hS X) : Set (points B S hS X) :=
  subspacePointSet B S hS X Z.subspace

/-- A generic point of a prime divisor, viewed as a point of the ambient space. -/
def PrimeDivisor.genericPoint (Z : PrimeDivisor B S hS X) : points B S hS X :=
  Classical.choose Z.codimension_one

/-- The point selected by `AlgebraicGeometry.Space.PrimeDivisor.genericPoint` is a generic
point of the point set of the prime divisor. -/
theorem PrimeDivisor.isGenericPoint_genericPoint (Z : PrimeDivisor B S hS X) :
    letI := pointTopology B S hS X
    IsGenericPoint (Z.genericPoint B S hS X) (Z.support B S hS X) :=
  (Classical.choose_spec Z.codimension_one).1

/-- The generic point of a prime divisor has codimension one in the ambient space. -/
theorem PrimeDivisor.codimension_genericPoint (Z : PrimeDivisor B S hS X) :
    letI := pointTopology B S hS X
    codimension (IrreducibleCloseds.closureSingleton (Z.genericPoint B S hS X)) = 1 :=
  (Classical.choose_spec Z.codimension_one).2

/-- A point lies in the set tested for local finiteness at a prime divisor exactly when the
coefficient there is nonzero and the point lies in the prime divisor. -/
private theorem mem_ite_support_iff {D : PrimeDivisor B S hS X → ℤ}
    {Z : PrimeDivisor B S hS X} {p : points B S hS X} :
    p ∈ (if D Z = 0 then (∅ : Set (points B S hS X))
        else PrimeDivisor.support B S hS X Z) ↔
      D Z ≠ 0 ∧ p ∈ PrimeDivisor.support B S hS X Z := by
  by_cases h : D Z = 0 <;> simp [h]

/-- **Stacks 0ENJ, part (2).** The group `Div(X)` of *Weil divisors* of `X`: integer
coefficient families on prime divisors of `X` whose nonzero part has locally finite support
in `|X|`. -/
@[stacks 0ENJ "part (2): Weil divisors"]
def WeilDivisor : AddSubgroup (PrimeDivisor B S hS X → ℤ) :=
  letI := pointTopology B S hS X
  { carrier := {D | LocallyFinite fun Z : PrimeDivisor B S hS X =>
      if D Z = 0 then ∅ else Z.support B S hS X}
    zero_mem' := fun _ => ⟨Set.univ, Filter.univ_mem, by simp⟩
    add_mem' := by
      intro D E hD hE x
      obtain ⟨U, hU, hUD⟩ := hD x
      obtain ⟨V, hV, hVE⟩ := hE x
      refine ⟨U ∩ V, Filter.inter_mem hU hV, (hUD.union hVE).subset ?_⟩
      rintro Z ⟨p, hp, hpU, hpV⟩
      obtain ⟨hne, hpZ⟩ := (mem_ite_support_iff B S hS X (D := D + E)).1 hp
      by_cases hDZ : D Z = 0
      · have hEZ : E Z ≠ 0 := by simpa only [Pi.add_apply, hDZ, zero_add] using hne
        exact Or.inr ⟨p, (mem_ite_support_iff B S hS X).2 ⟨hEZ, hpZ⟩, hpV⟩
      · exact Or.inl ⟨p, (mem_ite_support_iff B S hS X).2 ⟨hDZ, hpZ⟩, hpU⟩
    neg_mem' := by
      intro D hD
      change LocallyFinite _ at hD ⊢
      simpa only [Pi.neg_apply, neg_eq_zero] using hD }

/-- A coefficient family is a Weil divisor exactly when the point sets of the prime divisors
with nonzero coefficient form a locally finite family. -/
@[simp]
theorem mem_weilDivisor_iff (D : PrimeDivisor B S hS X → ℤ) :
    letI := pointTopology B S hS X
    D ∈ WeilDivisor B S hS X ↔ LocallyFinite fun Z : PrimeDivisor B S hS X =>
      if D Z = 0 then ∅ else Z.support B S hS X :=
  Iff.rfl

end AlgebraicGeometry.Space

end
