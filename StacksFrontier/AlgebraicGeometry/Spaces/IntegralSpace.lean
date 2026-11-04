module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Integral algebraic spaces

An algebraic space over a scheme `S` is *integral* when it is reduced, decent, and its space
of points is irreducible.

Reducedness of an algebraic space is reducedness as an étale-local property of schemes, in
the sense of `AlgebraicGeometry.Space.HasEtaleLocalProperty`; irreducibility is irreducibility
of `|X|` for the canonical topology `AlgebraicGeometry.Space.pointTopology` on the
field-valued points of `X`. Decency is asked for in addition because without it the point set
of an algebraic space can be irreducible for reasons that have nothing to do with the
geometry of the space.

## Main definitions

* `AlgebraicGeometry.Space.IsIntegralSpace` is integrality of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace`,
  `AlgebraicGeometry.Space.IsIntegralSpace.hasEtaleLocalProperty_isReduced` and
  `AlgebraicGeometry.Space.IsIntegralSpace.irreducibleSpace` read off the three conditions.
* `AlgebraicGeometry.Space.IsIntegralSpace.finite_irreducibleComponents`: an integral
  algebraic space has finitely many irreducible components, having exactly one.

## Implementation notes

The predicate is stated for an arbitrary presheaf on the big fppf site over `S`, rather than
for one carrying an `AlgebraicGeometry.IsAlgebraicSpace` hypothesis: all three conditions
make sense without that hypothesis, and a client which has it can simply apply the predicate
to its space. In particular no algebraicity argument is needed to form the point topology,
`AlgebraicGeometry.Space.pointTopology` being defined on the points of any presheaf.

The definition is kept as an `abbrev`, as for `AlgebraicGeometry.Space.IsDecentSpace`, so
that the three conjuncts are directly available to statements about integral spaces without
an unfolding lemma.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 0AD4.** An algebraic space over `S` is *integral* when it is reduced, decent,
and its space of points is irreducible. -/
@[stacks 0AD4]
abbrev IsIntegralSpace : Prop :=
  HasEtaleLocalProperty B S hS F (fun Y : Scheme.{u} => IsReduced Y) ∧
    IsDecentSpace B S hS F ∧ IrreducibleSpace (points B S hS F)

/-- An integral algebraic space is reduced. -/
theorem IsIntegralSpace.hasEtaleLocalProperty_isReduced (h : IsIntegralSpace B S hS F) :
    HasEtaleLocalProperty B S hS F (fun Y : Scheme.{u} => IsReduced Y) := h.1

/-- An integral algebraic space is decent. -/
theorem IsIntegralSpace.isDecentSpace (h : IsIntegralSpace B S hS F) :
    IsDecentSpace B S hS F := h.2.1

/-- The space of points of an integral algebraic space is irreducible, in particular
nonempty. -/
theorem IsIntegralSpace.irreducibleSpace (h : IsIntegralSpace B S hS F) :
    IrreducibleSpace (points B S hS F) := h.2.2

/-- A space of points which is irreducible has exactly one irreducible component, so in
particular finitely many. -/
theorem finite_irreducibleComponents_of_irreducibleSpace
    (h : IrreducibleSpace (points B S hS F)) :
    (irreducibleComponents (points B S hS F)).Finite := by
  rw [irreducibleComponents_eq_singleton]
  exact Set.finite_singleton _

/-- An integral algebraic space has finitely many irreducible components: its space of points
is irreducible, so it has exactly one. -/
theorem IsIntegralSpace.finite_irreducibleComponents (h : IsIntegralSpace B S hS F) :
    (irreducibleComponents (points B S hS F)).Finite :=
  finite_irreducibleComponents_of_irreducibleSpace B S hS F h.2.2

end AlgebraicGeometry.Space

end
