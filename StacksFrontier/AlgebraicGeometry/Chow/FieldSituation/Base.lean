module

public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.Field
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Catenary

/-!
# The spectrum of a field is a Chow situation

Chapter 42 builds Chow homology over a base `(S, δ)` consisting of a locally Noetherian,
universally catenary scheme together with a dimension function on it — `Stacks.Chow.ChowSituation`.
Every statement of the chapter is quantified over such a base, so all of them are conditional
until one is exhibited.

This file exhibits one. The base is the spectrum of a field `k`, whose dimension function is the
constant zero of `AlgebraicGeometry.fieldBaseDimensionFunction`; the one nontrivial input is
universal catenarity, and that is the scheme-level reading of Tag 0A21,
`AlgebraicGeometry.isCatenarySpace_of_locallyOfFiniteType_over_field`: a scheme locally of finite
type over a field is catenary, which is exactly the defining condition of
`AlgebraicGeometry.Scheme.IsUniversallyCatenary` at `Spec k`. The dimension function costs nothing,
since `Spec k` has one point and so no non-trivial specialization at all.

The base so obtained is not degenerate: it is nonempty, so the Chow situation is not the one over
the empty scheme, for which every cycle group vanishes.

The imports of this file are the construction's own inputs and nothing else, so the witness is
available to every consumer in the chapter; the statements instantiated at it live downstream.

## Main definitions

* `Stacks.Chow.fieldDimensionFunction` — the constant-zero dimension function on `Spec k`.
* `Stacks.Chow.fieldChowSituation` — the Chow situation with base `Spec k`.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_spec_of_field` — the spectrum of a field is
  universally catenary.
* `Stacks.Chow.nonempty_chowSituation` — `Stacks.Chow.ChowSituation` is inhabited.
* `Stacks.Chow.nonempty_fieldChowSituation_base` — its base is nonempty.

## References

* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM)
* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **The spectrum of a field is universally catenary.** Universal catenarity of a locally
Noetherian scheme `S` is the condition that every scheme locally of finite type over `S` be a
catenary space, and for `S = Spec k` that is Tag 0A21,
`AlgebraicGeometry.isCatenarySpace_of_locallyOfFiniteType_over_field`. -/
theorem isUniversallyCatenary_spec_of_field (k : Type u) [Field k] :
    IsUniversallyCatenary (AlgebraicGeometry.Spec (.of k)) :=
  fun X g _ => isCatenarySpace_of_locallyOfFiniteType_over_field k X g

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

/-- The constant-zero dimension function on the spectrum of a field. Both conditions on a
dimension function are conditions on a non-trivial specialization, and `Spec k` has none: its
underlying space is a subsingleton. -/
def fieldDimensionFunction (k : Type u) [Field k] :
    DimensionFunction (AlgebraicGeometry.Spec (.of k)) where
  toFun := AlgebraicGeometry.fieldBaseDimensionFunction k
  strictAnti_specializes := fun {x y} _ hne => absurd (Subsingleton.elim x y) hne
  step_immediate := fun {x y} h => absurd (Subsingleton.elim x y) h.2.1

/-- **Stacks 02QM.** For a field `k`, the pair `(Spec k, δ)` with `δ(pt) = 0` at the unique point
is a base situation of chapter 42 (Situation 02QL): `Spec k` is Noetherian, it is universally
catenary (`AlgebraicGeometry.Scheme.isUniversallyCatenary_spec_of_field`), and the constant zero
is a dimension function on it (`Stacks.Chow.fieldDimensionFunction`). The base scheme is
`Spec k` by definition, and the dimension function vanishes by
`Stacks.Chow.fieldChowSituation_dimensionFunction`.

It is an `abbrev` so that its base scheme is reducibly `Spec k`: the cycle groups of the fibres
of a morphism are formed for this situation, and instance search on them has to see through to
`AlgebraicGeometry.Spec`. -/
@[stacks 02QM "the spectrum of a field with the zero dimension function is a Situation 02QL"]
abbrev fieldChowSituation (k : Type u) [Field k] : ChowSituation.{u} where
  S := AlgebraicGeometry.Spec (.of k)
  isUniversallyCatenary := Scheme.isUniversallyCatenary_spec_of_field k
  dimensionFunction := fieldDimensionFunction k

/-- The dimension function of `Stacks.Chow.fieldChowSituation` vanishes. -/
@[simp]
theorem fieldChowSituation_dimensionFunction (k : Type u) [Field k]
    (x : (fieldChowSituation k).S) : (fieldChowSituation k).dimensionFunction x = 0 :=
  rfl

/-- The dimension function of `Stacks.Chow.fieldChowSituation k` is the constant-zero function
`AlgebraicGeometry.fieldBaseDimensionFunction k` of Tag 02QM. -/
theorem coe_fieldChowSituation_dimensionFunction (k : Type u) [Field k] :
    ⇑(fieldChowSituation k).dimensionFunction = AlgebraicGeometry.fieldBaseDimensionFunction k :=
  rfl

/-- **The base situation of chapter 42 is inhabited.** Every statement of the chapter is
quantified over a `Stacks.Chow.ChowSituation`; this is a witness that there is one. -/
theorem nonempty_chowSituation : Nonempty ChowSituation.{u} :=
  ⟨fieldChowSituation (ULift.{u} ℚ)⟩

/-- The base of `Stacks.Chow.fieldChowSituation` is nonempty, so the witness is not the
degenerate situation over the empty scheme, where every cycle group vanishes. -/
theorem nonempty_fieldChowSituation_base (k : Type u) [Field k] :
    Nonempty (fieldChowSituation k).S :=
  inferInstanceAs (Nonempty (AlgebraicGeometry.Spec (.of k)))

end Stacks.Chow

end
