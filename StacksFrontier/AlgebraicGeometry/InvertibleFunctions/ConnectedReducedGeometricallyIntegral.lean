module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.GroupTheory.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ConnectedReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.VarietyFieldConditions

/-!
# Invertible functions on a geometrically integral scheme over a field

Stacks Tag 04L7 says that for `k` a field and `X` a connected reduced scheme, locally of finite
type over `k`, with finitely many irreducible components, the group `𝒪(X)^*/k^*` of invertible
global functions modulo the constants is a finitely generated abelian group as soon as one of

1. the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`,
2. `X` has a `k`-rational point, or
3. `X` is geometrically integral

holds.  Conditions (1) and (2) are treated in
`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/ConnectedReducedBaseChange.lean`; this file
treats condition (3).  It is separate because the reduction of (3) to (1) is the one carried out
for Tag 04L8 in
`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/VarietyFieldConditions.lean`, which already
imports the proof of 04L7 under condition (1).

The source omits the verification that (3) implies (1).  It is the classical argument, and it is
available here as
`AlgebraicGeometry.integralClosure_globalSections_eq_bot_of_geometricallyIntegral`:
a geometrically integral `X` is integral, its function field is a separable extension of `k`
because `X` is geometrically reduced (Tag 04KS), and `k` is separably closed in that function
field because `X` is geometrically irreducible (Tag 054Q); so `k` is algebraically closed in the
function field, and the global sections embed in it.

## Main results

* `AlgebraicGeometry.mem_range_of_isIntegralElem_of_geometricallyIntegral`: **(3) implies (1).**
  On a geometrically integral scheme over `k`, every global section integral over `k` is a
  constant.
* `AlgebraicGeometry.fg_units_quotient_of_geometricallyIntegral`: **Tag 04L7 under condition (3)**.

## Implementation notes

Condition (1) is consumed by `AlgebraicGeometry.fg_units_quotient_of_integrallyClosed` in the
elementwise spelling "every global section integral over `k` lies in the image of `k`", so the
bridge lemma here converts `integralClosure k Γ(X, 𝒪_X) = ⊥` into that form.

Connectedness, reducedness and the finiteness of the set of irreducible components are standing
hypotheses of the proposition and are kept in the statement below, even though condition (3)
implies all three: a geometrically integral scheme over a field is integral.

## References

* [Stacks Project, Tag 04L7](https://stacks.math.columbia.edu/tag/04L7)
* [Stacks Project, Tag 04L8](https://stacks.math.columbia.edu/tag/04L8)
* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Tag 04L7, condition (3) implies condition (1).** Let `k` be a field and let `X` be an
integral scheme over `k` which is geometrically integral.  Then every global section of `X` which
is integral over `k` is a constant, i.e. the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`.

This is `AlgebraicGeometry.integralClosure_globalSections_eq_bot_of_geometricallyIntegral` in the
elementwise spelling that the proof of 04L7 under condition (1) consumes. -/
theorem mem_range_of_isIntegralElem_of_geometricallyIntegral (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsIntegral X] (hgi : GeometricallyIntegral f)
    (a : Γ(X, ⊤)) (ha : (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).IsIntegralElem a) :
    a ∈ Set.range ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hmem : a ∈ integralClosure k Γ(X, ⊤) := ha
  rw [integralClosure_globalSections_eq_bot_of_geometricallyIntegral k X f hgi] at hmem
  exact Algebra.mem_bot.mp hmem

/-- **Stacks Project, Tag 04L7 under its condition (3).** Let `k` be a field and let `X` be a
connected reduced scheme, locally of finite type over `k`, with finitely many irreducible
components, and suppose `X` is geometrically integral over `k`.  Then the group of invertible
global functions on `X` modulo the constants coming from `k` is a finitely generated abelian
group.

Condition (3) implies condition (1) by `mem_range_of_isIntegralElem_of_geometricallyIntegral`, and
`fg_units_quotient_of_integrallyClosed` is the proposition under condition (1). -/
@[stacks 04L7 "geometrically_integral"]
theorem fg_units_quotient_of_geometricallyIntegral (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] [LocallyOfFiniteType f]
    (hX : (irreducibleComponents (X : Type u)).Finite) (hgi : GeometricallyIntegral f) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) :=
  have : GeometricallyIntegral f := hgi
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  fg_units_quotient_of_integrallyClosed k X f hX fun a ha =>
    mem_range_of_isIntegralElem_of_geometricallyIntegral k X f hgi a ha

end AlgebraicGeometry

end
