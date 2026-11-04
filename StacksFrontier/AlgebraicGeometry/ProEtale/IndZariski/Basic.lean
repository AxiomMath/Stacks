module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.LocalIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Ind-Zariski algebras

A ring map is *ind-Zariski* when its target is a filtered colimit, as an algebra over the
source, of local isomorphisms.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsIndZariski`: the ind-Zariski property of a commutative algebra.

## Main results

* `AlgebraicGeometry.ProEtale.indZariski_lift_index_universe`: the ind-Zariski property is
  preserved when the universe of the index category is enlarged.

## Implementation notes

The filtered-colimit presentation is `CategoryTheory.ObjectProperty.ind` in the category of
commutative algebras over the source ring, taken for the object property `Algebra.IsLocalIso`.
The stages have carrier universe `max u v`, where `u` and `v` are the independent universes of
the source and target rings; the target is lifted into that universe with `ULift`. Restricting
the stages to the target universe would impose a size bound absent from the definition.
The index-category universe is independent of the algebra-carrier universe, so base change can
retain the same index category. Since the predicate is an abbreviation, the existing API for
`ObjectProperty.ind` applies to it directly; that local isomorphisms are finitely presentable,
and the resulting stability of ind-Zariski algebras under filtered colimits (Tag 096S), are in
`StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.FilteredColimit`.

## References

* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

universe u v w

/-- A commutative `A`-algebra is ind-Zariski if it is a filtered colimit of
`A`-algebras whose structure maps are local isomorphisms. The stages and the lifted
target lie in the maximum of the source and target carrier universes. -/
@[stacks 096N]
abbrev IsIndZariski (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ObjectProperty.ind.{w} (fun C : CommAlgCat.{max u v} A => Algebra.IsLocalIso A C)
    (CommAlgCat.of A (ULift.{u} B))

universe w'

/-- The ind-Zariski property is insensitive to enlarging the universe of the index category: a
filtered colimit presentation indexed in one universe is reindexed by a small model of its index
category in any larger one. -/
theorem indZariski_lift_index_universe (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (h : IsIndZariski.{u, v, w} A B) : IsIndZariski.{u, v, max w w'} A B := by
  obtain ⟨J, _, _, pres, hP⟩ := h
  have : EssentiallySmall.{max w w'} J := essentiallySmallSelf J
  exact ObjectProperty.of_essentiallySmall_index pres hP

end AlgebraicGeometry.ProEtale

end
