module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.LocalIso

import StacksCore.Tactic.StacksAttribute

/-!
# Ind-Zariski ring maps

A ring map `A → B` is *ind-Zariski* if `B` is a filtered colimit of `A`-algebras `B i` all of
whose structure maps `A → B i` are local isomorphisms.

## Main definitions

* `CommAlgCat.localIso` is the object property of `R`-algebras that are local isomorphisms.
* `Algebra.IsIndZariski` is the ind-Zariski property of an algebra, with the base and the
  algebra in independent universes.

## Main results

* `Algebra.isIndZariski_iff`: with the base and the algebra in a common universe, the lifted
  condition is the plain `ObjectProperty.ind` condition.
* `Algebra.IsLocalIso.isIndZariski`: a local isomorphism is ind-Zariski.

## Implementation notes

The filtered-colimit presentation is `CategoryTheory.ObjectProperty.ind` in the category
`CommAlgCat` of commutative algebras over the base, applied to the object property
`CommAlgCat.localIso`, which is the direct analogue of Mathlib's `CommAlgCat.etale`.

Universes are handled exactly as for `StacksDraft.IndEtale`: for `A : Type u` and
`B : Type v`, the carrier universe of the ambient category is `max u v` and `B` is lifted into
it with `ULift`, because `CommAlgCat.{w} A` only contains `A`-algebras of size `w`. Restricting
the carrier universe to the universe of `B` alone would impose a size bound that the source
definition does not have. The index universe of the filtered colimit is *pinned* to `max u v`
as well, again following `StacksDraft.IndEtale`: left free it would be a third universe
parameter of the predicate, so `IsIndZariski.{u, v, w}` and `IsIndZariski.{u, v, w'}` would be
two a priori different notions and no consumer could tell which one it had.

## References

* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CommAlgCat

/-- The object property of `R`-algebras that are local isomorphisms over `R`. This is the
analogue for `Algebra.IsLocalIso` of Mathlib's `CommAlgCat.etale`. -/
abbrev localIso (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Algebra.IsLocalIso R S

end CommAlgCat

namespace Algebra

/-- An `A`-algebra `B` is *ind-Zariski* if it is a filtered colimit of `A`-algebras whose
structure maps are local isomorphisms. The stages and the lifted algebra live in
`CommAlgCat.{max u v} A`, where `u` and `v` are the independent universes of the base and of the
algebra, and the filtered index category is taken in that same universe.

This is the `w := max u v` case of `AlgebraicGeometry.ProEtale.IsIndZariski`, which leaves the
index universe free; the two are the same term, since `CommAlgCat.localIso R` unfolds to
`fun S ↦ Algebra.IsLocalIso R S`. Tag 096N is registered there, on the general statement, and not
here. -/
abbrev IsIndZariski (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  (CommAlgCat.localIso.{u, max u v} A).ind.{max u v} (CommAlgCat.of A (ULift.{u} B))

/-- With the base and the algebra in a common universe, the lifted ind-Zariski condition is the
plain one. -/
theorem isIndZariski_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    IsIndZariski A B ↔ (CommAlgCat.localIso A).ind.{u} (CommAlgCat.of A B) :=
  ⟨(CommAlgCat.localIso A).ind.prop_of_iso (CommAlgCat.isoMk ULift.algEquiv),
    (CommAlgCat.localIso A).ind.prop_of_iso (CommAlgCat.isoMk ULift.algEquiv.symm)⟩

/-- A local isomorphism is ind-Zariski: it is the colimit of the one-object diagram on
itself. -/
theorem IsLocalIso.isIndZariski (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsLocalIso A B] : IsIndZariski A B :=
  ObjectProperty.le_ind (CommAlgCat.localIso.{u, max u v} A) _
    (Algebra.IsLocalIso.of_algEquiv (ULift.algEquiv (R := A) (A := B)).symm)

end Algebra

end
