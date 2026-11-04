module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
import StacksCore.Tactic.StacksAttribute

/-!
# Local rings along a flat morphism of normal schemes

Stacks Tag 0BD7 reduces to its affine case by applying that case to
`Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}`. This file supplies the two local hypotheses that reduction
needs and that are not otherwise available by instance search: that a stalk of a normal scheme
is integrally closed, and that the map of local rings induced by a flat morphism is faithfully
flat.

The first is literally the field `AlgebraicGeometry.IsNormal.stalk_normal` of the class
`AlgebraicGeometry.IsNormal` (Tag 033I), which is not declared as an instance where the class
is defined; with it, and with Mathlib's `IsFractionRing (X.presheaf.stalk x) X.functionField`
and `IsNoetherianRing (X.presheaf.stalk x)`, the stalk of an integral, locally Noetherian,
normal scheme is found by instance search to be a Noetherian local normal domain with fraction
field the function field — which is the ring `R` of the affine step of Tag 0BD7.

The second is faithful flatness, which Tag 0BD7 uses to descend an equality of ideals from the
upstairs ring to the base. A flat morphism induces a flat map on local rings, and a map of
local rings is local, so the induced map is faithfully flat.

## Main results

* `AlgebraicGeometry.IsNormal.instIsIntegrallyClosedStalk`: the stalks of a normal scheme are
  integrally closed, as an instance.
* `AlgebraicGeometry.Flat.faithfullyFlat_stalkMap`: a flat morphism of schemes induces a
  faithfully flat map on local rings.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The local rings of a normal scheme are integrally closed. This is the field
`AlgebraicGeometry.IsNormal.stalk_normal`, made available to instance search. -/
instance IsNormal.instIsIntegrallyClosedStalk {X : Scheme.{u}} [IsNormal X] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) :=
  IsNormal.stalk_normal x

/-- A flat morphism of schemes induces a faithfully flat map on local rings: the map is flat,
and a map of local rings induced by a morphism of schemes is local. -/
theorem Flat.faithfullyFlat_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end AlgebraicGeometry

end
