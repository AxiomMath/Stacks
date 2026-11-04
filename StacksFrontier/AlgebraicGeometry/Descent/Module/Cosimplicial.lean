module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian modules over a cosimplicial algebra

For a cosimplicial algebra `A`, a cosimplicial `A`-module consists of a module in
each cosimplicial degree and semilinear transition maps satisfying the usual
identity and composition laws. It is cartesian when every transition map becomes
an isomorphism after extension of scalars.

## Main definitions

* `CategoryTheory.CosimplicialModule` is a module varying cosimplicially over a cosimplicial
  commutative algebra.
* `CategoryTheory.CosimplicialModule.baseChangeMap` is the map induced from a transition map by
  extension of scalars.
* `CategoryTheory.CosimplicialModule.Cartesian` is the cartesian condition.

## Implementation notes

Cosimplicial modules are represented by Mathlib's category of modules over a
presheaf of rings, using the double-opposite equivalence for the simplex
category. Transition maps are therefore morphisms into a restriction of
scalars. The extension--restriction adjunction gives the induced base-change
map canonically. The tensor product used by `ModuleCat.extendScalars` has the
scalar algebra as its left factor; commutativity identifies this with the
ordering in the source.

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory

/-- The presheaf of underlying rings associated to a cosimplicial commutative
`R`-algebra. -/
abbrev cosimplicialRingPresheaf {R : Type u} [CommRing R]
    (A : CosimplicialObject (CommAlgCat.{v, u} R)) :=
  unopUnop SimplexCategory ⋙ A ⋙ forget₂ (CommAlgCat R) CommRingCat

/-- A cosimplicial module over a cosimplicial commutative algebra. -/
abbrev CosimplicialModule {R : Type u} [CommRing R]
    (A : CosimplicialObject (CommAlgCat.{v, u} R)) :=
  PresheafOfModulesOfCommRing.{w} (cosimplicialRingPresheaf A)

namespace CosimplicialModule

variable {R : Type u} [CommRing R] {A : CosimplicialObject (CommAlgCat.{v, u} R)}

/-- The map from the extension of scalars of the module in the source degree to
the module in the target degree induced by a cosimplicial transition map. -/
noncomputable def baseChangeMap (M : CosimplicialModule A) {n m : SimplexCategory}
    (f : n ⟶ m) :
    (ModuleCat.extendScalars (A.map f).hom.toRingHom).obj (M.obj (op (op n))) ⟶
      M.obj (op (op m)) :=
  (ModuleCat.extendRestrictScalarsAdj (A.map f).hom.toRingHom).homEquiv _ _
    |>.symm (M.map f.op.op)

/-- A cosimplicial module is cartesian when every cosimplicial transition map
induces an isomorphism after extension of scalars. -/
@[stacks 039Y "cartesian_module"]
abbrev Cartesian (M : CosimplicialModule A) : Prop :=
  ∀ {n m : SimplexCategory} (f : n ⟶ m), IsIso (M.baseChangeMap f)

end CosimplicialModule

end CategoryTheory
