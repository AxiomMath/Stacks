module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# Morphisms of quasi-coherent modules on a groupoid, through a named compatibility condition

A morphism of quasi-coherent modules on a groupoid in algebraic spaces, Stacks 0441, is a
morphism `h` of the underlying modules on the space of objects together with the compatibility
`α ∘ s^*h = t^*h ∘ α'` of `AlgebraicGeometry.Space.QuasicoherentModule.Hom`.  This file names
that compatibility, `AlgebraicGeometry.Space.QuasicoherentModule.Compatible`, and gives the
smart constructor `AlgebraicGeometry.Space.QuasicoherentModule.homMk` building a morphism from
`h` and a proof of it, together with the two round trips and the identity and composition
equations for the underlying morphism.

Nothing here is new mathematics: `homMk` is the structure constructor and
`AlgebraicGeometry.Space.QuasicoherentModule.compatibleEquiv` says so.  What the naming buys is a
*small* statement for the compatibility condition, which is what lets a functor into the
category of quasi-coherent modules on a groupoid be assembled at all; see the implementation
notes.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.Compatible` is the compatibility of a morphism of
  the underlying modules with the two transition morphisms.
* `AlgebraicGeometry.Space.QuasicoherentModule.homMk` builds a morphism of quasi-coherent
  modules on a groupoid from a compatible morphism of the underlying modules.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.homMk_hom` and
  `AlgebraicGeometry.Space.QuasicoherentModule.homMk_hom_self` are the two round trips, and
  `AlgebraicGeometry.Space.QuasicoherentModule.compatibleEquiv` is the resulting bijection
  between the morphisms and the compatible morphisms of the underlying modules.
* `AlgebraicGeometry.Space.QuasicoherentModule.id_hom` and
  `AlgebraicGeometry.Space.QuasicoherentModule.comp_hom`: the underlying morphism of an identity
  is an identity and that of a composite is the composite.

## Implementation notes

The compatibility condition is an equation between morphisms of `𝒪_R`-modules, and at these
types the *statement* of such an equation is a very large term: the `CategoryTheory.Quiver`
instance it is stated at carries the whole tower
`AlgebraicGeometry.Space.smallEtaleRingedSite … |>.ringSheaf` through
`CategoryTheory.SheafOfModules`, and each of the two objects carries it again.  Written out, the
condition runs to tens of thousands of nodes.

The kernel's deterministic budget is per declaration, and checking such a statement *once*
already costs a large part of it.  A declaration that both carries the condition written out in
its type and does any further work with it — the compatibility field of a morphism built at a
concrete pair of quasi-coherent modules, say — exceeds the budget, and that is the obstruction
that kept the inverse image of Stacks 0442 and the functor of Stacks 03M3 from being assembled.
Measurably: with the condition written out, a declaration whose body is only
`⟨h, hc⟩` for hypotheses `h` and `hc` is a kernel timeout, while the same body with `hc` taken
from an existing morphism is fine.

Naming the condition removes the written-out form from every statement downstream: `homMk` pays
for it once, with the two modules and the morphism still variables — which is the cheap case,
since the projections are then irreducible — and every later declaration mentions only
`Compatible h`.  This is why the two functors can be assembled through `homMk` and not through
the structure constructor.

The same accounting applies to anything else large that a `CategoryTheory.Functor` bundle would
repeat in the type of each of its four fields — in particular to the object map, when the source
category is not itself a category of quasi-coherent modules on a groupoid.  The two users of
this file are
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupoidQuasicoherentPullbackFunctor.lean`,
Stacks 0442, and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentFromSpaceBaseFunctor.lean`,
Stacks 03M3;  the second has to name its object map as well, and says so.

## References

* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

namespace QuasicoherentModule

variable {M N P : QuasicoherentModule B S hS G}

/-- The compatibility of a morphism `h` of the underlying modules on the space of objects with
the transition morphisms of two quasi-coherent modules on a groupoid in algebraic spaces: the
condition `α ∘ s^*h = t^*h ∘ α'` which is the second field of
`AlgebraicGeometry.Space.QuasicoherentModule.Hom`. -/
def Compatible (h : M.F.obj ⟶ N.F.obj) : Prop :=
  M.alpha ≫ (modulePullback B S hS G.source).map h =
    (modulePullback B S hS G.target).map h ≫ N.alpha

/-- **A compatible morphism of the underlying modules is a morphism of quasi-coherent modules on
the groupoid.**  This is the constructor of
`AlgebraicGeometry.Space.QuasicoherentModule.Hom`, with the compatibility condition named; see
the implementation notes for why the name is what makes it usable. -/
def homMk (h : M.F.obj ⟶ N.F.obj) (hc : Compatible h) : M ⟶ N where
  hom := h
  comm := hc

/-- The underlying morphism of a morphism of quasi-coherent modules on a groupoid is
compatible. -/
theorem compatible_hom (f : M ⟶ N) : Compatible f.hom :=
  Hom.comm f

/-- The underlying morphism of `AlgebraicGeometry.Space.QuasicoherentModule.homMk` is the given
one. -/
@[simp]
theorem homMk_hom (h : M.F.obj ⟶ N.F.obj) (hc : Compatible h) : (homMk h hc).hom = h :=
  rfl

/-- Building a morphism of quasi-coherent modules on a groupoid from its own underlying
morphism returns it. -/
@[simp]
theorem homMk_hom_self (f : M ⟶ N) : homMk f.hom (compatible_hom f) = f :=
  rfl

/-- Morphisms of quasi-coherent modules on a groupoid in algebraic spaces are exactly the
compatible morphisms of the underlying modules on the space of objects.

This is the same bijection as
`AlgebraicGeometry.Space.QuasicoherentModule.homEquiv` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentAbelian.lean`, which lands in the
additive subgroup of the compatible morphisms rather than in the subtype;  it is named
differently so that the two can coexist. -/
def compatibleEquiv : (M ⟶ N) ≃ { h : M.F.obj ⟶ N.F.obj // Compatible h } where
  toFun f := ⟨f.hom, compatible_hom f⟩
  invFun h := homMk h.1 h.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying morphism of an identity is an identity. -/
@[simp]
theorem id_hom (M : QuasicoherentModule B S hS G) : (𝟙 M : M ⟶ M).hom = 𝟙 M.F.obj :=
  rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_hom (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

end QuasicoherentModule

end AlgebraicGeometry.Space

end
