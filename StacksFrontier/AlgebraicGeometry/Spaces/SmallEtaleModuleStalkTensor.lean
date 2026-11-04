module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorMixed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The geometric stalk of a tensor product of sheaves of modules on a small étale site

Let `X` be an algebraic space over a scheme `S` and let `𝒜` be an arbitrary sheaf of
commutative rings on `X_étale`. For two sheaves of `𝒜`-modules `M` and `N` and a geometric
point `x` of `X`, the stalk at `x` of `M ⊗_𝒜 N` is the tensor product of the stalks over the
stalk ring `𝒜_x`:

`(M ⊗_𝒜 N)_x ≅ M_x ⊗_{𝒜_x} N_x`.

This is the case of Stacks 03EL at the point of the small étale site determined by `x`
(Stacks 04K0), and it is the computation the source's stalkwise proofs of Stacks 04G0 and
Stacks 0DK4 need for the *source* of their canonical map and for the inner tensor product of
its target.

## Main results

* `AlgebraicGeometry.Space.geometricModuleStalkTensorIso`: the stalk at a geometric point of a
  tensor product of sheaves of modules over an arbitrary sheaf of rings on a small étale site
  is the tensor product of the stalks.

## Implementation notes

The statement is `Stacks.tensorSheafModuleFiberIso` at
`AlgebraicGeometry.Space.etaleSitePoint`, the point of the small étale site attached to `x`.
What made it unavailable until that free-universe form existed is a universe mismatch rather
than any mathematics: the small étale site of an algebraic space has its objects in
`Type (u + 1)` and its sections in `Type u` — `AlgebraicGeometry.Space.smallEtaleRingedSite` is
a `CategoryTheory.RingedSite.{u + 1, u, u}`. `Stacks.tensorSheafModuleFiberIso` has the three
universes free, tied only by `[LocallySmall.{w} C]`, which the small étale site does satisfy —
it is what `AlgebraicGeometry.Space.etaleSitePoint` already relies on.

The sheaves of modules are taken over `Stacks.commRingSheafToRingSheaf 𝒜`, which is
`(CategoryTheory.sheafCompose _ (forget₂ CommRingCat RingCat)).obj 𝒜` and so is the same sheaf
of rings as `Stacks.SheafOfModules.Tensor.ringSheaf 𝒜` and as
`Stacks.SheafOfModules.Tensor.ringSheaf` of the small étale ringed topos of `𝒜`,
the sheaf of rings the modules of Stacks 04G0 and Stacks 0DK4 are taken over. The tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensor`, the one
`AlgebraicGeometry.Space.tensorPushforwardMap` is built from, so no transport is needed between
this computation and that map.

Both universe annotations on the type of `M` and `N` are load-bearing and neither may be
dropped. `SheafOfModules` and `Stacks.commRingSheafToRingSheaf` each carry a universe for the
objects of the site and one for its morphisms, and at this site those differ — `u + 1` and `u`.
In a binder nothing constrains them before `𝒜` is checked, so left implicit they are assigned
`0` and the binder is rejected with `𝒜` reported as having the wrong sort. Writing
`SheafOfModules.{u}` alone is not enough: that pins only the module universe. The order of the
parameters of `Stacks.commRingSheafToRingSheaf` is morphisms, objects, sections.

The stalk functor here is `Stacks.sheafModuleFiberOfCommRing`, valued in modules over the
`CommRingCat`-valued stalk of `𝒜`, because that is the ring the tensor product of the stalks is
taken over. `AlgebraicGeometry.Space.geometricModuleStalkFunctor` is the same functor before
that restriction of scalars, valued in modules over the `RingCat`-valued stalk; the two differ
by `ModuleCat.restrictScalars` along `Stacks.commRingSheafFiberIso`, which is an isomorphism of
rings, so a map of sheaves of modules is invertible on the stalks of one exactly when it is on
the stalks of the other.

Deliberately untagged, for the reason
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SitePointStalkTensorMixed.lean` records: the
clauses of Stacks 03EL are about an arbitrary morphism of ringed topoi, and a point of a site
is one particular such morphism, so this covers neither clause.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X) CommRingCat.{u})

/-- **The stalk of a tensor product of sheaves of modules at a geometric point.** For an
arbitrary sheaf of commutative rings `𝒜` on the small étale site of an algebraic space `X`, two
sheaves of `𝒜`-modules `M` and `N` and a geometric point `x` of `X`, the stalk at `x` of
`M ⊗_𝒜 N` is `M_x ⊗_{𝒜_x} N_x`.

This is `Stacks.tensorSheafModuleFiberIso` at the point of the small étale site attached to `x`
by Stacks 04K0. It is the computation the source's stalkwise proofs of Stacks 04G0 and
Stacks 0DK4 perform on the source of their canonical map. -/
noncomputable def geometricModuleStalkTensorIso (x : GeometricPoint B S hS X)
    (M N : SheafOfModules.{u, u, u + 1, u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X x hX) 𝒜).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜).obj M).obj N) ≅
      ((curriedTensor (ModuleCat.{u}
            (Stacks.ringFiber (etaleSitePoint B S hS X x hX) 𝒜.obj))).obj
          ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X x hX) 𝒜).obj M)).obj
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X x hX) 𝒜).obj N) :=
  Stacks.tensorSheafModuleFiberIso (etaleSitePoint B S hS X x hX) 𝒜 M N

end AlgebraicGeometry.Space

end
