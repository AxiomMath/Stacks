module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NoncommExtendScalarsSheaf

/-!
# Extension of scalars carries the unit module to the unit module

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site.  Extension of scalars along `α` is
informally `R' ⊗_R -`, so it carries `R` regarded as a module over itself to `R' ⊗_R R`, which is
`R'`.  This file records that identification for
`Stacks.NoncommChangeOfRings.Sheaf.extendScalars`, the form of Stacks 03CZ that exists over an
arbitrary site and for sheaves of not necessarily commutative rings.

It is the base case of every argument that extension of scalars carries free modules to free
modules: a free module is a coproduct of copies of the unit module, and extension of scalars
preserves coproducts, being a left adjoint.

## Main definitions

* `Stacks.NoncommChangeOfRings.Sheaf.extendScalarsObjUnitIso`: `R' ⊗_R R ≅ R'`.

## Implementation notes

The identification is not proved by hand.  Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is
the comparison `f^*(unit) ⟶ unit` for its pullback of sheaves of modules along a continuous
functor of sites, and is an isomorphism;
`Stacks.NoncommChangeOfRings.Sheaf.extendScalarsIsoPullback` identifies extension of scalars with
that pullback along the identity functor of the site.  So the content is Mathlib's, and what this
file adds is its availability for the unconditional extension of scalars.

The instance `(SheafOfModules.pushforward (structureMap α)).IsRightAdjoint` that Mathlib's
comparison needs is supplied by hand rather than by instance search, which does not find it
inside its heartbeat budget: restriction of scalars along `α` *is* that pushforward, and
`Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction` exhibits it as a right
adjoint.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory

universe u u' v'

namespace Stacks.NoncommChangeOfRings.Sheaf

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Extension of scalars carries the unit module to the unit module**: for a morphism
`α : R ⟶ R'` of sheaves of rings on a site, `R' ⊗_R R ≅ R'`. -/
noncomputable def extendScalarsObjUnitIso :
    (extendScalars.{u} α).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit R' :=
  haveI : (SheafOfModules.pushforward.{u}
      (Stacks.SheafOfModules.ChangeOfRings.structureMap α)).IsRightAdjoint :=
    (extendRestrictScalarsAdjunction.{u} α).isRightAdjoint
  (extendScalarsIsoPullback.{u} α).app (SheafOfModules.unit R) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit
      (Stacks.SheafOfModules.ChangeOfRings.structureMap α))

end Stacks.NoncommChangeOfRings.Sheaf

end
