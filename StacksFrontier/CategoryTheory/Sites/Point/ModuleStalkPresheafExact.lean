module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the stalk functor on modules over a site, in bundled form

Let `(C, J)` be a site, `Φ` a point of it and `R` a presheaf of rings on `C`. Taking the stalk
at `Φ` of a presheaf of `R`-modules is an exact functor to modules over the stalk of `R`. This
file records that statement in the bundled form `CategoryTheory.Limits.exactFunctor`, which is
the form Stacks 04EQ asserts.

## Main results

* `Stacks.exactFunctor_presheafModuleFiber`: part (2) of Stacks 04EQ, that the stalk functor
  on presheaves of modules is an exact functor.

Parts (1) and (3) of Stacks 04EQ — exactness of the stalk functor on *sheaves* of modules,
and the agreement of the stalk of a presheaf with the stalk of its sheafification — are
`Stacks.exactFunctor_sheafModuleFiber` and
`Stacks.isIso_moduleFiberSheafificationComparison`, in this same namespace.

## Implementation notes

The mathematics is not proved here. Exactness of `Stacks.presheafModuleFiber` is already
available as the two instances `Stacks.instPreservesFiniteLimitsPresheafModuleFiber` and
`Stacks.instPreservesFiniteColimitsPresheafModuleFiber` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleStalkFunctor.lean`, both proved there by
reflection along `forget₂ (ModuleCat _) AddCommGrpCat`. Since
`CategoryTheory.Limits.exactFunctor_iff` is `Iff.rfl`, all that is needed is to package them,
and that is all this file does; it exists so that the bundled form has a name to cite.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (R : Cᵒᵖ ⥤ RingCat.{w})

/-- **Stacks 04EQ, part (2).** Taking the stalk at a point of a site is an exact functor from
presheaves of `R`-modules to modules over the stalk of `R`. -/
@[stacks 04EQ "part (2)"]
theorem exactFunctor_presheafModuleFiber :
    exactFunctor (PresheafOfModules.{w} R)
      (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R))
      (presheafModuleFiber Φ R) :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

end Stacks
