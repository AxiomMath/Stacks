module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Restriction of scalars preserves monomorphisms of sheaves of modules

For a morphism `α : R ⟶ R'` of sheaves of rings on a site, restriction of scalars
`SheafOfModules.restrictScalars α` carries a monomorphism of sheaves of `R'`-modules to a
monomorphism of sheaves of `R`-modules.

## Main results

* `Stacks.SheafifyMono.restrictScalars_preservesMonomorphisms`:
  `(SheafOfModules.restrictScalars α).PreservesMonomorphisms`.

## Implementation notes

Restriction of scalars changes only the action, not the underlying presheaf of abelian groups.
That is recorded in Mathlib twice, and both records are definitional:
`SheafOfModules.restrictScalars_obj_val` and
`PresheafOfModules.restrictScalarsCompToPresheaf`.  So for `φ` a morphism of sheaves of
`R'`-modules, the underlying presheaf morphisms of `φ` and of `(restrictScalars α).map φ` are the
same morphism, and the two functors
`SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _` agree on it.

The two halves of the argument are therefore read off the same morphism of presheaves of abelian
groups.  On the `R'` side, `SheafOfModules.forget R'` and `PresheafOfModules.toPresheaf R'.obj`
both preserve finite limits, hence monomorphisms, so the underlying presheaf morphism of `φ` is a
monomorphism.  On the `R` side, both functors are faithful, hence reflect monomorphisms, so
`(restrictScalars α).map φ` is a monomorphism.
-/

@[expose] public section

open CategoryTheory Limits

universe v v' u'

namespace Stacks.SheafifyMono

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{v}}

/-- Restriction of scalars along a morphism `α : R ⟶ R'` of sheaves of rings preserves
monomorphisms of sheaves of modules. -/
instance restrictScalars_preservesMonomorphisms (α : R ⟶ R') :
    (SheafOfModules.restrictScalars α).PreservesMonomorphisms where
  preserves φ _ :=
    Functor.mono_of_mono_map (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)
      (show Mono ((SheafOfModules.forget R' ⋙
        PresheafOfModules.toPresheaf R'.obj).map φ) from inferInstance)

end Stacks.SheafifyMono
