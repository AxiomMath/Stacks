module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Cohomology over an object of a site is right-derived sections

For an abelian sheaf on a small site, Mathlib's cohomology over an object of the site is an
`Ext`-group out of the free abelian sheaf on that object's Yoneda presheaf. This file identifies
it with the right-derived functor of sections over the object.

## Main results

* `Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections`: the
  `Ext`-functors out of the free abelian sheaf on `yoneda.obj U` are the right-derived functors
  of sections over `U`.
* `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`:
  `Sheaf.H' F p U ≅ (((sheafSections J Ab).obj (op U)).rightDerived p).obj F`.

## Implementation notes

Sections over an object of the site are corepresented by the sheafification of the free abelian
presheaf on `yoneda.obj U` — the object `Stacks.Cohomology.ModuleComparison.freeSectionsSheaf`,
with the corepresentation `ModuleSheafCohomology.evaluationRepresentation` — and that
sheafification is exactly the object Mathlib's `Sheaf.cohomologyPresheafFunctor` takes `Ext` out
of. So the comparison is an instance of
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`: for an additive, left exact
functor to abelian groups corepresented by an object `Z`, the right-derived functors agree with
the `Ext`-functors out of `Z`.

Only existence is asserted upstream, so `cohomologyIsoRightDerivedSections` is a choice and no
compatibility in degree zero with the canonical map to the right-derived functor is claimed.

This generalizes `Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`, which is
the same comparison for the site of opens of a topological space; the proof there uses nothing
about opens, only the corepresentation,
which `ModuleSheafCohomology.evaluationRepresentation` already supplies for an arbitrary small
site. The left exactness and additivity of sections over an object, and the corepresenting free
sheaf itself, are `Stacks.Cohomology.ModuleComparison.siteSections_preservesFiniteLimits`,
`.siteSections_additive` and `.freeSectionsSheaf`; nothing about them is restated here.

The `Ext` universe is forced to be the morphism universe of the site. The corepresentation
identifies sections over `U` with `preadditiveCoyoneda.obj (op (freeSectionsSheaf J U))`, whose
values live in the category's own morphism universe, so the comparison with right-derived
functors is only available for `Ext` in that universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.SiteSections

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The `Ext`-functors out of the free abelian sheaf on `yoneda.obj U` are the right-derived
functors of sections over `U`.** Sections over `U` are corepresented by
`Stacks.Cohomology.ModuleComparison.freeSectionsSheaf J U`, so this is an instance of
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`. -/
theorem nonempty_extFunctorObj_iso_rightDerived_sheafSections [HasSheafify J Ab.{u}]
    [HasExt.{u} (Sheaf J Ab.{u})] [HasInjectiveResolutions (Sheaf J Ab.{u})]
    (U : C) (p : ℕ) :
    Nonempty (Abelian.extFunctorObj (ModuleComparison.freeSectionsSheaf J U) p ≅
      ((sheafSections J Ab.{u}).obj (op U)).rightDerived p) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived
    ((sheafSections J Ab.{u}).obj (op U)) _
    (ModuleSheafCohomology.evaluationRepresentation J U) p

/-- **Cohomology over an object of the site is right-derived sections.** For an abelian sheaf `F`
on a small site, Mathlib's `Sheaf.H' F p U` — the `p`-th `Ext`-group from the free abelian sheaf
on `yoneda.obj U` to `F` — is identified with the `p`-th right-derived functor of sections over
`U`, evaluated at `F`.

This is a choice: see `nonempty_extFunctorObj_iso_rightDerived_sheafSections`. -/
def cohomologyIsoRightDerivedSections [HasSheafify J Ab.{u}]
    [HasExt.{u} (Sheaf J Ab.{u})] [HasInjectiveResolutions (Sheaf J Ab.{u})]
    (F : Sheaf J Ab.{u}) (p : ℕ) (U : C) :
    Sheaf.H'.{u, u, u} F p U ≅ (((sheafSections J Ab.{u}).obj (op U)).rightDerived p).obj F :=
  (nonempty_extFunctorObj_iso_rightDerived_sheafSections J U p).some.app F

end Stacks.Cohomology.SiteSections

end
