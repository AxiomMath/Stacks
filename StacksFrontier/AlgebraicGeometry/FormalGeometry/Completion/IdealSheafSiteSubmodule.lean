module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit

/-!
# A quasi-coherent ideal sheaf of a scheme, as a sheaf of ideals of its ringed site

`AlgebraicGeometry.Scheme.IdealSheafData` records a quasi-coherent sheaf of ideals of a scheme
by its components `ℐ(U) ⊂ Γ(X, U)` on the *affine* opens. The derived-completeness predicate of
[Stacks, Tag 0999], `AlgebraicGeometry.RingedSite.IsDerivedComplete`, is stated at a ringed site
and asks instead for a

`SheafOfModules.Submodule (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))`,

a submodule of the unit sheaf of modules, defined at *every* object of the site. This file
crosses between the two, so that derived completeness along the sheaf of ideals of an
`IdealSheafData` can be spoken of at all.

The crossing needs no new mathematics: `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`
already builds the subsheaf `ℐ^n 𝒪_X` of the unit sheaf of modules from an `IdealSheafData`, as
the least subsheaf containing `ℐ(U)^n Γ(X, U)` on every affine open — an infimum, so that it is
defined on every open and is a subsheaf by construction — and
`Stacks.Algebraization.idealPowerMultiple_unit_toSubmodule_obj_affine` computes its affine
sections. What was missing was the *name*: the small Zariski site of `X` read as a ringed site
is `Stacks.SheafOfModules.opensRingedSite X.sheaf`, and no declaration said that `ℐ^1 𝒪_X` is a
sheaf of ideals of it.

## Main definitions

* `Stacks.Algebraization.idealSheafSiteSubmodule` — the sheaf of ideals of the ringed site of `X`
  attached to `I : X.IdealSheafData`.

## Main results

* `Stacks.Algebraization.idealSheafSiteSubmodule_obj_affine` — its sections over an affine open
  `U` are `I.ideal U`, on the nose.
* `Stacks.Algebraization.mem_idealSheafSiteSubmodule_obj_affine` — the same, as a membership
  criterion, which is the form the quantifier of
  `AlgebraicGeometry.RingedSite.IsDerivedComplete` consumes.

## Implementation notes

The two spellings of the sheaf of rings — `X.ringCatSheaf`, which
`AlgebraicGeometry.Scheme.Modules` is built from, and
`(Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)` — are
definitionally equal but not syntactically so, and a goal mixing them is type-correct only at
default transparency. So the datum is ascribed into the site's spelling once, here, and the lemmas
below are stated against that ascription; nothing downstream has to mention `X.ringCatSheaf` again.

`Stacks.SheafOfModules.opensRingedSite` lands in `AlgebraicGeometry.RingedSite.{u, u, u}`, a
single universe, which is the shape at which the derived-category statements about restriction to
a slice site are available.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- **A quasi-coherent sheaf of ideals of a scheme, read as a sheaf of ideals of its ringed
site**: the subsheaf `ℐ 𝒪_X` of the unit sheaf of modules, ascribed as a submodule of the unit
over the structure sheaf of `Stacks.SheafOfModules.opensRingedSite X.sheaf`.

This is the datum that `AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999]
takes, so it is what lets derived completeness of an object of `D(𝒪_X)` along `ℐ` be stated. -/
def idealSheafSiteSubmodule (I : X.IdealSheafData) :
    SheafOfModules.Submodule (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.opensRingedSite X.sheaf).O))) :=
  Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1
    (SheafOfModules.unit X.ringCatSheaf)

/-- **The sections of the sheaf of ideals over an affine open are the ideal there.** -/
theorem idealSheafSiteSubmodule_obj_affine (I : X.IdealSheafData) (U : X.affineOpens) :
    ((idealSheafSiteSubmodule I).toSubmodule.obj (op U.1) :
        Submodule Γ(X, U.1) Γ(X, U.1)) = I.ideal U := by
  refine Eq.trans ?_ (pow_one (I.ideal U))
  exact idealPowerMultiple_unit_toSubmodule_obj_affine I 1 U

/-- Membership in the sheaf of ideals over an affine open is membership in the ideal there. This
is the form the quantifier `∀ U, ∀ f ∈ ℐ(U), …` of
`AlgebraicGeometry.RingedSite.IsDerivedComplete` consumes. -/
theorem mem_idealSheafSiteSubmodule_obj_affine (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) :
    f ∈ (idealSheafSiteSubmodule I).toSubmodule.obj (op U.1) ↔ f ∈ I.ideal U := by
  rw [show ((idealSheafSiteSubmodule I).toSubmodule.obj (op U.1) :
    Submodule Γ(X, U.1) Γ(X, U.1)) = I.ideal U from
      idealSheafSiteSubmodule_obj_affine I U]
  exact Iff.rfl

end Stacks.Algebraization

end
