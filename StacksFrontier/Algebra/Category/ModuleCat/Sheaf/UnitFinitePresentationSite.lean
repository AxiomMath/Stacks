module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# The structure sheaf is of finite presentation, on a site with independent universes

For a site `(C, J)` with `C : Type u`, `[Category.{v} C]` and a sheaf of rings `R` with values in
`Type t`, a free sheaf of modules on a finite index type has a tautological presentation with no
relations, so the sheaf of rings `R`, regarded as a module over itself, is of finite presentation.
The three universes are independent, so that this applies to large sites such as the small étale
site of an algebraic space.

## Main definitions and results

* `Stacks.SheafOfModules.Site.freePresentation`: the tautological presentation of `free I`.
* `Stacks.SheafOfModules.Site.unitPresentation`: the resulting presentation of `unit R`.
* `Stacks.SheafOfModules.Site.unit_isFinitePresentation`: `unit R` is of finite presentation.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

universe t v u

namespace Stacks.SheafOfModules.Site


section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **The tautological presentation of a free sheaf of modules.** The standard basis generates
it and there are no relations: the map `free I ⟶ free I` it induces is the identity, whose
kernel is a zero object. -/
noncomputable def freePresentation (I : Type t) :
    (free (R := R) I).Presentation where
  generators := free.generatingSections I
  relations := Site.zeroGeneratingSections (isZero_kernel_of_mono _)

/-- On a finite index type, the tautological presentation of `free I` is finite. -/
instance freePresentation_isFinite (I : Type t) [Finite I] :
    (freePresentation (R := R) I).IsFinite where
  isFiniteType_generators := ⟨by exact inferInstanceAs (Finite I)⟩
  isFiniteType_relations := by
    exact inferInstanceAs
      (Site.zeroGeneratingSections (M := kernel (free.generatingSections (R := R) I).π)
        (isZero_kernel_of_mono _)).IsFiniteType

/-- The free sheaf of modules on a one-element index type is the sheaf of rings itself. -/
noncomputable def freePUnitIso : free (R := R) PUnit.{t + 1} ≅ unit R :=
  coproductUniqueIso (fun _ : PUnit.{t + 1} ↦ unit R)

/-- **The tautological presentation of the sheaf of rings as a module over itself**, obtained
from `Stacks.SheafOfModules.Site.freePresentation` on a one-element index type. -/
noncomputable def unitPresentation : (unit R).Presentation :=
  (freePresentation PUnit.{t + 1}).ofIsIso freePUnitIso.hom

/-- The tautological presentation of `unit R` is finite. -/
instance unitPresentation_isFinite : (unitPresentation (R := R)).IsFinite := by
  exact inferInstanceAs
    ((freePresentation PUnit.{t + 1}).ofIsIso (freePUnitIso (R := R)).hom).IsFinite

section Global

variable [Limits.HasBinaryProducts C] [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{t}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The restriction of `unit R` to the slice site over an object `Y` inherits the tautological
presentation of `Stacks.SheafOfModules.Site.unitPresentation`, because that restriction *is* the
sheaf of rings `R.over Y` regarded as a module over itself
(`Stacks.SheafOfModules.FiniteTypeKernel.unitOverIso`). -/
noncomputable def unitOverPresentation {R : Sheaf J RingCat.{t}} (Y : C) :
    ((unit R).over Y).Presentation :=
  (unitPresentation (R := R.over Y)).ofIsIso (FiniteTypeKernel.unitOverIso Y).hom

/-- The presentation of the restriction of `unit R` to the slice site over `Y` is finite. -/
instance unitOverPresentation_isFinite {R : Sheaf J RingCat.{t}} (Y : C) :
    (unitOverPresentation (R := R) Y).IsFinite := by
  exact inferInstanceAs
    ((unitPresentation (R := R.over Y)).ofIsIso
      (FiniteTypeKernel.unitOverIso (R := R) Y).hom).IsFinite

/-- The quasi-coherent datum presenting `unit R` on the trivial covering of the site by all of
its objects. -/
noncomputable def unitQuasicoherentData : (unit R).QuasicoherentData where
  I := C
  X := id
  coversTop _ := GrothendieckTopology.covering_of_eq_top J <| by
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  presentation Y := unitOverPresentation Y

/-- Every presentation in `Stacks.SheafOfModules.Site.unitQuasicoherentData` is finite. -/
instance unitQuasicoherentData_isFinitePresentation {R : Sheaf J RingCat.{t}} :
    (unitQuasicoherentData (R := R)).IsFinitePresentation where
  isFinite_presentation Y := by exact unitOverPresentation_isFinite _

/-- **The sheaf of rings, regarded as a module over itself, is of finite presentation**, hence
also quasi-coherent and of finite type. -/
instance unit_isFinitePresentation : (unit R).IsFinitePresentation :=
  ⟨unitQuasicoherentData, unitQuasicoherentData_isFinitePresentation⟩

end Global

end Site

end Stacks.SheafOfModules.Site

end
