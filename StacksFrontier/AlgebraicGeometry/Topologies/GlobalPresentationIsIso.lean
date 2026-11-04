module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation

/-!
# Natural transformations invertible on modules with a global presentation

A natural transformation between two functors out of sheaves of modules that preserve the
relevant colimits, and that is invertible at the structure sheaf, is invertible at every free
module, at every module with a `SheafOfModules.Presentation` and at every module with a global
presentation in the sense of Stacks 03DE (6): such modules are built from the structure sheaf by
coproducts and cokernels.

## Main results

* `Stacks.SheafOfModules.isIso_app_of_hasGlobalPresentation`: a natural transformation between
  two functors preserving finite colimits and coproducts, invertible at the structure sheaf, is
  invertible at every module with a global presentation in the sense of Stacks 03DE (6).

## Implementation notes

A global presentation exhibits the *universe lift* of the module as a cokernel of a map between
coproducts of copies of the universe lift of the structure sheaf. The proof therefore transports
invertibility across `Stacks.SheafOfModules.uliftForPresentationIsoSelf` at both ends, and
applies `Stacks.CategoryTheory.isIso_app_of_isColimit` to the coproducts and to the cokernel.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v₂ u₂

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {B : Type u₂} [Category.{v₂} B] {G H : _root_.SheafOfModules.{u} R ⥤ B}

/-- **A natural transformation agreeing on the structure sheaf agrees on a module with a global
presentation.** A global presentation in the sense of Stacks 03DE (6) exhibits the module, up to
a universe lift, as a cokernel of a map between two coproducts of copies of the structure sheaf;
both functors preserve those colimits, so a transformation invertible at the structure sheaf is
invertible at the module. -/
theorem isIso_app_of_hasGlobalPresentation (α : G ⟶ H)
    [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) H]
    (hunit : IsIso (α.app (_root_.SheafOfModules.unit R)))
    {M : _root_.SheafOfModules.{u} R} (hM : M.HasGlobalPresentation) :
    IsIso (α.app M) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := hM
  have hu : IsIso (α.app (_root_.SheafOfModules.uliftForPresentation.{u, u, u, u, u}
      (_root_.SheafOfModules.unit R))) :=
    (NatTrans.isIso_app_iff_of_iso α (uliftForPresentationIsoSelf.{u, u, u, u} _)).1 hunit
  have coprod {I : Type u} {D : Discrete I ⥤ _root_.SheafOfModules.{u} R} {c : Cocone D}
      (hc : IsColimit c) (h : ∀ k, IsIso (α.app (D.obj k))) : IsIso (α.app c.pt) :=
    Stacks.CategoryTheory.isIso_app_of_isColimit α (isColimitOfPreserves G hc)
      (isColimitOfPreserves H hc) h
  have hM' : IsIso (α.app (_root_.SheafOfModules.uliftForPresentation.{u, u, u, u, u} M)) := by
    refine Stacks.CategoryTheory.isIso_app_of_isColimit α (isColimitOfPreserves G hc)
      (isColimitOfPreserves H hc) ?_
    rintro (_ | _)
    · exact coprod hQ fun _ => hu
    · exact coprod hP fun _ => hu
  exact (NatTrans.isIso_app_iff_of_iso α (uliftForPresentationIsoSelf.{u, u, u, u} M)).2 hM'

end Stacks.SheafOfModules

end
