module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# Epimorphisms of sheaves of modules restrict to the site over an object

An epimorphism of sheaves of modules stays an epimorphism after restriction to the site over an
object.

## Main results

* `Stacks.SheafOfModules.EpiMono.epi_over`: the restriction of an epimorphism is an epimorphism.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u u' t

namespace Stacks.SheafOfModules.EpiMono

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- An epimorphism of sheaves of modules stays an epimorphism after restriction to the site over
an object. -/
theorem epi_over [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}] {M N : SheafOfModules.{t} R} (p : M ⟶ N)
    [hp : Epi p] (T : C) : Epi (p.over T) := by
  have hp := isLocallySurjective_of_epi p
  have hloc : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over T)).map (p.over T)) :=
    Presheaf.isLocallySurjective_whisker (J.over T) J (Over.forget T)
      ((PresheafOfModules.toPresheaf R.obj).map p.val)
  exact (SheafOfModules.toSheaf (R.over T)).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

end Stacks.SheafOfModules.EpiMono

end
