module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint

/-!
# Zeroth cohomology on the homotopy category of differential graded modules

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras. Zeroth cohomology of a right differential graded `A`-module
is the degree-zero cohomology of its underlying cochain complex of sheaves of modules, and it
is unchanged by homotopy. Consequently it descends from the category of right differential
graded modules to their homotopy category.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.zerothCohomologyFunctor` is zeroth cohomology of a
  right differential graded module.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor` is the
  functor it induces on the homotopy category.

## Main results

* `SheafOfModules.DifferentialGradedModule.zerothCohomology_map_eq_of_homotopic`: homotopic
  morphisms of right differential graded modules induce the same morphism on zeroth
  cohomology.

## References

* [Stacks Project, Tag 0FT2](https://stacks.math.columbia.edu/tag/0FT2)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Zeroth cohomology of a right differential graded module. -/
noncomputable def zerothCohomologyFunctor (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, m} A ⥤ SheafOfModules.{m} R :=
  toCochainComplex A ⋙
    HomologicalComplex.homologyFunctor (SheafOfModules.{m} R) (ComplexShape.up ℤ) 0

/-- Homotopic morphisms of right differential graded modules act identically on zeroth
cohomology. -/
@[stacks 0FT2 "h0_factors"]
theorem zerothCohomology_map_eq_of_homotopic (A : DifferentialGradedAlgebra.{t, a} R)
    (M N : DifferentialGradedModule.{t, a, m} A) (f g : M ⟶ N) (h : Homotopic f g) :
    (zerothCohomologyFunctor A).map f = (zerothCohomologyFunctor A).map g := by
  rcases h with ⟨h⟩
  let homfun : ∀ i j : ℤ, M.complex.X i ⟶ N.complex.X j := fun i j =>
    if hij : j + 1 = i then
      h.app i ≫ eqToHom (congrArg N.complex.X (by lia : i - 1 = j)) else 0
  let hh : _root_.Homotopy f.toHomologicalComplex g.toHomologicalComplex := by
    refine ⟨homfun, ?_, ?_⟩
    · intro i j hij
      change ¬ (j + 1 = i) at hij
      simp [homfun, hij]
    · intro i
      rw [dNext_eq homfun (ComplexShape.up_mk i (i + 1) (by lia)),
        prevD_eq homfun (ComplexShape.up_mk (i - 1) i (by lia))]
      simp only [↓reduceDIte, sub_add_cancel, eqToHom_refl, Category.comp_id, homfun]
      rw [← sub_eq_iff_eq_add, h.comm i]
      simp only [Category.assoc, add_comm]
  exact hh.homologyMap_eq 0

namespace HomotopyCategory

/-- Zeroth cohomology on the homotopy category of right differential graded modules. -/
@[stacks 0FT2 "h0_factors"]
noncomputable def zerothCohomologyFunctor (A : DifferentialGradedAlgebra.{t, a} R) :
    HomotopyCategory.{t, a, m} A ⥤ SheafOfModules.{m} R :=
  CategoryTheory.Quotient.lift _
    (DifferentialGradedModule.zerothCohomologyFunctor.{t, a, m} A)
    (zerothCohomology_map_eq_of_homotopic A)

end HomotopyCategory

end DifferentialGradedModule

end SheafOfModules
