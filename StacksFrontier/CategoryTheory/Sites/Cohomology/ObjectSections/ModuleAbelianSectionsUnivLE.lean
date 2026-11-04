module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# Module and abelian cohomology over an object, with the rings in their own universe

Let `(C, J)` be a site whose objects live in `Type u` and morphisms in `Type v`, let `R` be a
sheaf of rings with rings in `Type r`, and consider sheaves of `R`-modules with sections in the
universe `max u v r t`. This file proves [Stacks, Tag 03FD] over an object `U` in that seating:
the higher cohomology of a sheaf of modules `F` over `U`, computed in `Mod(R)`, is the higher
cohomology over `U` of its underlying abelian sheaf.

The existing comparisons pin the universe of the rings to that of the sections
(`Stacks.Cohomology.InjectiveModuleSheafAcyclicity`) or to that of the morphisms
(`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`). The sites of
algebraic stacks have their structure rings in `Type u`, their morphisms in `Type u` and their
objects and module sections in `Type (u + 1)`, which is neither.

## Main results

* `Stacks.Cohomology.ModuleAbelianSectionsUnivLE.isZero_rightDerived_sections_toSheaf_succ`:
  the underlying abelian sheaf of an injective sheaf of modules has no higher cohomology over
  any object.
* `Stacks.Cohomology.ModuleAbelianSectionsUnivLE.rightDerivedEvaluationIso`: the higher
  module-valued sections, read as abelian groups, are the higher abelian sections of the
  underlying abelian sheaf.
* `Stacks.Cohomology.ModuleAbelianSectionsUnivLE.isZero_rightDerived_evaluation_iff`: the
  vanishing statements agree.

## Implementation notes

The acyclicity is `Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, which is
stated with independent ring and module universes, against the free abelian sheaf on `U`, whose
`Ext`-groups are the right derived functors of sections by
`Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections`. The
comparison is then the collapse `Stacks.RightDerivedComp.objIsoOfAcyclicImage` for the exact
functor to abelian sheaves.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.FreeYonedaUnivLE

namespace Stacks.Cohomology.ModuleAbelianSectionsUnivLE

/-- The higher right derived functors of an exact functor vanish. -/
theorem _root_.CategoryTheory.Functor.isZero_rightDerived_succ_of_exact {A B : Type*}
    [Category* A] [Category* B] [Abelian A] [Abelian B] [HasInjectiveResolutions A]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (M : A) (n : ℕ) : IsZero ((G.rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  have hex : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt (n + 1) :=
    (I.cocomplex_exactAt_succ n).map G
  exact hex.isZero_homology.of_iso (I.isoRightDerivedObj G (n + 1))

universe t r v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t}]
  [HasExt.{max u v r t} (Sheaf J AddCommGrpCat.{max u v r t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v r t})]
  (R : Sheaf J RingCat.{r})

/-- **[Stacks, Tag 03FD], the acyclicity.** The underlying abelian sheaf of an injective sheaf of
`R`-modules has vanishing higher cohomology over every object, the rings of `R` living in a
universe of their own. -/
theorem isZero_rightDerived_sections_toSheaf_succ (I : SheafOfModules.{max u v r t} R)
    [Injective I] (U : C) (q : ℕ) :
    IsZero ((((sheafSections J AddCommGrpCat.{max u v r t}).obj (op U)).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) := by
  refine IsZero.of_iso ?_
    (((nonempty_extFunctorObj_iso_rightDerived_sections.{max r t} J U (q + 1)).some).app
      ((SheafOfModules.toSheaf R).obj I)).symm
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  have h₀ : ∀ e : Ext.{max u v r t} ((freeYoneda.{max u r t} J).obj U)
      ((SheafOfModules.toSheaf R).obj I) (q + 1), e = 0 := fun e =>
    Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u v r t, max u v t, r}
      J R I _
      (ModuleSheafCohomology.isTorsionFree_sheafify J
        (uliftYoneda.{max u r t}.obj U ⋙ AddCommGrpCat.free) (fun point => by
          change Module.IsTorsionFree ℤ
            (FreeAbelianGroup (ULift.{max u r t} (point.unop ⟶ U)))
          exact Module.Flat.isTorsionFree)) q e
  rw [h₀ a, h₀ b]

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

variable [EnoughInjectives (SheafOfModules.{max u v r t} R)]

/-- **[Stacks, Tag 03FD] over an object.** The higher module-valued sections over `U` of a
sheaf of `R`-modules, read as abelian groups, are the higher sections over `U` of its underlying
abelian sheaf. -/
def rightDerivedEvaluationIso (F : SheafOfModules.{max u v r t} R) (U : C) (n : ℕ) :
    (forget₂ (ModuleCat.{max u v r t} (R.obj.obj (op U))) AddCommGrpCat.{max u v r t}).obj
        (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) ≅
      (((sheafSections J AddCommGrpCat.{max u v r t}).obj (op U)).rightDerived n).obj
        ((SheafOfModules.toSheaf R).obj F) :=
  have : PreservesFiniteLimits
      (forget₂ (ModuleCat.{max u v r t} (R.obj.obj (op U))) AddCommGrpCat.{max u v r t}) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits
      (forget₂ (ModuleCat.{max u v r t} (R.obj.obj (op U))) AddCommGrpCat.{max u v r t}) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : (forget₂ (ModuleCat.{max u v r t} (R.obj.obj (op U)))
      AddCommGrpCat.{max u v r t}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Classical.choice (_root_.rightDerived_comp_iso_of_preservesHomology
      (SheafOfModules.evaluation R (op U))
      (forget₂ (ModuleCat.{max u v r t} (R.obj.obj (op U))) AddCommGrpCat.{max u v r t}) n F)) ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (SheafOfModules.toSheaf R)
      ((sheafSections J AddCommGrpCat.{max u v r t}).obj (op U))
      (fun m hm => by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        exact Functor.isZero_rightDerived_succ_of_exact _ F k)
      (fun I hI m hm => by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        exact isZero_rightDerived_sections_toSheaf_succ.{t} J R I U k) n

/-- **The vanishing of module and abelian cohomology over an object agree.** -/
theorem isZero_rightDerived_evaluation_iff (F : SheafOfModules.{max u v r t} R) (U : C) (n : ℕ) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) ↔
      IsZero ((((sheafSections J AddCommGrpCat.{max u v r t}).obj (op U)).rightDerived n).obj
        ((SheafOfModules.toSheaf R).obj F)) := by
  rw [← (rightDerivedEvaluationIso.{t} J R F U n).isZero_iff, ModuleCat.isZero_iff_subsingleton,
    AddCommGrpCat.isZero_iff_subsingleton]
  rfl

end Stacks.Cohomology.ModuleAbelianSectionsUnivLE

end
