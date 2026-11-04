module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite

/-!
# Vanishing of the cohomology of a sheaf of modules over an object

Let `(C, J)` be a small site and `R` a sheaf of rings on it, with the site, the rings and the
modules in one universe.  The cohomology `H^p(U, M)` of a sheaf of `R`-modules over an object `U`,
in the sense of `Stacks.Cohomology.moduleCohomology` (the right derived functors of evaluation
at `U`), vanishes as soon as the abelian sheaf cohomology of the underlying abelian sheaf of `M`
over `U` does, or as soon as the global cohomology of its restriction to the slice `C/U` does.

The chain of comparisons is: forgetting the module structure is exact and faithful; evaluation
followed by forgetting is sections of the underlying abelian sheaf, and Stacks 03FD for sections
over an object (`ModuleSheafCohomology.sectionsComparisonIso`) computes its derived functors on
abelian sheaves; those are the `Ext`-groups out of the free abelian sheaf on `yoneda.obj U`
(`ModuleSheafCohomology.extFunctorObjIsoRightDerived`), which is `CategoryTheory.Sheaf.H'`; and
`Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'` identifies that
with the global cohomology of the slice.

## Main results

* `Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH'`
* `Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH_over`

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- The module cohomology `H^p(U, M)` vanishes when the abelian sheaf cohomology `H^p(U, M)` of
the underlying abelian sheaf, `CategoryTheory.Sheaf.H'`, vanishes. -/
theorem isZero_moduleCohomology_of_subsingleton_sheafH' (U : C) (p : ℕ)
    (M : SheafOfModules.{u} R)
    (h : Subsingleton (Sheaf.H'.{u} ((SheafOfModules.toSheaf.{u} R).obj M) p U)) :
    IsZero (moduleCohomology R U p M) := by
  let E : SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op U)) :=
    SheafOfModules.evaluation R (op U)
  let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
  have hEadd : E.Additive := by
    dsimp [E, SheafOfModules.evaluation]
    infer_instance
  let Sec := (sheafSections J AddCommGrpCat.{u}).obj (op U)
  have hcomp : E ⋙ G ≅ SheafOfModules.toSheaf.{u} R ⋙ Sec := Iso.refl _
  have hSadd : Sec.Additive := ⟨by intros; rfl⟩
  have hSlim : PreservesFiniteLimits Sec :=
    preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{u}).symm
  have h1 : IsZero ((Sec.rightDerived p).obj ((SheafOfModules.toSheaf.{u} R).obj M)) := by
    have h0 : IsZero ((Abelian.extFunctorObj ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) p).obj ((SheafOfModules.toSheaf.{u} R).obj M)) :=
      AddCommGrpCat.isZero_iff_subsingleton.2 h
    exact h0.of_iso ((ModuleSheafCohomology.extFunctorObjIsoRightDerived Sec _
      (ModuleSheafCohomology.evaluationRepresentation J U) p).app _).symm
  have h2 : IsZero (((E ⋙ G).rightDerived p).obj M) :=
    (h1.of_iso ((ModuleSheafCohomology.sectionsComparisonIso J R U p).app M)).of_iso
      ((rightDerivedIsoOfFunctorIso hcomp p).app M)
  have hGz : IsZero (G.obj (moduleCohomology R U p M)) :=
    h2.of_iso (rightDerivedExactPostcompositionIso E G M p)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hGz.eq_of_src _ _

/-- The module cohomology `H^p(U, M)` vanishes when the global cohomology of the restriction of
the underlying abelian sheaf of `M` to the slice `C/U` vanishes. -/
theorem isZero_moduleCohomology_of_subsingleton_sheafH_over (U : C) (p : ℕ)
    (M : SheafOfModules.{u} R)
    (h : Subsingleton (Sheaf.H.{u} (((SheafOfModules.toSheaf.{u} R).obj M).over U) p)) :
    IsZero (moduleCohomology R U p M) := by
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u, u, u} J U
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u, u} J U
  exact isZero_moduleCohomology_of_subsingleton_sheafH' R U p M
    ((Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'.{u}
      J U (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J)
      _ p).1 h)

end Stacks.Cohomology
