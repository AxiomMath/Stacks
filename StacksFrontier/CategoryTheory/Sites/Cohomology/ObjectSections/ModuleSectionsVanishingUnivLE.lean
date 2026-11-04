module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Higher sections of a sheaf of modules over an object, at independent universes

Let `C` be a site whose objects lie in `Type u` and whose morphisms lie in `Type v`, let `𝒪` be
a sheaf of rings with sections in `Type r`, and let `M` be a sheaf of `𝒪`-modules with sections in
the universe `max u v r m`. Cohomology over an object `U` can be computed in the category of
sheaves of modules, by deriving the sections functor `M ↦ M(U)`, or in the category of abelian
sheaves, by deriving sections of the underlying abelian sheaf. This file proves that the first
is the second applied to the underlying abelian sheaf, in every degree, which is the content of
Stacks 03FD over an object for sites whose objects lie above their morphisms, as the big sites
of schemes do.

## Main results

* `Stacks.Cohomology.ObjectSections.isZero_rightDerived_toSheaf_obj_of_injective`: the underlying
  abelian sheaf of an injective sheaf of modules is acyclic for sections over every object.
* `Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoUnivLE`: the comparison
  `R^n(Γ(U, -) ∘ forget) ≅ R^nΓ(U, -) ∘ forget`.

## Implementation notes

The forgetful functor from sheaves of modules to abelian sheaves is exact, and sends injectives
to objects acyclic for sections over `U`: sections over `U` are corepresented by the free abelian
sheaf on the representable at `U`, which is sectionwise torsion free, and the underlying abelian
sheaf of an injective sheaf of modules is `Ext`-acyclic against sectionwise torsion-free sheaves
(`ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree`). The comparison is then
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`. The free abelian sheaf is built
on `uliftYoneda`, so that the coefficient universe is not pinned to the morphisms of the site.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open Stacks.Cohomology.FreeYonedaUnivLE

universe m r v u

namespace Stacks.Cohomology.ObjectSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m}]
  [HasExt.{max u v r m} (Sheaf J AddCommGrpCat.{max u v r m})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v r m})]
  [EnoughInjectives (SheafOfModules.{max u v r m} R)]

omit [EnoughInjectives (SheafOfModules R)] in
/-- **The underlying abelian sheaf of an injective sheaf of modules is acyclic for sections over
every object.** Its higher `Ext`-groups out of the sectionwise torsion-free free abelian sheaf on
the representable vanish, and these `Ext`-groups are the higher sections. -/
theorem isZero_rightDerived_toSheaf_obj_of_injective (U : C)
    (I : SheafOfModules.{max u v r m} R) [Injective I] (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections J AddCommGrpCat.{max u v r m}).obj (op U)).rightDerived n).obj
      ((SheafOfModules.toSheaf R).obj I)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have e := (nonempty_extFunctorObj_iso_rightDerived_sections.{max u r m} J U (k + 1)).some
  refine IsZero.of_iso ?_ (e.app ((SheafOfModules.toSheaf R).obj I)).symm
  have htf : ∀ X : Cᵒᵖ,
      Module.IsTorsionFree ℤ (((freeYoneda.{max u r m} J).obj U).obj.obj X) :=
    ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun Y ↦ by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{max u r m} (Y.unop ⟶ U)))
      exact Module.Flat.isTorsionFree)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have h := ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree.{max v m} J R I _ htf k
  exact ⟨fun a b ↦ (h a).trans (h b).symm⟩

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- **Stacks 03FD over an object, at independent universes.** The higher sections over `U` of a
sheaf of modules, computed in the category of sheaves of modules, are the higher sections of its
underlying abelian sheaf. -/
def rightDerivedSectionsIsoUnivLE (U : C) (n : ℕ) :
    (SheafOfModules.toSheaf R ⋙
      (sheafSections J AddCommGrpCat.{max u v r m}).obj (op U)).rightDerived n ≅
      SheafOfModules.toSheaf R ⋙
        ((sheafSections J AddCommGrpCat.{max u v r m}).obj (op U)).rightDerived n :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u v r m} R)
  letI := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{max u v r m})
  letI := HasDerivedCategory.standard AddCommGrpCat.{max u v r m}
  Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _ (fun I hI ↦ by
    have := hI
    exact (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).mpr
      (fun k hk ↦ isZero_rightDerived_toSheaf_obj_of_injective.{m} J R U I k hk)) n

end Stacks.Cohomology.ObjectSections
