module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.CorepresentableUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.SheafQuasiIsoFromPresheaf

/-!
# The derived direct image of abelian étale sheaves is computed by a K-injective module complex

The abelian complex underlying a K-injective complex of sheaves of `Λ`-modules computes the
derived direct image of abelian sheaves on the small étale site: the comparison from degreewise
to derived direct image is invertible there.

## Main results

* `Stacks.EtaleCohomology.quasiIso_etaleAbelianDirectImage_map_of_isKInjective`: degreewise direct
  image takes a K-injective resolution of the abelian complex underlying a K-injective complex of
  `Λ`-modules to a quasi-isomorphism.
* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageUnit_isIso_at_underlying_kInjective`: the
  comparison from degreewise to derived direct image is invertible at the abelian complex
  underlying a K-injective complex of `Λ`-modules.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Degreewise direct image takes a K-injective resolution of the abelian complex underlying a
K-injective complex of `Λ`-modules to a quasi-isomorphism. -/
theorem quasiIso_etaleAbelianDirectImage_map_of_isKInjective
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective]
    {Jc : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ} [Jc.IsKInjective]
    (q : ((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).obj I ⟶ Jc)
    [QuasiIso q] :
    QuasiIso (((etaleAbelianDirectImage.{u, r} f).mapHomologicalComplex (.up ℤ)).map q) := by
  apply Stacks.Cohomology.sheafQuasiIso_of_presheafQuasiIso Y.smallEtaleTopology
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro t
  change QuasiIso ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
    (op ((smallEtaleBaseChange f).obj t.unop))).mapHomologicalComplex (.up ℤ)).map q)
  refine Stacks.Cohomology.DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
    _ _ (Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation.{r, u, u + 1}
      X.smallEtaleTopology
      ((smallEtaleBaseChange f).obj t.unop)).symm q (fun n ↦ ?_)
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).map (q⟦n⟧'))) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (EtaleAbelianSheaves.{u, r} X) (.up ℤ))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    change QuasiIso ((CategoryTheory.shiftFunctor
      (CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ) n).map q)
    infer_instance
  exact Stacks.Cohomology.DerivedLowerShriek.bijective_postcomp_of_qh_bijective _
    (qh_map_bijective_single_of_isKInjective.{u, r} Λ X _
      (Stacks.Cohomology.isTorsionFree_freeYoneda.{max (u + 1) r, u, u + 1}
        X.smallEtaleTopology _) I n)
    (CochainComplex.IsKInjective.Qh_map_bijective _ (Jc⟦n⟧))

/-- The abelian complex underlying a K-injective complex of `Λ`-modules computes the derived direct
image of abelian étale sheaves: the canonical comparison from degreewise to derived direct image is
invertible there. -/
theorem etaleAbelianDerivedDirectImageUnit_isIso_at_underlying_kInjective
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).obj
        (((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).obj I))) :=
  Stacks.Cohomology.ForgetModule.rightDerivedUnit_isIso_of_quasiIso_degreewise
    (etaleAbelianDirectImage.{u, r} f) (etaleAbelianDerivedDirectImage.{u, r} f)
    (etaleAbelianDerivedDirectImageUnit.{u, r} f) _
    (quasiIso_etaleAbelianDirectImage_map_of_isKInjective.{u, r} Λ f I _)

end Stacks.EtaleCohomology

end
