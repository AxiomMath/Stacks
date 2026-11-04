module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImageUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The underlying abelian complex of a K-injective complex of modules computes `Rf_*`

Let `f : X ⟶ Y` be a morphism of schemes and `O` a sheaf of rings on the small étale site of
`X`. The underlying abelian complex `I_ab` of a K-injective complex `I` of sheaves of
`O`-modules is in general not a K-injective complex of abelian sheaves, but it still computes
the unbounded derived direct image of abelian sheaves: the unit
`f_* I_ab ⟶ Rf_* I_ab` of `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImage` is an
isomorphism there.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective`:
  the unit of `Rf_*` is invertible at the underlying abelian complex of a K-injective complex of
  `O`-modules.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (O : Sheaf X.smallEtaleTopology RingCat.{max (u + 1) v})

/-- For a sheaf of rings `O` on `X_étale` and a K-injective complex `I` of sheaves of
`O`-modules, the derived-functor unit `f_* I_ab ⟶ Rf_* I_ab` at the underlying complex of abelian
sheaves `I_ab` is an isomorphism. -/
public theorem isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective
    (I : CochainComplex (SheafOfModules.{max (u + 1) v} O) ℤ) [I.IsKInjective] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, v}
    (J := X.smallEtaleTopology)
  exact Stacks.Cohomology.ForgetModule.rightDerivedUnit_isIso_of_quasiIso_degreewise
    (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
    (etaleAbelianDerivedDirectImageUnit.{u, v} f) _
    (Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective_univ.{v}
      X.smallEtaleTopology Y.smallEtaleTopology (smallEtaleBaseChange f) O I _)

end Stacks.EtaleCohomology

end
