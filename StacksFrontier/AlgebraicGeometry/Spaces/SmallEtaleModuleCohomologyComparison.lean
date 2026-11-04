module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonAmbient
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses

/-!
# Stacks 03FD on the small étale site of an algebraic space

For an algebraic space `F` over a scheme `S`, the derived global sections of an `𝒪_F`-module on
the small étale site agree, in every degree, with the derived global sections of its underlying
abelian sheaf.

This is [Stacks, Tag 03FD] for the one site this development most needs it on, and it is a
corollary of `ModuleSheafCohomology.globalSectionsComparisonIsoAmbient` and nothing else: the
small étale site of `F` has its objects in `Type (u + 1)` and its morphisms in `Type u`, its
structure rings have sections in `Type u`, and the comparison applies at coefficients
`max (u + 1) w`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleGlobalSectionsComparisonIso`: the comparison, with its
  degree-zero normalization
  `AlgebraicGeometry.Space.toRightDerivedZero_comp_smallEtaleGlobalSectionsComparisonIso`.

## Implementation notes

The site is *not* a `CategoryTheory.SmallCategory` -- its objects lie one universe above its
morphisms -- which is what the earlier seating of 03FD required and why
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse` could not relate its
cohomology to abelian sheaf cohomology.

The sheafification, `Ext` and injectivity data are carried as `have`s inside the statements,
as everywhere else in this development that works at this module universe; they are discharged
inside `globalSectionsComparisonIsoAmbient` and restated here only so that the type elaborates.

Only the global-sections half is available. Sections over an object of the site are still
seated at a small site; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

attribute [local instance] ModuleSheafCohomology.Univ.gamma_additive

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03FD on the small étale site of an algebraic space.** Deriving the global sections
of an `𝒪_F`-module and then forgetting to abelian groups agrees, in every degree, with
forgetting to an abelian sheaf and deriving global sections there. -/
def smallEtaleGlobalSectionsComparisonIso (n : ℕ) :
    have := site_hasSheafify_addCommGrp.{u + 1, u, w}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    have : EnoughInjectives
        (Sheaf (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}) :=
      site_enoughInjectives_addCommGrp.{u + 1, u, w}
        (J := (smallEtaleRingedSite B S hS F hF).J)
    have : HasInjectiveResolutions
        (Sheaf (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}) := inferInstance
    have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    (SheafOfModules.toSheaf.{max (u + 1) w}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        Sheaf.Γ (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}).rightDerived n ≅
      SheafOfModules.toSheaf.{max (u + 1) w}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        (Sheaf.Γ (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}).rightDerived n :=
  ModuleSheafCohomology.globalSectionsComparisonIsoAmbient.{u + 1, u, u, w}
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) n

/-- The degree-zero normalization of `smallEtaleGlobalSectionsComparisonIso`. -/
lemma toRightDerivedZero_comp_smallEtaleGlobalSectionsComparisonIso :
    have := site_hasSheafify_addCommGrp.{u + 1, u, w}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    have : EnoughInjectives
        (Sheaf (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}) :=
      site_enoughInjectives_addCommGrp.{u + 1, u, w}
        (J := (smallEtaleRingedSite B S hS F hF).J)
    have : HasInjectiveResolutions
        (Sheaf (smallEtaleRingedSite B S hS F hF).J Ab.{max (u + 1) w}) := inferInstance
    have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    (SheafOfModules.toSheaf.{max (u + 1) w}
            (ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
          Sheaf.Γ (smallEtaleRingedSite B S hS F hF).J
            Ab.{max (u + 1) w}).toRightDerivedZero ≫
        (smallEtaleGlobalSectionsComparisonIso.{w} B S hS F hF 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{max (u + 1) w}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        (Sheaf.Γ (smallEtaleRingedSite B S hS F hF).J
          Ab.{max (u + 1) w}).toRightDerivedZero :=
  ModuleSheafCohomology.toRightDerivedZero_comp_globalSectionsComparisonIsoAmbient.{u + 1, u, u, w}
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O)

end AlgebraicGeometry.Space

end
