module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses

/-!
# Stacks 03FD for global sections at the ambient module universe

`ModuleSheafCohomology.Univ.globalSectionsComparisonIso` compares the derived global sections of a
sheaf of modules with the derived global sections of its underlying abelian sheaf, in every
degree, over a site whose objects and morphisms live in unrelated universes. It takes the
sheafification, `Ext` and injectivity data of the two sheaf categories as hypotheses, because at
a coefficient universe chosen freely above the site there is no reason for them to exist.

At the coefficient universe `max u v r w` -- the one at which
`Stacks.Cohomology.SiteModules.globalModuleCohomology` of Stacks 071H is defined -- they all do,
and the lemmas that produce them are already in this library. This file discharges them, so that
the comparison is available over *any* site with no hypotheses at all beyond the site and the
sheaf of rings.

This is what makes the comparison usable on the small étale site of a scheme or of an algebraic
space, whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`, so that it is not
a `CategoryTheory.SmallCategory` and the earlier seating of 03FD did not reach it.

## Main definitions

* `ModuleSheafCohomology.globalSectionsComparisonIsoAmbient`: the comparison at the ambient
  module universe, with its degree-zero normalization
  `ModuleSheafCohomology.toRightDerivedZero_comp_globalSectionsComparisonIsoAmbient`.

## Implementation notes

The five inputs come from `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`,
`Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp`,
`Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp`,
`Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp` and
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`; the last two of the seven instance
arguments are then `HasInjectiveResolutions` from `EnoughInjectives` and `HasExt` from
`IsGrothendieckAbelian`, both of which Mathlib supplies. All five are stated at `max u v w` for
a coefficient universe `w`, so they are applied at `w := max r w` and the coefficient universe
of the comparison is `max u v r w`; the module universe `m` of
`ModuleSheafCohomology.Univ.globalSectionsComparisonIso` is therefore `max v w`.

Only the global-sections half is here. The sections-over-an-object half,
`ModuleSheafCohomology.sectionsComparisonIso`, is still seated at a small site, for the reason
recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef`: its
corepresenting object is built from the hom-types of the site.

## References

* [Stacks: Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks: Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

namespace ModuleSheafCohomology

attribute [local instance] Univ.gamma_additive

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (O : Sheaf J RingCat.{r})

/-- **Stacks 03FD for global sections, over an arbitrary site, with no hypotheses.** Deriving
the global sections of a sheaf of `O`-modules and then forgetting agrees, in every degree, with
forgetting to an abelian sheaf and deriving global sections there.

This is `globalSectionsComparisonIso` at the module universe `max u v r w` of
`Stacks.Cohomology.SiteModules.globalModuleCohomology`, where every one of its sheafification,
`Ext` and injectivity hypotheses is a theorem of this library. -/
def globalSectionsComparisonIsoAmbient (n : ℕ) :
    have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
    have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
      site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
    have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
    have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
    (SheafOfModules.toSheaf.{max u v r w} O ⋙ Sheaf.Γ J Ab.{max u v r w}).rightDerived n ≅
      SheafOfModules.toSheaf.{max u v r w} O ⋙ (Sheaf.Γ J Ab.{max u v r w}).rightDerived n :=
  have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
    site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
  have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
  have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := site_hasExt_addCommGrp.{u, v, max r w} (J := J)
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  Univ.globalSectionsComparisonIso.{max v w, r, u, v} J O n

/-- The degree-zero normalization of `globalSectionsComparisonIsoAmbient`. -/
lemma toRightDerivedZero_comp_globalSectionsComparisonIsoAmbient :
    have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
    have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
      site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
    have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
    have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
    (SheafOfModules.toSheaf.{max u v r w} O ⋙
        Sheaf.Γ J Ab.{max u v r w}).toRightDerivedZero ≫
        (globalSectionsComparisonIsoAmbient.{u, v, r, w} J O 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{max u v r w} O)
        (Sheaf.Γ J Ab.{max u v r w}).toRightDerivedZero :=
  have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
    site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
  have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
  have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := site_hasExt_addCommGrp.{u, v, max r w} (J := J)
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  Univ.toRightDerivedZero_comp_globalSectionsComparisonIso.{max v w, r, u, v} J O

end ModuleSheafCohomology

end
