module

public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonAmbient
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered colimits and the cohomology of modules on a site

On any site, the cohomology of `O`-modules commutes with a colimit of a given shape exactly when
the cohomology of abelian sheaves does: the comparison `colim_i H^p(C, M_i) ⟶ H^p(C, colim_i M_i)`
of module cohomology is an isomorphism as soon as the corresponding comparison for the underlying
abelian sheaves is.

This is the module-coefficient half of a filtered-colimit statement; the abelian half is a
genuinely cohomological theorem about the site (Stacks 0739, and Stacks 073E on the small étale
site of a quasi-compact and quasi-separated algebraic space), and it is taken here as a
hypothesis. Nothing below proves a filtered-colimit statement from nothing.

## Main results

* `ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology`: **the module comparison is
  an isomorphism as soon as the abelian one is.**
* `ModuleSheafCohomology.preservesColimit_globalModuleCohomology`: the same as preservation of the
  colimit, which is the form a consumer that needs the colimit cocone uses.
* `ModuleSheafCohomology.globalSectionsFunctorRightDerivedForgetIso`: the degreewise comparison
  the two of them are built from -- module cohomology, read in abelian groups, is abelian sheaf
  cohomology of the underlying abelian sheaf.

## Implementation notes

The three steps are

* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` with the exact functor
  `CategoryTheory.forget₂ (ModuleCat _) AddCommGrpCat`, which pulls the forgetful functor out of
  the right derived functor, together with
  `Stacks.Cohomology.SiteModules.globalSectionsForgetAddCommGrpIso` in degree zero: the module
  cohomology of `M`, read in abelian groups, is the right derived functor of
  `SheafOfModules.toSheaf ⋙ Sheaf.Γ`;
* `ModuleSheafCohomology.globalSectionsComparisonIsoAmbient`, which is Stacks 03FD: that right
  derived functor is `SheafOfModules.toSheaf` followed by abelian sheaf cohomology;
* `Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf` for the
  passage from a colimit of modules to the colimit of the underlying abelian sheaves, and
  `CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves` against the forgetful functor
  to abelian groups, which reflects colimits because it reflects isomorphisms.

The module universe is the `max u v r w` of
`Stacks.Cohomology.SiteModules.globalModuleCohomology`, which is where Stacks 03FD is seated and
where the sheafification, `Ext` and injectivity data are theorems of this library rather than
hypotheses; they are carried as `have`s inside the statements, as everywhere else in this
development that works at that universe.  The conclusions are phrased through
`Stacks.Cohomology.SiteModules.globalModuleCohomology` rather than through
`Functor.rightDerived` of `Stacks.Cohomology.SiteModules.globalSectionsFunctor` written out: the
two are the same by definition, but only the former is a closed term, and a consumer that writes
the latter at a *concrete* module universe sets instance search the universe constraint
`max u v r ?w =?= m`, which it cannot solve.

The coefficient universe of the abelian hypothesis is therefore `max u v r w` as well, and that
is a real constraint on the consumers: an abelian filtered-colimit statement at a coefficient
universe strictly below the universe of the objects of the site cannot be fed to this, because
Stacks 03FD is not available there.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

namespace ModuleSheafCohomology

attribute [local instance] Univ.gamma_additive

universe v' w' u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (O : Sheaf J RingCat.{r})

/-- The module cohomology of degree `p`, read in abelian groups, is the degree-`p` abelian sheaf
cohomology of the underlying abelian sheaf.

This is `Stacks.Cohomology.SiteModules.globalSectionsForgetAddCommGrpIso` derived, by
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, and then
`ModuleSheafCohomology.globalSectionsComparisonIsoAmbient`, which is Stacks 03FD. -/
@[ega "0 12.1.1" "partial", sga "4 V 3.5" "special case"]
def globalSectionsFunctorRightDerivedForgetIso (p : ℕ) :
    have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
    have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
      site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
    have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
    have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
    globalModuleCohomology.{u, v, r, w} O p ⋙
        forget₂ (ModuleCat.{max u v r w} (RingCat.sectionsSubring O.obj))
          Ab.{max u v r w} ≅
      SheafOfModules.toSheaf.{max u v r w} O ⋙
        (Sheaf.Γ J Ab.{max u v r w}).rightDerived p :=
  have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
    site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
  have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
  have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (globalSectionsFunctor.{u, v, r, max u v r w} O)
      (forget₂ (ModuleCat.{max u v r w} (RingCat.sectionsSubring O.obj)) Ab.{max u v r w})
      (SheafOfModules.toSheaf.{max u v r w} O ⋙ Sheaf.Γ J Ab.{max u v r w})
      (globalSectionsForgetAddCommGrpIso.{u, v, r, max v r w} O) p ≪≫
    globalSectionsComparisonIsoAmbient.{u, v, r, w} J O p

/-- **The cohomology of `O`-modules preserves a colimit as soon as abelian sheaf cohomology
does.** For a diagram `D` of `O`-modules whose underlying abelian sheaves have the property that
`colim_i H^p(C, D_i) ⟶ H^p(C, colim_i D_i)` is an isomorphism, module cohomology preserves the
colimit of `D`. -/
theorem preservesColimit_globalModuleCohomology (p : ℕ) {I : Type w'}
    [Category.{v'} I] [HasColimitsOfShape I Ab.{max u v r w}]
    (D : I ⥤ SheafOfModules.{max u v r w} O)
    (h : have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
      have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
        site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
      have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
      have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
      IsIso (colimit.post (D ⋙ SheafOfModules.toSheaf.{max u v r w} O)
        ((Sheaf.Γ J Ab.{max u v r w}).rightDerived p))) :
    have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
    PreservesColimit D (globalModuleCohomology.{u, v, r, w} O p) := by
  have hsh := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have hinj : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
    site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
  have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
  have hwl := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  have hT : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{max u v r w} O) :=
    Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf O I
  have hab : PreservesColimit (D ⋙ SheafOfModules.toSheaf.{max u v r w} O)
      ((Sheaf.Γ J Ab.{max u v r w}).rightDerived p) :=
    have := h
    preservesColimit_of_isIso_post _ _
  have hcomp : PreservesColimit D (SheafOfModules.toSheaf.{max u v r w} O ⋙
      (Sheaf.Γ J Ab.{max u v r w}).rightDerived p) := inferInstance
  have hforget : PreservesColimit D
      (globalModuleCohomology.{u, v, r, w} O p ⋙
        forget₂ (ModuleCat.{max u v r w} (RingCat.sectionsSubring O.obj)) Ab.{max u v r w}) :=
    (preservesColimit_iff_of_natIso D
      (globalSectionsFunctorRightDerivedForgetIso.{u, v, r, w} J O p)).2 hcomp
  exact preservesColimit_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{max u v r w} (RingCat.sectionsSubring O.obj)) Ab.{max u v r w})

/-- **The comparison map for the cohomology of `O`-modules is an isomorphism as soon as the one
for abelian sheaves is.** This is
`ModuleSheafCohomology.preservesColimit_globalModuleCohomology` read back as
invertibility of `CategoryTheory.Limits.colimit.post`. -/
theorem isIso_colimit_post_globalModuleCohomology (p : ℕ) {I : Type w'}
    [Category.{v'} I] [HasColimitsOfShape I Ab.{max u v r w}]
    (D : I ⥤ SheafOfModules.{max u v r w} O)
    (h : have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
      have : EnoughInjectives (Sheaf J Ab.{max u v r w}) :=
        site_enoughInjectives_addCommGrp.{u, v, max r w} (J := J)
      have : HasInjectiveResolutions (Sheaf J Ab.{max u v r w}) := inferInstance
      have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
      IsIso (colimit.post (D ⋙ SheafOfModules.toSheaf.{max u v r w} O)
        ((Sheaf.Γ J Ab.{max u v r w}).rightDerived p))) :
    have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
    IsIso (colimit.post D (globalModuleCohomology.{u, v, r, w} O p)) := by
  have hsh := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have hwl := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  have := preservesColimit_globalModuleCohomology.{v', w', u, v, r, w} J O p D h
  infer_instance

end ModuleSheafCohomology

end
