module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.GlobalSectionsCohomologyBridge

/-!
# Module-valued derived global sections against abelian sheaf cohomology on a space

Let `X` be an algebraic space over a scheme `S`. On its small étale site, whose objects lie in
`Type (u + 1)` and whose morphisms and structure rings lie in `Type u`, the vanishing of the
right derived functors of the global sections of `𝒪_X`-modules implies the vanishing of the
cohomology `CategoryTheory.Sheaf.H.{u + 1}` of the underlying abelian sheaf, in every positive
degree. This is
`Stacks.Cohomology.ObjectSections.subsingleton_sheafH_of_subsingleton_rightDerived_globalSections`
with its sheafification, injectivity and `Ext` data supplied on that site.

It is the form in which the vanishing of `H²(X, 𝓘)` asked by Stacks 0DNM is read off from the
derived direct images in the proof of Stacks 0DPJ.

## Main results

* `AlgebraicGeometry.Space.subsingleton_sheafH_of_isZero_rightDerived_globalSections`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Vanishing of the derived global sections of an `𝒪_X`-module forces vanishing of the
cohomology of its underlying abelian sheaf**, in every positive degree, on the small étale site
of an algebraic space. -/
theorem subsingleton_sheafH_of_isZero_rightDerived_globalSections (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (hF : have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
        hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).rightDerived (n + 1)).obj F)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj F) (n + 1)) :=
  have : EnoughInjectives (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
    enoughInjectives_modules B S hS X.1 X.2
  have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
    hasInjectiveResolutions_modules B S hS X.1 X.2
  have : HasExt.{u + 1} (SheafOfModules.{u} (structureRingSheaf B S hS X)) := HasExt.standard _
  Stacks.Cohomology.ObjectSections.subsingleton_sheafH_of_subsingleton_rightDerived_globalSections
    (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS X) F n
    (ModuleCat.isZero_iff_subsingleton.mp hF)

end AlgebraicGeometry.Space

end
