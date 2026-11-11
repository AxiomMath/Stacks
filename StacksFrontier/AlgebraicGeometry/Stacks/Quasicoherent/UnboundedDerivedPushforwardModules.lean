module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardShiftedSumSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ShiftedSumOfModulesAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasicoherentPullbackExactness

/-!
# The unbounded derived direct image of modules on algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a `1`-morphism of algebraic stacks.  This file defines the unbounded total
right derived functor

`Rf_* : D(𝒪_𝒳) ⟶ D(𝒪_𝒴)`

of the direct image `f_* : Mod(𝒪_𝒳) ⟶ Mod(𝒪_𝒴)` on the big fppf sites, at the universe of the
schemes, and computes it on K-injective complexes: `f_*` has an exact left adjoint `f^*`, so it
carries K-injective complexes to K-injective complexes, and `Rf_*(I) = f_*(I)` for every
K-injective `I`.

This is the functor of **Stacks 07DD**, which says that for a quasi-compact and quasi-separated
`f` it need not carry `D_{QCoh}(𝒪_𝒳)` into `D_{QCoh}(𝒪_𝒴)`.

## Main definitions and results

* `AlgebraicGeometry.Stack.fppfModulesDerivedPushforward`: the functor `Rf_*`.
* `AlgebraicGeometry.Stack.isKInjective_mapHomologicalComplex_fppfModulesPushforward`: `f_*`
  preserves K-injective complexes.
* `AlgebraicGeometry.Stack.fppfModulesDerivedPushforwardObjIsoOfIsKInjective`:
  `Rf_*(I) ≅ f_*(I)` for a K-injective complex `I`.

## Implementation notes

The models of the derived categories are instance arguments `HasDerivedCategory`; nothing here
fixes `HasDerivedCategory.standard`.  The modules on the total category of an algebraic stack
form a Grothendieck abelian category with enough injectives at the universe of the schemes,
because that category is essentially small
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`); the instances are set up as in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ShiftedSumOfModulesAlgebraicStack.lean`.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)]

/-- **The unbounded derived direct image `Rf_* : D(𝒪_𝒳) ⟶ D(𝒪_𝒴)`** of modules along a
`1`-morphism of algebraic stacks, on the big fppf sites at the universe of the schemes: the total
right derived functor of `AlgebraicGeometry.Stack.fppfModulesPushforward`. -/
abbrev fppfModulesDerivedPushforward :
    DerivedCategory (fppfModules B S hS 𝒳) ⥤ DerivedCategory (fppfModules B S hS 𝒴) :=
  Stacks.DerivedFunctor.totalRightDerived (fppfModulesPushforward B S hS f)

omit [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)] in
/-- The inverse image of fppf modules along a `1`-morphism of algebraic stacks is left exact. -/
theorem preservesFiniteLimits_fppfModulesPullback :
    PreservesFiniteLimits (fppfModulesPullback B S hS f) :=
  preservesFiniteLimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS _ _ _ _ _ _ _ _

omit [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)] in
/-- **The direct image of modules preserves K-injective complexes** (**Stacks 08BJ**): its left
adjoint, the inverse image, is exact. -/
theorem isKInjective_mapHomologicalComplex_fppfModulesPushforward
    (I : CochainComplex (fppfModules B S hS 𝒳) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((fppfModulesPushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := preservesFiniteLimits_fppfModulesPullback B S hS f
  Stacks.DerivedFunctor.isKInjective_mapHomologicalComplex_of_adjunction _
    (fppfModulesPullbackPushforwardAdjunction B S hS f) I

/-- **`Rf_*` on a K-injective complex** is the direct image applied degreewise:
`Rf_*(I) ≅ f_*(I)`. -/
def fppfModulesDerivedPushforwardObjIsoOfIsKInjective
    (I : CochainComplex (fppfModules B S hS 𝒳) ℤ) [I.IsKInjective] :
    (fppfModulesDerivedPushforward B S hS f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((fppfModulesPushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  Stacks.DerivedFunctor.totalRightDerivedObjQIsoOfIsKInjective _ I

end AlgebraicGeometry.Stack

end
