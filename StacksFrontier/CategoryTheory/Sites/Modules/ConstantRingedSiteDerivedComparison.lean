module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteModelComparison
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The two readings of `D(C/U, Λ)` agree over the constant ringed site

`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteModelComparison` puts the two
readings of Stacks 09BD's ambient *abelian* category in bijection, by
`Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`, and identifies 09BD's
constant-complex functor with the constant sheaf functor across it, by
`Stacks.ConstantRingModules.constantFunctorOverIso`. Stacks 09BD and Stacks 09BE are statements
about morphisms of a *derived* category, so neither of those applies to them directly.

This file carries both to the derived categories.

## Main definitions

* `Stacks.ConstantRingModules.constantRingedSiteModuleDerivedEquivalence`: the induced
  equivalence `D(SheafOfModules (Λ̲|_U)) ≌ D(Sheaf (J.over U) (ModuleCat Λ))`, i.e. 09BD's
  ambient derived category is 09BE's.
* `Stacks.ConstantRingModules.constantFunctorOverDerivedIso`: across the induced functor, the
  class of 09BD's complex of constant sheaves of modules on a complex `P` of `Λ`-modules is the
  class of the complex of constant sheaves on `P`, naturally in `P`.

## What this is for, and what it does not do

These are the two things the transport of Stacks 09BD across the equivalence needs on its input
side. 09BD takes a morphism `α : Q(K̲^•) ⟶ Q(F)` of `D(Λ̲|_U)`; 09BE's hypothesis is a morphism
of `D(Sheaf (J.over U) (ModuleCat Λ))` out of the class of the complex of constant sheaves. The
derived equivalence carries one ambient category to the other, and
`constantFunctorOverDerivedIso` identifies the two sources, so a morphism of the second kind
yields one of the first and 09BD applies to it.

**It does not yet finish the transport.** 09BD's *conclusion* is an equation in `D(Λ̲|_V)` for
each arrow `V ⟶ U` of a covering sieve, written through
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the restriction functor. Carrying that
equation back needs, on top of the two definitions here, the compatibility of the derived
slicing square
`Stacks.ConstantRingModules.toModuleSheafOverMapDerivedIso`
(`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesDerivedCompatibility`) with the
`mapDerivedCategoryFactors` of the two restriction functors it compares -- the junction square,
of the kind
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction` supplies
for the derived tensor product. That square is not proved here; it is
`Stacks.ConstantRingModules.toModuleSheafOverMapDerivedIso_hom_app_Q`, beside the square itself.
What that still leaves for 09BE is recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom`; in particular the
equivalence used here is not the slice of a single global reading, so the two readings of
`D(Λ̲|_V)` have themselves to be identified before the junction square applies. No claim about
09BE is made.

## Implementation notes

The derived equivalence is `Dualizing.mapDerivedCategoryEquivalenceOfEquivalence`, the repo's
existing construction, instantiated at `constantRingedSiteModuleEquivalence`. Its four exactness
hypotheses are discharged rather than assumed: an equivalence preserves binary coproducts, hence
binary biproducts, hence is additive, and it preserves all limits and colimits that exist. The
two `Additive` instances are seated as `local instance`s below because
`CategoryTheory.Equivalence.trans`, `Equivalence.symm` and
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso` are `def`s that typeclass resolution
does not unfold, so the component-wise instances are not found at the composite.

`constantFunctorOverDerivedIso` is `constantFunctorOverIso` and
`CategoryTheory.Functor.mapDerivedCategoryFactors` chained: the latter moves
`E.mapDerivedCategory` past the localisation functor, and the former -- read on complexes through
`CategoryTheory.Functor.mapHomologicalComplexCompIso` -- identifies the two complexes.

No `@[stacks]` attribute is attached. Nothing here is an assertion of 09BD or of 09BE.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d u

namespace Stacks.ConstantRingModules

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules.Constant Stacks.Sheaves.RingedPoint

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J RingCat.{u}]
  (U : C) [HasWeakSheafify (J.over U) RingCat.{u}]
  [(J.over U).WEqualsLocallyBijective RingCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d}
    (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U))]
  [HasDerivedCategory.{d} (Sheaf (J.over U) (ModuleCat.{u} Λ))]

/-- The functor of `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence` is additive:
it is an equivalence, so it preserves binary coproducts and hence binary biproducts. Seated by
hand because the equivalence is a composite of two `def`s that instance search does not
unfold. -/
local instance additive_constantRingedSiteModuleEquivalence_functor :
    (constantRingedSiteModuleEquivalence J Λ U).functor.Additive :=
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (constantRingedSiteModuleEquivalence J Λ U).functor
  Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence` is additive,
its functor being so. -/
local instance additive_constantRingedSiteModuleEquivalence_inverse :
    (constantRingedSiteModuleEquivalence J Λ U).inverse.Additive :=
  (constantRingedSiteModuleEquivalence J Λ U).inverse_additive

/-- **The two readings of `D(C/U, Λ)` agree over the constant ringed site.** The derived category
of sheaves of modules over the restriction to `U` of the structure sheaf of the constant ringed
site -- the ambient category of Stacks 09BD -- is the derived category of sheaves of
`Λ`-modules on the slice site `C/U`, which is the ambient category of Stacks 09BE. -/
def constantRingedSiteModuleDerivedEquivalence :
    DerivedCategory (_root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U)) ≌
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{u} Λ)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (constantRingedSiteModuleEquivalence J Λ U)

/-- **Stacks 09BD's complex of constant sheaves of modules has the same class in the derived
category as the complex of constant sheaves.** Across the functor induced by
`Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`, the class of
`AlgebraicGeometry.RingedSite.constantFunctorOver` applied termwise to a complex `P` of
`Λ`-modules is the class of `constantSheaf (J.over U) (ModuleCat Λ)` applied termwise to `P`,
naturally in `P`.

This is the derived form of `Stacks.ConstantRingModules.constantFunctorOverIso`, and it is what
turns a morphism out of the class of the complex of constant sheaves -- the hypothesis of
Stacks 09BE -- into a morphism out of the class of 09BD's complex, which is what 09BD takes. -/
def constantFunctorOverDerivedIso :
    (constantFunctorOver_general J Λ U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙
          (constantRingedSiteModuleEquivalence J Λ U).functor.mapDerivedCategory ≅
      (constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft
      ((constantFunctorOver_general J Λ U).mapHomologicalComplex (ComplexShape.up ℤ))
      (constantRingedSiteModuleEquivalence J Λ U).functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (constantFunctorOverIso J Λ U) (ComplexShape.up ℤ))
      DerivedCategory.Q

end Stacks.ConstantRingModules

end
