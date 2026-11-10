module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CounitGysinEdgeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory

/-!
# Pushing forward and forgetting, at a module placed in a single degree

Let `f : X ⟶ Y` be a morphism of ringed spaces whose direct image of sheaves of modules is exact.
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` is the
comparison, on unbounded derived categories, of pushing modules forward and then forgetting the
module structure with forgetting and then pushing abelian sheaves forward.  This file evaluates
that comparison **at a module placed in a single degree**: there the four single-functor
comparisons of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the four functors of the square
identify both ways round the square with one another.

`derivedModulePushforwardCompToSheafIso_fac` pins the comparison down at the image of a cochain
complex, and `derivedModulePushforwardCompToSheafIso_homology` carries it past the cohomology
functor.  Neither answers the question here, which is what the comparison does to a *single
complex*; that is what a diagram chase needs when a morphism whose source is an object placed in
one degree — the Gysin edge morphism `i_*ℋ ᶜ_Z(K)[-c] ⟶ K` of [Stacks, Tag 0G8A] — has to be
carried across the forgetful functor.

## Main results

* `derivedModulePushforwardCompToSheafIso_single`: **the comparison at a single complex.**
  Moving the forgetful functor past the direct image and then out of the single functor is moving
  it out of the single functor and then past the direct image, up to the comparison.

## Implementation notes

The whole content is the two structural laws of the single-functor comparison proved in
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso`: the comparison
is a three-factor composite of two instances of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and one of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_app` and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app` evaluate each factor.
What is left is formal, and it is done by `Stacks.CounitGysinEdge.paste`, which is stated at a
variable category and
applied with `exact` for the reason recorded in the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory`: the
objects
along the composites are definitionally equal in the two spellings "push forward then forget" and
"forget then push forward", which `rw` and `simp` refuse to identify.

The statement keeps the trailing factor
`Stacks.Cohomology.ModulePushforwardComparison.modulePushforwardCompToSheafIso`, even though that
isomorphism is `CategoryTheory.Iso.refl`, so that the two sides have syntactically equal targets.

**No declaration here carries a `@[stacks ...]` attribute.**  This is a coherence between
canonical isomorphisms of this library's making; it states no result of the source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [PreservesFiniteLimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)]

/-- **The comparison of pushing forward and forgetting, at a module placed in a single degree.**
Forgetting the module structure of `f_*A` placed in degree `c` is, through the comparison
`derivedModulePushforwardCompToSheafIso`, the abelian direct image of the forgetful image of `A`
placed in degree `c`: the four single-functor comparisons of the square intertwine.

This is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_app` at each of the two
instances of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` the comparison is
built from, together with
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app` at the instance of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` between them. -/
theorem derivedModulePushforwardCompToSheafIso_single (c : ℤ)
    (A : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.map
          (((modulePushforward f).mapDerivedCategorySingleFunctor c).hom.app A) ≫
        ((_root_.SheafOfModules.toSheaf
            (structureSheafRing Y)).mapDerivedCategorySingleFunctor c).hom.app
          ((modulePushforward f).obj A) =
      (derivedModulePushforwardCompToSheafIso f).hom.app
          ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) c).obj A) ≫
        ((abelianPushforward f).mapDerivedCategory.map
            (((_root_.SheafOfModules.toSheaf
              (structureSheafRing X)).mapDerivedCategorySingleFunctor c).hom.app A) ≫
          ((abelianPushforward f).mapDerivedCategorySingleFunctor c).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj A)) ≫
        (DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) c).map
          ((modulePushforwardCompToSheafIso f).inv.app A) :=
  Stacks.CounitGysinEdge.paste _ _ _ _ _ _ _ _ _ _ _
    (Functor.mapDerivedCategorySingleFunctor_comp_app (modulePushforward f)
      (_root_.SheafOfModules.toSheaf (structureSheafRing Y)) c A)
    (Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app
      (modulePushforward f ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing Y))
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f)
      (modulePushforwardCompToSheafIso f) c A)
    (Functor.mapDerivedCategorySingleFunctor_comp_app
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)) (abelianPushforward f) c A)
    (Iso.hom_inv_id_app _ _)
    (Eq.trans ((DerivedCategory.singleFunctor
        (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) c).map_comp _ _).symm
      (Eq.trans
        (congrArg (DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) c).map
          (Iso.hom_inv_id_app (modulePushforwardCompToSheafIso f) A))
        ((DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) c).map_id _)))
    rfl

end Stacks.Cohomology.ModulePushforwardComparison

end
