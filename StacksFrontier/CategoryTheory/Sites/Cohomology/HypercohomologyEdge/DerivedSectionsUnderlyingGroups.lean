module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# The two spellings of derived sections over an object agree

Let `(C, O)` be a ringed site whose objects, morphisms and ring sections share one universe, and
let `U` be an object of `C`. There are two unbounded right derived functors of "sections over
`U`":

* `Stacks.Cohomology.HypercohomologyEdge.derivedSections O U`, the right derived functor of
  `SheafOfModules.evaluation O (op U)`, valued in `D(Mod Γ(U, O))`;
* `Stacks.Cohomology.Localization.derivedSectionsOverObject X U`, the right derived functor of
  sections with the module structure forgotten, valued in `D(Ab)`.

They agree: forgetting the module structure commutes with the right derived functor, because
`forget₂ (ModuleCat R) AddCommGrpCat` is exact. This is the instance
`F = SheafOfModules.evaluation`, `G = forget₂` of
`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`, which says
`R(F) ⋙ G.mapDerivedCategory ≅ R(F ⋙ G)` for `F` additive out of a Grothendieck abelian category
and `G` exact.

## Main definitions

* `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsForgetModuleIso`: **the comparison**,
  `RΓ(U, -) ⋙ forget₂ ≅ RΓ_{Ab}(U, -)` as functors `D(O) ⥤ D(Ab)`.
* `Stacks.Cohomology.HypercohomologyEdge.homologyDerivedSectionsForgetModuleIso`: its degreewise
  form, `H^q(RΓ_{Ab}(U, -)) ≅ H^q(RΓ(U, -))` with the module structure forgotten.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.HypercohomologyEdge

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] evaluation_additive

open AlgebraicGeometry

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The forgetful functor from `Γ(U, O)`-modules to abelian groups. -/
abbrev forgetSectionsModule :
    ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) ⥤
      AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
    AddCommGrpCat.{u}

/-- **Derived sections over an object, with the module structure forgotten after deriving, are
derived sections with it forgotten before.**

The left-hand side is `Stacks.Cohomology.HypercohomologyEdge.derivedSections`, the right derived
functor of `SheafOfModules.evaluation`, followed by the functor that the exact
`forget₂ (ModuleCat Γ(U, O)) AddCommGrpCat` induces on unbounded derived categories. The
right-hand side is `Stacks.Cohomology.Localization.derivedSectionsOverObject`, the right derived
functor of sections with the module structure forgotten first. -/
def derivedSectionsForgetModuleIso :
    derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        (forgetSectionsModule X U).mapDerivedCategory ≅
      Localization.derivedSectionsOverObject X U :=
  SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U))
    (forgetSectionsModule X U)

/-- **The degreewise form of `derivedSectionsForgetModuleIso`**: the degree-`q` hypercohomology of
`U` computed in abelian groups is the underlying abelian group of the degree-`q` hypercohomology
computed in `Γ(U, O)`-modules. -/
def homologyDerivedSectionsForgetModuleIso (q : ℤ) :
    Localization.derivedSectionsOverObject X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q ≅
      derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) q ⋙
        forgetSectionsModule X U :=
  (Functor.isoWhiskerRight (derivedSectionsForgetModuleIso X U)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q)).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso (forgetSectionsModule X U) q)

end Stacks.Cohomology.HypercohomologyEdge

end
