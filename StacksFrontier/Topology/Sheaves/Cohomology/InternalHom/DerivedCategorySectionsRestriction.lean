module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections

/-!
# Restricting the degree-zero hypercohomology of the derived internal Hom to an open

Let `(X, O_X)` be a ringed space, `U ⊆ X` an open and `L`, `M` objects of `D(O_X)`. **Stacks
08DK** identifies the degree-zero global hypercohomology of `RSheafHom(L, M)` with
`Hom_{D(O_X)}(L, M)` and its degree-zero hypercohomology over `U` with
`Hom_{D(O_U)}(L|_U, M|_U)`. The two identifications are **compatible under restriction**: the
square

```
H⁰(X, RSheafHom(L, M)) ----> Hom_{D(O_X)}(L, M)
        |                           |
H⁰(U, RSheafHom(L, M)) ----> Hom_{D(O_U)}(L|_U, M|_U)
```

commutes.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSectionsEquiv_restriction`: the commuting square.

## Implementation notes

A topological space with a sheaf of commutative rings *is* a ringed site, so this is the
ringed-site statement
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_restriction` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectRestriction`, read
off along `Stacks.SheafOfModules.ringedSite` exactly as Stacks 08DK itself is in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections`; nothing is
reproved.

The restriction of hypercohomology is the one of the site,
`Stacks.Cohomology.ModuleSections.derivedSectionsRestriction`, and the restriction of morphisms
is `CategoryTheory.Functor.mapDerivedCategory` of `SheafOfModules.overFunctor`, which is the
restriction `L|_U` that Stacks 08DK over an open is stated for.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]
  (U : Opens X)
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]

/-- Restriction to the opens contained in `U` is left exact, at the ringed-site spelling of the
structure sheaf that the ringed-site form of the compatibility is stated at. -/
local instance preservesFiniteLimitsOverRingedSite :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
  Stacks.Cohomology.Localization.preservesFiniteLimits_restriction (ringedSite Rc) U

/-- Restriction to the opens contained in `U` is right exact, at the ringed-site spelling. -/
local instance preservesFiniteColimitsOverRingedSite :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
  Stacks.Cohomology.Localization.preservesFiniteColimits_restriction (ringedSite Rc) U

/-- **Stacks 08DK globally is compatible with Stacks 08DK over an open under restriction of
hypercohomology.** The restriction `RΓ(X, -) ⟶ RΓ(U, -)` carries the identification of the
degree-zero global hypercohomology of `RSheafHom(L, M)` with `Hom_{D(O_X)}(L, M)` to the
identification of its degree-zero hypercohomology over `U` with `Hom_{D(O_U)}(L|_U, M|_U)`. -/
theorem derivedSheafHomSectionsEquiv_restriction
    (L M : DerivedCategory (StructureSheafModules Rc))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv Rc U L M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedSectionsRestriction (ringedSite Rc) U).app
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) ξ) =
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.map
        (derivedSheafHomGlobalSectionsEquiv Rc L M ξ) :=
  RingedSite.derivedSheafHomSectionsEquiv_restriction (ringedSite Rc) U L M ξ

end Stacks.SheafOfModules

end
