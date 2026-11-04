module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOverAnObjectNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of the derived internal Hom on a ringed space

Let `(X, O_X)` be a ringed space and let `L`, `M` be objects of the derived category `D(O_X)`.
For every open `U ⊆ X` the degree-zero hypercohomology over `U` of the derived internal Hom
`RSheafHom(L, M)` is the group of morphisms between the restrictions to `U`:

`H⁰(U, RSheafHom(L, M)) = Hom_{D(O_U)}(L|_U, M|_U)`,

and in particular, taking `U = X`,

`H⁰(X, RSheafHom(L, M)) = Hom_{D(O_X)}(L, M)`.

Both identifications are additive. They say that the derived internal Hom is an internal Hom
for the derived category: its degree-zero cohomology recovers the morphism groups, locally over
every open as well as globally.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSectionsEquiv`: the identification over an open `U`, and
  `Stacks.SheafOfModules.derivedSheafHomSectionsEquiv_naturality`: it is natural in both
  variables.
* `Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv`: the identification globally.

## Implementation notes

A topological space together with a sheaf of commutative rings on it is a ringed site, namely
the site of its opens with the open-cover topology, and under that reading the derived internal
Hom of the space, its derived global sections and its derived sections over an open are those of
the site. So both statements are the ones for a ringed site, read off along
`Stacks.SheafOfModules.ringedSite` as the K-injectivity of the internal Hom complex out of a
K-flat complex is.

The restriction `L|_U` of an object of `D(O_X)` is the functor induced on derived categories by
restriction of sheaves of modules to the slice site over `U`,
`CategoryTheory.Functor.mapDerivedCategory` of `SheafOfModules.overFunctor`; its exactness is
taken as a hypothesis, as it is for a ringed site, rather than deduced from the sheafification
hypotheses on every slice.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A8T](https://stacks.math.columbia.edu/tag/0A8T)
* [Stacks Project, Tag 0A8R](https://stacks.math.columbia.edu/tag/0A8R)
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
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 08DK globally.** For objects `L`, `M` of `D(O_X)` the degree-zero global
hypercohomology of the derived internal Hom `RSheafHom(L, M)` is the group of morphisms
`L ⟶ M` in the derived category of `O_X`-modules. -/
@[stacks 08DK "global sections"]
def derivedSheafHomGlobalSectionsEquiv (L M : DerivedCategory (StructureSheafModules Rc)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) :
        Type u) ≃+ (L ⟶ M) :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) L M

variable (U : Opens X)
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]

/-- **Stacks 08DK over an open.** For objects `L`, `M` of `D(O_X)` and an open `U ⊆ X` the
degree-zero hypercohomology over `U` of the derived internal Hom `RSheafHom(L, M)` is the group
of morphisms `L|_U ⟶ M|_U` in the derived category of `O_U`-modules. -/
@[stacks 08DK "sections over an open"]
def derivedSheafHomSectionsEquiv (L M : DerivedCategory (StructureSheafModules Rc)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject (ringedSite Rc) U).obj
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) :
        Type u) ≃+
      ((SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.obj L ⟶
        (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.obj M) := by
  letI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  letI : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  exact RingedSite.derivedSheafHomSectionsEquiv (ringedSite Rc) U L M

/-- **Stacks 08DK over an open is natural in both variables.**  For `φ : L' ⟶ L` and
`ψ : M ⟶ M'` the morphism induced on `RSheafHom` carries the identification of
`Stacks.SheafOfModules.derivedSheafHomSectionsEquiv` to precomposition with `φ|_U` and
postcomposition with `ψ|_U`.  No attribute: the clause of Tag 08DK is the identification itself,
and `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality`, of which this is the
reading on a space, carries none either. -/
theorem derivedSheafHomSectionsEquiv_naturality
    {L L' M M' : DerivedCategory (StructureSheafModules Rc)} (φ : L' ⟶ L) (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject (ringedSite Rc) U).obj
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) :
        Type u)) :
    derivedSheafHomSectionsEquiv Rc U L' M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject (ringedSite Rc) U).map
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map φ.op).app M ≫
              ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L')).map ψ)) ξ) =
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.map φ ≫
        derivedSheafHomSectionsEquiv Rc U L M ξ ≫
          (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.map ψ := by
  let : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  let : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  exact RingedSite.derivedSheafHomSectionsEquiv_naturality (ringedSite Rc) U φ ψ ξ

end Stacks.SheafOfModules

end
