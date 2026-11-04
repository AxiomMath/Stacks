module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CupProductAndDualityPairing

/-!
# The square of Stacks 0FVB on degree-zero global hypercohomology classes

Let `(X, O_X)` be a ringed space and let `K` and `E` be objects of `D(O_X)` with `E` perfect.
This file states the square of Stacks 0FVB with every corner a degree-zero global
hypercohomology group: for `ξ ∈ H⁰(X, K ⊗^L E^∨)` and `η ∈ H⁰(X, E)`, the map induced on `H⁰` by
the contraction against `ε : E^∨ ⊗^L E ⟶ O_X` applied to the cup product of `ξ` and `η` is the
map induced on `H⁰` by the morphism `E ⟶ K` attached to `ξ`, applied to `η`.

The passage from morphisms `O_X ⟶ Z` to classes of `H⁰(X, Z)` is the covariant naturality of
Stacks 08JA, `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality`;
that identification is injective, which is what lets the square be read back.

## Main results

* `Stacks.SheafOfModules.derivedDualPairingSquareOnClasses`: the square, with the left vertical
  arrow `Stacks.SheafOfModules.derivedDualSectionToHom`.
* `Stacks.SheafOfModules.derivedDualPairingSquareOnClasses_of_applicationLaw`: the square with
  the left vertical arrow the identification `derivedTensorDualGlobalSectionsMap` of
  Stacks 08I1 and 08DQ, as soon as the canonical map of Stacks 08I1 followed by the application
  morphism of Stacks 08J8 is the contraction against `ε`. That equation is
  `Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit`,
  and the resulting square is `Stacks.SheafOfModules.derivedDualPairingSquare`.

## References

* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

-- The ring sheaf of `ringedSite Rc` is `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which pairs
-- `Rc.obj ⋙ forget₂ CommRingCat RingCat` with the sheaf condition directly, while the objects
-- below live over `StructureSheafModules Rc = SheafOfModules (structureSheaf Rc)`, i.e. over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`. The two sheaves of rings are the same
-- sheaf, but seeing it needs `Tensor.ringSheaf` and `CategoryTheory.sheafCompose` unfolded, which
-- instance search does not do at reducible transparency: without this the derived category of one
-- spelling has no `Preadditive` instance at the other, so the identification
-- `H⁰(X, Z) ≃+ (O_X ⟶ Z)` of Stacks 08JA cannot be applied. Same attribute, on the same
-- declaration, for the same reason as in the neighbour that defines `ringedSite`,
-- `StacksDraft.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection`
-- `.InternalHomComplexQuasiIso`.
attribute [local implicit_reducible] CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

variable (K E : DerivedCategory (StructureSheafModules Rc))

variable [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

/-- **The square of Stacks 0FVB on classes, with the left vertical arrow the morphism attached to
a class by contraction.** Let `(X, O_X)` be a ringed space, let `K` and `E` be objects of
`D(O_X)` with `E` perfect, and let `ξ ∈ H⁰(X, K ⊗^L E^∨)` and `η ∈ H⁰(X, E)`. Then the class of
`H⁰(X, K)` obtained by cupping `ξ` with `η` and applying the map induced by the contraction
against `ε : E^∨ ⊗^L E ⟶ O_X` is the class obtained by evaluating on `η` the morphism
`E ⟶ K` given by `Stacks.SheafOfModules.derivedDualSectionToHom` at `ξ`. -/
theorem derivedDualPairingSquareOnClasses
    (hE : (ringedSite Rc).IsPerfect E)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedTensor Rc).obj K).obj (derivedDual Rc E))) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj E) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map (derivedDualContraction Rc K E))
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedTensor Rc).obj
            (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).obj E)).symm
          (derivedSectionTensor Rc
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
              (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ)
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) E η))) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (derivedDualSectionToHom Rc K E
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
              (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ))) η := by
  refine (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) K).injective ?_
  have h1 := derivedStructureSheafGlobalSectionsEquiv_derivedDualContraction Rc K E hE
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ)
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) E η)
  have h2 := RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality (ringedSite Rc)
    (derivedDualSectionToHom Rc K E
      (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
        (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ)) η
  rw [h1, h2]

/-- **The square of Stacks 0FVB on classes, from the equation for the canonical map.** Let
`(X, O_X)` be a ringed space, let `K` and `E` be objects of `D(O_X)` with `E` perfect, and let
`ξ ∈ H⁰(X, K ⊗^L E^∨)` and `η ∈ H⁰(X, E)`. If the canonical map of Stacks 08I1 followed by the
application morphism of Stacks 08J8 is the contraction against `ε` (`happ`), then cupping `ξ`
with `η` and applying the map induced on `H⁰` by the contraction against `ε` gives the same
class of `H⁰(X, K)` as sending `ξ` to the morphism `E ⟶ K` it names under the identification
`H⁰(X, K ⊗^L E^∨) = Hom_{D(O_X)}(E, K)` of Stacks 08I1 and Lemma 08DQ and evaluating the map it
induces on `H⁰` at `η`. -/
theorem derivedDualPairingSquareOnClasses_of_applicationLaw
    (hE : (ringedSite Rc).IsPerfect E)
    (happ : derivedTensorDualToSheafHom Rc E K ▷ E ≫ derivedSheafHomCounit Rc E K =
      derivedDualContraction Rc K E)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedTensor Rc).obj K).obj (derivedDual Rc E))) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj E) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map (derivedDualContraction Rc K E))
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedTensor Rc).obj
            (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).obj E)).symm
          (derivedSectionTensor Rc
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
              (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ)
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) E η))) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (derivedTensorDualGlobalSectionsMap Rc E K ξ)) η := by
  have h3 := derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom_of_applicationLaw
    Rc K E happ
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedTensor Rc).obj K).obj (derivedDual Rc E)) ξ)
  rw [AddEquiv.symm_apply_apply] at h3
  rw [h3]
  exact derivedDualPairingSquareOnClasses Rc K E hE ξ η

end Stacks.SheafOfModules

end
