module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.StacksAttribute

/-! # Functoriality in `M` of the induced map `H⁰(X, M ⊗^L L^∨) ⟶ Hom_{D(O_X)}(L, M)`

Let `(X, O_X)` be a ringed space and let `L` be an object of `D(O_X)` with dual
`L^∨ = RSheafHom(L, O_X)`. **Stacks 08I1** asserts a canonical map
`M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)` and says that the map of abelian groups

`H⁰(X, M ⊗^L_{O_X} L^∨) ⟶ Hom_{D(O_X)}(L, M)`

it induces is **functorial in `M`**. That clause is proved here;
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual` carries the canonical
map, its characterisation by the derived composition morphism of Stacks 0A8V, its functoriality
in `M`, and the reading of that functoriality on degree-zero global hypercohomology *before* the
identification of Stacks 08DK.

The missing input was the compatibility of the identification
`H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` of Stacks 08DK with postcomposition in `M`. That
compatibility is the naturality of Stacks 08JA in its covariant variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`, and is read
off here along `Stacks.SheafOfModules.ringedSite` exactly as the identification itself is.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_naturality`: the identification of
  Stacks 08DK is natural in both variables for arbitrary morphisms of `D(O_X)`.
* `Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_naturality_target`: the same in the
  covariant variable alone — compatibility with postcomposition in `M`.
* `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_naturality` (Stacks 08I1):
  **the induced map on degree-zero global cohomology is functorial in `M`.**

## Implementation notes

The section "What this file does not contain" of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual` recorded this clause as
absent, on the ground that the naturality of Stacks 0A94 needed a compatibility of
`AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso` with
`AlgebraicGeometry.RingedSite.homMap` which the characterising structure did not record. That is
stale: the compatibility is `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, the global
naturality of Stacks 0A94 is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`, and the
naturality of Stacks 08JA for arbitrary morphisms of the derived category is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`.

A topological space with a sheaf of commutative rings *is* a ringed site, so every statement
below is the ringed-site statement of Stacks 08JD read along
`Stacks.SheafOfModules.ringedSite`, for the derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, exactly as the canonical map and its
functoriality are.

## References

* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

-- `AlgebraicGeometry.RingedSite.ringSheaf (ringedSite Rc)` is
-- `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which pairs `Rc.obj ⋙ forget₂ CommRingCat RingCat`
-- with the sheaf condition directly, while the objects below live over
-- `StructureSheafModules Rc = SheafOfModules (structureSheaf Rc)`, i.e. over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`. The two sheaves of rings are the same
-- sheaf, but seeing it needs `CategoryTheory.sheafCompose` unfolded, which instance search and
-- the keyed matching of `rw`/`simp` do not do at reducible transparency: without this attribute
-- the `simp` identifying `(canonicalDerivedTensorProduct (ringedSite Rc)).tensor` with
-- `derivedTensor Rc` below is stuck. Same attribute, on the same declaration, for the same
-- reason as in `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual` and in
-- the neighbour that defines `ringedSite`,
-- `StacksDraft.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection`
-- `.InternalHomComplexQuasiIso`.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The identification of Stacks 08DK is natural in both variables.** For `φ : L' ⟶ L` and
`ψ : M ⟶ M'` the morphism induced on `RSheafHom` carries the identification of
`H⁰(X, RSheafHom(L, M))` with `Hom_{D(O_X)}(L, M)` to precomposition with `φ` and
postcomposition with `ψ`. This is the ringed-site statement
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`. -/
theorem derivedSheafHomGlobalSectionsEquiv_naturality
    {L L' M M' : DerivedCategory (StructureSheafModules Rc)} (φ : L' ⟶ L) (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv Rc L' M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).map φ.op).app M ≫
              ((derivedSheafHom Rc).obj (op L')).map ψ)) ξ) =
      φ ≫ derivedSheafHomGlobalSectionsEquiv Rc L M ξ ≫ ψ :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality (ringedSite Rc) φ ψ ξ

/-- **The identification of Stacks 08DK is compatible with postcomposition in `M`.** For
`ψ : M ⟶ M'` it carries the degree-zero global hypercohomology of `RSheafHom(L, ψ)` to
postcomposition with `ψ`. This is the clause the induced map of Stacks 08I1 is read through, and
it is the ringed-site statement
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`. -/
theorem derivedSheafHomGlobalSectionsEquiv_naturality_target
    (L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv Rc L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).obj (op L)).map ψ)) ξ) =
      derivedSheafHomGlobalSectionsEquiv Rc L M ξ ≫ ψ :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target (ringedSite Rc) L ψ ξ

/-- **Stacks 08I1: the induced map `H⁰(X, M ⊗^L_{O_X} L^∨) ⟶ Hom_{D(O_X)}(L, M)` is functorial
in `M`.** For `m : M ⟶ M'` the degree-zero global hypercohomology of `m ⊗ 1` carries the induced
map at `M` to the induced map at `M'` followed by postcomposition with `m`.

This is the ringed-site statement
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`, read along
`Stacks.SheafOfModules.ringedSite` for the canonical derived tensor product. -/
@[stacks 08I1 "functoriality in M of the induced map on degree-zero global cohomology"]
theorem derivedTensorDualGlobalSectionsMap_naturality
    (L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedTensor Rc).obj M).obj (derivedDual Rc L))) : Type u)) :
    derivedTensorDualGlobalSectionsMap Rc L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedTensor Rc).map m).app (derivedDual Rc L))) z) =
      derivedTensorDualGlobalSectionsMap Rc L M z ≫ m :=
  RingedSite.derivedTensorDualGlobalSectionsMap_naturality (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L m z

/-- Functoriality in `M` of the induced map of Stacks 08I1, in the `derivedTensorMap` spelling of
the map induced on the derived tensor product. -/
@[stacks 08I1 "functoriality in M of the induced map on degree-zero global cohomology"]
theorem derivedTensorDualGlobalSectionsMap_naturality_tensorMap
    (L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedTensor Rc).obj M).obj (derivedDual Rc L))) : Type u)) :
    derivedTensorDualGlobalSectionsMap Rc L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (derivedTensorMap Rc m (𝟙 (derivedDual Rc L)))) z) =
      derivedTensorDualGlobalSectionsMap Rc L M z ≫ m := by
  have htensor : derivedTensorMap Rc m (𝟙 (derivedDual Rc L)) =
      ((derivedTensor Rc).map m).app (derivedDual Rc L) := by
    let tensor := (canonicalDerivedTensorProduct (ringedSite Rc)).tensor
    exact (congrArg (((tensor.map m).app (derivedDual Rc L)) ≫ ·)
      ((tensor.obj M').map_id (derivedDual Rc L))).trans (Category.comp_id _)
  rw [htensor, derivedTensorDualGlobalSectionsMap_naturality]

end Stacks.SheafOfModules

end
