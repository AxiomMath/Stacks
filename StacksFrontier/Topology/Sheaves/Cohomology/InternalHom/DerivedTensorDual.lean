module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual and the map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)` on a ringed space

Let `(X, O_X)` be a ringed space and let `L` be an object of the derived category `D(O_X)` of
sheaves of `O_X`-modules. The **dual** of `L` is `L^∨ = RSheafHom(L, O_X)`, the derived internal
Hom into the structure sheaf. **Stacks 08I1** asserts, for every object `M` of `D(O_X)`, a
canonical map

`M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)`

in `D(O_X)`, together with the map of abelian groups

`H⁰(X, M ⊗^L_{O_X} L^∨) ⟶ Hom_{D(O_X)}(L, M)`

that it induces on degree-zero global hypercohomology, both functorial in `M`.

The canonical map is the derived composition morphism of Stacks 0A8V taken at intermediate
object the structure sheaf: its source there is `RSheafHom(O_X, M) ⊗^L_{O_X} RSheafHom(L, O_X)`,
whose left factor is `M` because the derived internal Hom out of the structure sheaf is the
identity functor. Functoriality in `M` is the covariant naturality of Stacks 0A8V in its target,
transported along that identification. The induced map is the degree-zero global
hypercohomology of the canonical map followed by the identification
`H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` of Stacks 08DK.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site statement of Stacks 08JD applies
verbatim. The declarations below read it off along `Stacks.SheafOfModules.ringedSite`, for the
derived tensor product of `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, exactly as the
derived composition morphism of Stacks 0A8V is read off there.

## Main definitions

* `Stacks.SheafOfModules.derivedDual`: the dual `L^∨ = RSheafHom(L, O_X)`.
* `Stacks.SheafOfModules.derivedTensorDualToSheafHom` (Stacks 08I1): the canonical map
  `M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)`.
* `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap` (Stacks 08I1): the induced map of
  abelian groups `H⁰(X, M ⊗^L_{O_X} L^∨) →+ Hom_{D(O_X)}(L, M)`.

## Main results

* `Stacks.SheafOfModules.derivedTensorDualToSheafHom_eq_composition`: the canonical map is the
  derived composition morphism at intermediate object the structure sheaf, precomposed with the
  identification of `M` with `RSheafHom(O_X, M)`. This is what makes the map content rather
  than an unconstrained morphism of its type.
* `Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality` and
  `Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality_tensorMap` (Stacks 08I1): the
  canonical map is functorial in `M`, in the bifunctor spelling and in the
  `derivedTensorMap`/`derivedSheafHomMap` spelling.
* `Stacks.SheafOfModules.derivedTensorDualSections_naturality`: the canonical map read on
  degree-zero global hypercohomology is functorial in `M`, before the identification of
  Stacks 08DK.
* `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_apply`: the induced map is the
  hypercohomology of the canonical map read through that identification.

## What this file does not contain, and what it used to report absent

Stacks 08I1 asserts that the **induced** map `H⁰(X, M ⊗^L_{O_X} L^∨) ⟶ Hom_{D(O_X)}(L, M)` is
functorial in `M`. That clause is not stated below, but it is **proved**, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality`, as
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_naturality`, which carries the
tag 08I1 for it. It lives in a separate module only because it needs the naturality of
Stacks 08JA, which is not in the import closure of this one.

This section used to report that clause missing from the library. Both of its factors are
proved. Functoriality of the canonical map itself is available in
both of its forms — in `D(O_X)` as `derivedTensorDualToSheafHom_naturality` and on degree-zero
global hypercohomology as `derivedTensorDualSections_naturality`. The other factor, the
compatibility of the identification `H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` of
Stacks 08DK with postcomposition in `M`, is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target` (Tag 08JA)
in `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality` —
which is exactly the covariant companion of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source` that this
section used to record as owed. The two are already assembled, in the same module, as
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`, and since
`derivedTensorDualGlobalSectionsMap Rc` is by definition the ringed-site map at `ringedSite Rc`
that statement applies to the map of this file directly.

For the record of how the obstruction fell: it reduced to the naturality of Stacks 0A94 with
respect to `AlgebraicGeometry.RingedSite.homMap`, proved in both variables as
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`,
off `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap`. The characterising structure indeed
records no compatibility of its `globalSectionsIso` field with `homMap`, but one is not needed:
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v` computes the global description on the
cochain determined by a global section, which is enough.

## References

* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.RingedSite.ringSheaf (ringedSite Rc)` is
-- `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which pairs `Rc.obj ⋙ forget₂ CommRingCat RingCat`
-- with the sheaf condition directly, while the objects below live over
-- `SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc) = SheafOfModules (structureSheaf Rc)`,
-- i.e. over `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`. The two sheaves of rings
-- are the same sheaf, but seeing it needs `CategoryTheory.sheafCompose` unfolded, which instance
-- search and the keyed matching of `rw`/`simp` do not do at reducible transparency: without this
-- attribute the derived category of one spelling has no `Category` instance at the other. Same
-- attribute, on the same declaration, for the same reason as in the neighbour that defines
-- `ringedSite`, `StacksDraft.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection`
-- `.InternalHomComplexQuasiIso`.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived dual on a ringed space.** For an object `L` of `D(O_X)` the dual is
`L^∨ = RSheafHom(L, O_X)`, the derived internal Hom from `L` into the structure sheaf placed in
degree zero. -/
abbrev derivedDual (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  RingedSite.derivedDual (ringedSite Rc) L

/-- The derived dual is the derived internal Hom into the structure sheaf. -/
theorem derivedDual_eq (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    derivedDual Rc L =
      ((derivedSheafHom Rc).obj (op L)).obj (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  rfl

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-- **Stacks 08I1: the canonical map `M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)`.** It is the derived
composition morphism of Stacks 0A8V, taken at intermediate object the structure sheaf, after the
left tensor factor `M` has been identified with `RSheafHom(O_X, M)`. -/
@[stacks 08I1 "the canonical map"]
def derivedTensorDualToSheafHom
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    ((derivedTensor Rc).obj M).obj (derivedDual Rc L) ⟶
      ((derivedSheafHom Rc).obj (op L)).obj M :=
  RingedSite.derivedTensorDualToSheafHom (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L M

/-- The canonical map of Stacks 08I1 is the derived composition morphism at intermediate object
the structure sheaf, precomposed in the left tensor factor with the identification of `M` with
`RSheafHom(O_X, M)`. -/
theorem derivedTensorDualToSheafHom_eq_composition
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    derivedTensorDualToSheafHom Rc L M =
      ((derivedTensor Rc).map
            (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv).app
          (derivedDual Rc L) ≫
        RingedSite.derivedSheafHomComposition (ringedSite Rc)
          (canonicalDerivedTensorProduct (ringedSite Rc))
          (RingedSite.derivedInternalHomOfBifunctor (ringedSite Rc)) L
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) M :=
  rfl

/-- **The canonical map of Stacks 08I1 is functorial in `M`.** This is the covariant naturality
of the derived composition morphism of Stacks 0A8V in its target, together with the naturality
of the identification of `M` with `RSheafHom(O_X, M)`. -/
@[stacks 08I1 "functoriality in M of the canonical map"]
theorem derivedTensorDualToSheafHom_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))} (m : M ⟶ M') :
    ((derivedTensor Rc).map m).app (derivedDual Rc L) ≫
        derivedTensorDualToSheafHom Rc L M' =
      derivedTensorDualToSheafHom Rc L M ≫ ((derivedSheafHom Rc).obj (op L)).map m :=
  RingedSite.derivedTensorDualToSheafHom_naturality (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L m

/-- Functoriality in `M` of the canonical map of Stacks 08I1, in the `derivedTensorMap` and
`derivedSheafHomMap` spelling of the induced maps on the derived tensor product and the derived
internal Hom. -/
@[stacks 08I1 "functoriality in M of the canonical map"]
theorem derivedTensorDualToSheafHom_naturality_tensorMap
    (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))} (m : M ⟶ M') :
    derivedTensorMap Rc m (𝟙 (derivedDual Rc L)) ≫ derivedTensorDualToSheafHom Rc L M' =
      derivedTensorDualToSheafHom Rc L M ≫ derivedSheafHomMap Rc (𝟙 L) m := by
  have htensor : derivedTensorMap Rc m (𝟙 (derivedDual Rc L)) =
      ((derivedTensor Rc).map m).app (derivedDual Rc L) := by
    exact (congrArg (((derivedTensor Rc).map m).app (derivedDual Rc L) ≫ ·)
      (((derivedTensor Rc).obj M').map_id (derivedDual Rc L))).trans (Category.comp_id _)
  have hhom : derivedSheafHomMap Rc (𝟙 L) m = ((derivedSheafHom Rc).obj (op L)).map m := by
    show RingedSite.derivedSheafHomMap (ringedSite Rc) (derivedInternalHom Rc) (𝟙 L) m =
      ((derivedInternalHom Rc).hom.obj (op L)).map m
    exact (congrArg (· ≫ ((derivedInternalHom Rc).hom.obj (op L)).map m)
      (NatTrans.congr_app ((derivedInternalHom Rc).hom.map_id (op L)) M)).trans
        (Category.id_comp _)
  exact (congrArg (· ≫ derivedTensorDualToSheafHom Rc L M') htensor).trans
    ((derivedTensorDualToSheafHom_naturality Rc L m).trans
      (congrArg (derivedTensorDualToSheafHom Rc L M ≫ ·) hhom.symm))

/-- The canonical map of Stacks 08I1 read on degree-zero global hypercohomology, as a map of
abelian groups `H⁰(X, M ⊗^L_{O_X} L^∨) →+ H⁰(X, RSheafHom(L, M))`. -/
def derivedTensorDualSectionsMap
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj
          (((derivedTensor Rc).obj M).obj (derivedDual Rc L))) : Type u) →+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj
          (((derivedSheafHom Rc).obj (op L)).obj M)) : Type u) :=
  RingedSite.derivedTensorDualSectionsMap (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L M

/-- **Functoriality in `M` of the canonical map of Stacks 08I1 on degree-zero global
hypercohomology**, as a commuting square of abelian groups, before the identification of
Stacks 08DK. -/
theorem derivedTensorDualSections_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))} (m : M ⟶ M') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedTensor Rc).map m).app (derivedDual Rc L))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (derivedTensorDualToSheafHom Rc L M')) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (derivedTensorDualToSheafHom Rc L M)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).obj (op L)).map m)) :=
  RingedSite.derivedTensorDualSections_naturality (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L m

/-- **Stacks 08I1: the induced map on degree-zero global cohomology.** The canonical map
`M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)` induces a map of abelian groups

`H⁰(X, M ⊗^L_{O_X} L^∨) ⟶ Hom_{D(O_X)}(L, M)`,

namely its degree-zero global hypercohomology followed by the identification
`H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` of Stacks 08DK. -/
@[stacks 08I1 "the induced map on degree-zero global cohomology"]
def derivedTensorDualGlobalSectionsMap
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj
          (((derivedTensor Rc).obj M).obj (derivedDual Rc L))) : Type u) →+ (L ⟶ M) :=
  RingedSite.derivedTensorDualGlobalSectionsMap (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) L M

/-- The induced map of Stacks 08I1 is the degree-zero global hypercohomology of the canonical
map, read through the identification `H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` of
Stacks 08DK. This pins the map down and is the form in which to rewrite it. -/
theorem derivedTensorDualGlobalSectionsMap_apply
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedTensor Rc).obj M).obj (derivedDual Rc L))) : Type u)) :
    derivedTensorDualGlobalSectionsMap Rc L M z =
      derivedSheafHomGlobalSectionsEquiv Rc L M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (derivedTensorDualToSheafHom Rc L M)) z) :=
  rfl

end Stacks.SheafOfModules

end
