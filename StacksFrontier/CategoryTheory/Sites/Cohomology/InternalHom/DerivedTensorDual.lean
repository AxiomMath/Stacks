module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-! # The derived dual and the canonical map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)`

Let `(C, O)` be a ringed site. The **dual** of an object `L` of `D(O)` is
`L^∨ = RSheafHom(L, O)`, the derived internal Hom into the structure sheaf. **Stacks 08JD**
asserts, for every object `M` of `D(O)`, a canonical map

`M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`

in `D(O)`, functorial in `M`, together with the canonical map of abelian groups

`H⁰(C, M ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, M)`

that it induces on degree-zero global hypercohomology.

The canonical map is the composition morphism of derived internal Homs of Stacks 0A98 taken at
intermediate object the structure sheaf: its source there is
`RSheafHom(O, M) ⊗^L_O RSheafHom(L, O)`, and the left factor is `M` because the derived
internal Hom out of the structure sheaf is the identity functor. Functoriality in `M` is the
covariant naturality of Stacks 0A98 in its target, transported along that identification. The
map on degree-zero global hypercohomology is the hypercohomology of the canonical map followed
by the identification `H⁰(C, RSheafHom(L, M)) ≅ Hom_{D(O)}(L, M)` of Stacks 08JA; it is a map
of abelian groups because hypercohomology of a morphism is additive and Stacks 08JA is an
isomorphism of abelian groups.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDual`: the dual `L^∨ = RSheafHom(L, O)`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`: **Stacks 08JD**, the canonical
  map `M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualSectionsMap`: the canonical map read on
  degree-zero global hypercohomology, before the identification of Stacks 08JA.
* `AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap`: **Stacks 08JD**, the
  induced map of abelian groups `H⁰(C, M ⊗^L_O L^∨) →+ Hom_{D(O)}(L, M)`.
* `AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`: the derived internal Hom datum
  of Stacks 0A97 carried by the bifunctor `RSheafHom(-, -)` itself.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_eq_composition`: the canonical map
  is the composition morphism of Stacks 0A98 at intermediate object the structure sheaf,
  precomposed with the identification `M ≅ RSheafHom(O, M)`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality`: the canonical map is
  natural in `M`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualSections_naturality` and
  `AlgebraicGeometry.RingedSite.derivedTensorDualSectionsMap_naturality`: the canonical map on
  degree-zero global hypercohomology is natural in `M`, before the identification of
  Stacks 08JA.

## What this file does not contain

Stacks 08JD asserts that the induced map of abelian groups
`H⁰(C, M ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, M)` is functorial in `M`. That clause is not stated below,
but it is **proved**, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality`,
as `AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`. It lives in a
separate module only because it needs the naturality of Stacks 08JA, which is not in the import
closure of this one.

What that naturality supplies is the compatibility of the identification
`H⁰(C, RSheafHom(L, M)) ≅ Hom_{D(O)}(L, M)` of Stacks 08JA with postcomposition in `M`: a
morphism `m : M ⟶ M'` carries `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv X
L M` to `derivedSheafHomGlobalSectionsEquiv X L M'` along hypercohomology of `RSheafHom(L, m)`
on one side and along `· ≫ m` on the other. It is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`, the
covariant half of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence`.
The naturality of Stacks 08JA rests on the naturality of Stacks 0A94, which needs a
compatibility of
`AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso` with
`AlgebraicGeometry.RingedSite.homMap` that the characterising structure does not record; that
compatibility is `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v` and the naturality of
Stacks 0A94 globally is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`.

## Implementation notes

Stacks 0A98 is parametrised by a derived tensor product datum
(`Stacks.SheafOfModules.DerivedTensorProduct`, Stacks 06YU) and a derived internal Hom datum
(`AlgebraicGeometry.RingedSite.DerivedInternalHom`, Stacks 0A97). The tensor product datum is
carried as a parameter here, since nothing below inspects it; the statements therefore apply to
any derived tensor product, in particular to
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`.

The internal Hom datum, by contrast, is **instantiated**, at
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`, whose bifunctor is literally
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`. This is forced: the two further inputs
are the identification `RSheafHom(O, -) ≅ 𝟭` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and Stacks 08JA, and both are stated
for that bifunctor, so the three only compose there. Instantiating is not a choice of data: the
datum has a genuine body, its comparison field being
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison` and its naturality field
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`; it is *not*
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, whose bifunctor is opaque.

The structure sheaf in degree zero is `AlgebraicGeometry.RingedSite.derivedStructureSheaf`, the
same object the unit identification is stated for, so no bridge between two spellings of the
unit is needed.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole Section 34 cluster, with the
derived category the standard one, as it must be for Stacks 08JA to apply.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived internal Hom of Stacks 0A97 as a datum on the bifunctor `RSheafHom(-, -)`
itself: its K-injective model comparison is the comparison of that bifunctor, and the
naturality field is the naturality of that comparison. -/
abbrev derivedInternalHomOfBifunctor : DerivedInternalHom X where
  hom := derivedSheafHomBifunctor X
  homComparison A B _ := derivedSheafHomComparison X A B
  homComparison_natural f g := derivedSheafHomComparison_naturality X f g

/-- The bifunctor of `derivedInternalHomOfBifunctor` is `RSheafHom(-, -)`. -/
@[simp]
lemma derivedInternalHomOfBifunctor_hom :
    (derivedInternalHomOfBifunctor X).hom = derivedSheafHomBifunctor X :=
  rfl

/-- **The derived dual.** For an object `L` of `D(O)` the dual is `L^∨ = RSheafHom(L, O)`, the
derived internal Hom from `L` into the structure sheaf in degree zero. -/
abbrev derivedDual
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ((derivedSheafHomBifunctor X).obj (op L)).obj (derivedStructureSheaf X)

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **Stacks 08JD: the canonical map `M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`.** It is the composition
morphism of derived internal Homs of Stacks 0A98, taken at intermediate object the structure
sheaf, after the left tensor factor `M` has been identified with `RSheafHom(O, M)`. -/
@[stacks 08JD "the canonical map"]
def derivedTensorDualToSheafHom
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj M).obj (derivedDual X L) ⟶
      ((derivedSheafHomBifunctor X).obj (op L)).obj M :=
  (T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
    derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
      (derivedStructureSheaf X) M

/-- The canonical map of Stacks 08JD is the composition morphism of Stacks 0A98 at intermediate
object the structure sheaf, precomposed in the left tensor factor with the identification of
`M` with `RSheafHom(O, M)`. -/
theorem derivedTensorDualToSheafHom_eq_composition
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorDualToSheafHom X T L M =
      (T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
        (derivedSheafHomCompositionConstruction X T
          (derivedInternalHomOfBifunctor X)).comp L (derivedStructureSheaf X) M :=
  rfl

/-- **The canonical map of Stacks 08JD is functorial in `M`.** This is the covariant naturality
of the composition morphism of Stacks 0A98 in its target, together with the naturality of the
identification of `M` with `RSheafHom(O, M)`. -/
theorem derivedTensorDualToSheafHom_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    (T.tensor.map m).app (derivedDual X L) ≫ derivedTensorDualToSheafHom X T L M' =
      derivedTensorDualToSheafHom X T L M ≫
        ((derivedSheafHomBifunctor X).obj (op L)).map m := by
  have hunit : (derivedStructureSheafHomIso X M).inv ≫
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map m =
        m ≫ (derivedStructureSheafHomIso X M').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact derivedStructureSheafHomIso_naturality X m
  have hcollapse :
      (T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
          (T.tensor.map (((derivedSheafHomBifunctor X).obj
            (op (derivedStructureSheaf X))).map m)).app (derivedDual X L) =
        (T.tensor.map m).app (derivedDual X L) ≫
          (T.tensor.map (derivedStructureSheafHomIso X M').inv).app (derivedDual X L) := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, hunit,
      CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  have hnat : derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
          (derivedStructureSheaf X) M ≫
        ((derivedSheafHomBifunctor X).obj (op L)).map m =
      (T.tensor.map (((derivedSheafHomBifunctor X).obj
            (op (derivedStructureSheaf X))).map m)).app (derivedDual X L) ≫
        derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
          (derivedStructureSheaf X) M' :=
    (derivedSheafHomCompositionConstruction X T
      (derivedInternalHomOfBifunctor X)).natural_target m
  -- The canonical map is spelled out here rather than unfolded by a tactic: the source of
  -- derived composition and the tensor product with the dual agree only at default
  -- transparency, so a goal produced by unfolding is one that no rewriting tactic can match.
  have key : (T.tensor.map m).app (derivedDual X L) ≫
        ((T.tensor.map (derivedStructureSheafHomIso X M').inv).app (derivedDual X L) ≫
          derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
            (derivedStructureSheaf X) M') =
      ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
          derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
            (derivedStructureSheaf X) M) ≫
        ((derivedSheafHomBifunctor X).obj (op L)).map m := by
    rw [Category.assoc, hnat, ← Category.assoc, ← Category.assoc, hcollapse]
  exact key

/-- The canonical map of Stacks 08JD read on degree-zero global hypercohomology, as a map of
abelian groups `H⁰(C, M ⊗^L_O L^∨) →+ H⁰(C, RSheafHom(L, M))`. -/
def derivedTensorDualSectionsMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          ((T.tensor.obj M).obj (derivedDual X L))) : Type u) →+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u) :=
  AddCommGrpCat.Hom.hom
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedTensorDualToSheafHom X T L M)))

/-- **Functoriality in `M` of the canonical map of Stacks 08JD on degree-zero global
hypercohomology**, as a commuting square of abelian groups. -/
theorem derivedTensorDualSections_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((T.tensor.map m).app (derivedDual X L))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedTensorDualToSheafHom X T L M')) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedTensorDualToSheafHom X T L M)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op L)).map m)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    derivedTensorDualToSheafHom_naturality]

/-- `derivedTensorDualSectionsMap` is natural in `M`, read on elements. -/
theorem derivedTensorDualSectionsMap_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        ((T.tensor.obj M).obj (derivedDual X L))) : Type u)) :
    derivedTensorDualSectionsMap X T L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((T.tensor.map m).app (derivedDual X L))) z) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj (op L)).map m))
        (derivedTensorDualSectionsMap X T L M z) := by
  show ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          ((T.tensor.map m).app (derivedDual X L))) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedTensorDualToSheafHom X T L M'))) z = _
  rw [derivedTensorDualSections_naturality]
  rfl

/-- **Stacks 08JD: the canonical map on degree-zero global hypercohomology.** The canonical map
`M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` induces a map of abelian groups

`H⁰(C, M ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, M)`,

namely its degree-zero global hypercohomology followed by the identification
`H⁰(C, RSheafHom(L, M)) ≅ Hom_{D(O)}(L, M)` of Stacks 08JA. -/
@[stacks 08JD "map on degree-zero derived global sections"]
def derivedTensorDualGlobalSectionsMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          ((T.tensor.obj M).obj (derivedDual X L))) : Type u) →+ (L ⟶ M) :=
  (derivedSheafHomGlobalSectionsEquiv X L M).toAddMonoidHom.comp
    (derivedTensorDualSectionsMap X T L M)

/-- The map of Stacks 08JD on degree-zero global hypercohomology is the hypercohomology of the
canonical map, read through the identification of Stacks 08JA. -/
theorem derivedTensorDualGlobalSectionsMap_apply
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        ((T.tensor.obj M).obj (derivedDual X L))) : Type u)) :
    derivedTensorDualGlobalSectionsMap X T L M z =
      derivedSheafHomGlobalSectionsEquiv X L M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedTensorDualToSheafHom X T L M)) z) :=
  rfl

end AlgebraicGeometry.RingedSite

end
