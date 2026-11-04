module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# Derived pullback is monoidal through K-flat complexes

For a morphism of ringed spaces `f : X ⟶ Y`, the pullback `f^*` on cochain complexes preserves
K-flatness, and on K-flat complexes the derived pullback `Lf^*` is computed by degreewise
pullback. Hence `Lf^*` is a strong monoidal functor `D(𝒪_Y) ⥤ D(𝒪_X)`.

## Main definitions

* `derivedPullbackKFlatIso`: on K-flat objects of the homotopy category, `Lf^*` is isomorphic to
  degreewise pullback.
* `derivedPullbackKFlatMonoidal`: `Lf^*` is strong monoidal for the monoidal structures
  `derivedMonoidal` on `D(𝒪_Y)` and `D(𝒪_X)`.
* `derivedPullbackCanonicalMonoidal`: `Lf^*` is strong monoidal for the monoidal structures
  `canonicalDerivedMonoidal`, whose tensor product is the derived tensor product and whose unit is
  the structure sheaf in degree zero.

## Main results

* `kFlat_pullbackComplex`: `f^*` on cochain complexes preserves K-flatness.
* `derivedPullbackKFlatMonoidal_ε`: the unit of `derivedPullbackKFlatMonoidal`.
* `derivedPullbackCanonicalMonoidal_ε`: the unit of `derivedPullbackCanonicalMonoidal`.

## References

* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction

universe w₁ w₂ u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

/-- The category of sheaves of modules over the structure sheaf of a ringed space `Z` is
abelian. -/
@[instance_reducible] local instance abelianStructureSheafRing (Z : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (structureSheafRing Z)) :=
  _root_.SheafOfModules.instAbelian (structureSheafRing Z)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`f^*` on cochain complexes preserves K-flatness** ([Stacks, Tag 06YC]), with K-flatness
read at the tensor product of the monoidal structure of `Mod(𝒪_Z)`. -/
theorem kFlat_pullbackComplex
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
      K) :
    KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
      ((pullbackComplex f).obj K) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f K hK

section Model

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- The derived category of `𝒪_X`-modules, for the category
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`. -/
@[instance_reducible] local instance hasDerivedCategoryModulesX :
    HasDerivedCategory.{w₁} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :=
  inferInstanceAs (HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))

/-- The derived category of `𝒪_Y`-modules, for the category
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y`. -/
@[instance_reducible] local instance hasDerivedCategoryModulesY :
    HasDerivedCategory.{w₂} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :=
  inferInstanceAs (HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))

/-- **On K-flat objects of the homotopy category, `Lf^*` is degreewise pullback** ([Stacks,
Tag 06YJ]): the comparison of the left derived functor `Lf^*` with `f^*`, restricted to the
K-flat objects, is an isomorphism. -/
def derivedPullbackKFlatIso :
    kFlatQ (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ≅
      CochainComplex.KFlatMonoidal.kFlatLift (StacksDraft.KFlat.modulePullback f)
          (kFlat_pullbackComplex f) ⋙
        kFlatQ (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :=
  have h : ∀ M, IsIso ((Functor.whiskerLeft
      (kFlatObjects
        (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).ι
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)).app M) :=
    fun M ↦ Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      f M.obj.as M.property
  @asIso _ _ _ _ (Functor.whiskerLeft
    (kFlatObjects
      (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).ι
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f))
    (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h)

/-- **Derived pullback is a strong monoidal functor** `D(𝒪_Y) ⥤ D(𝒪_X)`, for
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` on both sides ([Stacks, Tag 079U]). -/
@[instance_reducible]
def derivedPullbackKFlatMonoidal :
    @Functor.Monoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) :=
  CochainComplex.KFlatMonoidal.derivedFunctorMonoidal (StacksDraft.KFlat.modulePullback f)
    (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatIso f)

/-- **Derived pullback is a strong monoidal functor** `D(𝒪_Y) ⥤ D(𝒪_X)`, for
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` on both sides, whose tensor
product is the derived tensor product of [Stacks, Tag 06YU] and whose unit is the structure sheaf
in degree zero, on the nose ([Stacks, Tag 079U]). -/
@[instance_reducible]
def derivedPullbackCanonicalMonoidal :
    @Functor.Monoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
      _ _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) :=
  @MonoidalCategory.reseatFunctorMonoidal _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatMonoidal f)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)

/-! ### The unit -/

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal

/-- The unit of `derivedPullbackKFlatMonoidal`: the image of the unit of `f^*` on the homotopy
category, followed by the inverse of `derivedPullbackKFlatIso` at the unit. -/
lemma derivedPullbackKFlatMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatMonoidal f).toLaxMonoidal =
      DerivedCategory.Qh.map
          (@Functor.LaxMonoidal.ε _ _ _ _ _ _
            ((StacksDraft.KFlat.modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
            (CochainComplex.KFlatMonoidal.mapHomotopyCategoryMonoidal
              (StacksDraft.KFlat.modulePullback f)).toLaxMonoidal) ≫
        (derivedPullbackKFlatIso f).inv.app (𝟙_ ((kFlatObjects (curriedTensor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).FullSubcategory)) :=
  CochainComplex.KFlatMonoidal.derivedFunctorMonoidal_ε
    (A := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
    (B := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)
    (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatIso f)

/-- The unit of `derivedPullbackCanonicalMonoidal` is that of `derivedPullbackKFlatMonoidal`,
conjugated by the unit isomorphisms `canonicalUnitIso`. -/
lemma derivedPullbackCanonicalMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toLaxMonoidal =
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf).inv ≫
        @Functor.LaxMonoidal.ε _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
          _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (derivedPullbackKFlatMonoidal f).toLaxMonoidal ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf).hom :=
  @MonoidalCategory.reseatFunctorMonoidal_ε _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatMonoidal f)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)

end Model

end Stacks.Cohomology.DerivedPullbackTensor

end
