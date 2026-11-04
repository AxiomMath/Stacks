module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatComputedMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# Derived pullback is a monoidal functor

Let `f : X ⟶ Y` be a morphism of ringed spaces. The derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is a strong monoidal functor for the derived tensor products of
[Stacks, Tag 0FPT] on each side, with tensorator the comparison of [Stacks, Tag 079U]. On K-flat
complexes `Lf^*` is the degreewise pullback, which is monoidal ([Stacks, Tag 01CD]) and preserves
K-flatness.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackMonoidal.kFlatComparison`: on K-flat complexes the derived
  pullback is the degreewise pullback.
* `Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal`: the strong monoidal
  structure on `Lf^*`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Limits
open CochainComplex.KFlatBifunctor

universe w w' u

namespace Stacks.Cohomology.DerivedPullbackMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing Y))]


/-- The monoidal structure on sheaves of `𝒪_Z`-modules given by the sheaf tensor product. -/
@[instance_reducible] local instance monoidalModules (Z : RingedSpace.{u, u}) :
    MonoidalCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalCategorySheafTensor Z.sheaf

/-- The symmetric monoidal structure on sheaves of `𝒪_Z`-modules given by the sheaf tensor
product. -/
@[instance_reducible] local instance symmetricModules (Z : RingedSpace.{u, u}) :
    SymmetricCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.symmetricCategorySheafTensor Z.sheaf

/-- The sheaf tensor product of sheaves of `𝒪_Z`-modules is additive in each variable. -/
local instance monoidalPreadditiveModules (Z : RingedSpace.{u, u}) :
    MonoidalPreadditive (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalPreadditiveSheafTensor Z.sheaf

/-- The closed monoidal structure on sheaves of `𝒪_Z`-modules for the sheaf tensor product. -/
@[instance_reducible] local instance monoidalClosedModules (Z : RingedSpace.{u, u}) :
    MonoidalClosed (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalClosedSheafTensor Z.sheaf

/-- Any two `ℤ`-graded objects in sheaves of `𝒪_Z`-modules have a tensor product. -/
local instance hasTensorModules (Z : RingedSpace.{u, u}) :
    ∀ A B : GradedObject ℤ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z),
      GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

/-- The monoidal structure on cochain complexes of sheaves of `𝒪_Z`-modules induced by the
sheaf tensor product. -/
@[instance_reducible] local instance monoidalComplexes (Z : RingedSpace.{u, u}) :
    MonoidalCategory
      (CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  HomologicalComplex.monoidalCategory _ _

/-- The symmetric monoidal structure on cochain complexes of sheaves of `𝒪_Z`-modules induced
by the sheaf tensor product. -/
@[instance_reducible] local instance symmetricComplexes (Z : RingedSpace.{u, u}) :
    SymmetricCategory
      (CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  CochainComplex.symmetricCategory _

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

/-- The model of `D(𝒪_Y)`, at the spelling of the derived tensor products. -/
local instance hasDerivedCategoryY :
    HasDerivedCategory.{w'} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :=
  inferInstanceAs (HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing Y)))

/-- The model of `D(𝒪_X)`, at the spelling of the derived tensor products. -/
local instance hasDerivedCategoryX :
    HasDerivedCategory.{w} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :=
  inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X)))

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal

omit [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing Y))] in
/-- The degreewise pullback preserves K-flatness, read at `curriedTensor`. -/
theorem kFlat_pullback
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor _) K) :
    KFlat (curriedTensor _)
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f K hK

/-- **On K-flat complexes the derived pullback is the degreewise pullback**, as an isomorphism of
functors on the K-flat objects of the homotopy category. -/
def kFlatComparison :
    kFlatQ (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ≅
      Functor.kFlatLift (StacksDraft.KFlat.modulePullback f) (kFlat_pullback f) ⋙
        kFlatQ (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :=
  NatIso.ofComponents
    (fun P => @asIso _ _ _ _
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app P.obj)
      (by
        obtain ⟨⟨K⟩, hK⟩ := P
        exact Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
          f K hK))
    (fun g =>
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).naturality
        g.hom)

/-- **Derived pullback is a monoidal functor** ([Stacks, Tag 079U] with its coherence): for a
morphism of ringed spaces `f : X ⟶ Y`, `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is strong monoidal for the
derived tensor products `CochainComplex.KFlatMonoidal.derivedMonoidal` of [Stacks, Tag 0FPT], at
any models of the two derived categories. On K-flat complexes its tensorator is the degreewise
comparison of [Stacks, Tag 01CD]. -/
@[instance_reducible]
def derivedPullbackMonoidal :
    @Functor.Monoidal _ _
      (CochainComplex.KFlatMonoidal.derivedMonoidal
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
        (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)) _ _
      (CochainComplex.KFlatMonoidal.derivedMonoidal
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)
        (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) :=
  Functor.kFlatComputedMonoidal (StacksDraft.KFlat.modulePullback f) (kFlat_pullback f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) (kFlatComparison f)

end Stacks.Cohomology.DerivedPullbackMonoidal
