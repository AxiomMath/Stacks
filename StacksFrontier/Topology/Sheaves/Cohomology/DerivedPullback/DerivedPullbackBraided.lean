module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorBraided
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctorBraided
public import StacksFrontier.Homology.MapHomologicalComplexBraided
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal

/-!
# Derived pullback is a braided monoidal functor

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, the strong monoidal structure of
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` of [Stacks, Tag 079U] is compatible with the symmetries of the derived
tensor products: `Lf^*` is a braided monoidal functor, at any models of the two derived
categories, for `derivedMonoidal`/`derivedSymmetric` and for the re-seated
`canonicalDerivedMonoidal`/`canonicalDerivedSymmetric`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackBraided` — `f^*` is braided.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackBraided` — `Lf^*` is braided for
  `derivedMonoidal`/`derivedSymmetric`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalBraided` — `Lf^*` is braided for
  `canonicalDerivedMonoidal`/`canonicalDerivedSymmetric`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal_δ_braiding`: the
  oplax tensorator of `derivedPullbackCanonicalMonoidal` commutes with the symmetries,
  `Lf^*(β_{K,M}) ≫ δ(M, K) = δ(K, M) ≫ β_{Lf^*K, Lf^*M}`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
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
  abelianStructureSheafRing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The braiding axiom of `f^*` in oplax form, at the spelling of the strict structure. -/
private theorem pullback_braiding_aux
    (A B : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)) :
    (Stacks.RingedSpace.pullbackFunctor f).map
        (@BraidedCategory.braiding _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory Y)
          (Stacks.PullbackTensorCoherence.braidedCategory Y) A B).hom ≫
      Stacks.PullbackTensorCoherence.pullbackTensorComparison f B A =
    Stacks.PullbackTensorCoherence.pullbackTensorComparison f A B ≫
      (@BraidedCategory.braiding _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory X)
          (Stacks.PullbackTensorCoherence.braidedCategory X)
          ((Stacks.RingedSpace.pullbackFunctor f).obj A)
          ((Stacks.RingedSpace.pullbackFunctor f).obj B)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding f A B

/-- **`f^*` on sheaves of modules is a braided monoidal functor**, for the re-seated symmetric
structures and the monoidal structure whose oplax tensorator is the comparison of
[Stacks, Tag 01CD]. -/
@[instance_reducible]
def pullbackBraided : (StacksDraft.KFlat.modulePullback f).Braided :=
  Functor.Braided.ofOplax _ fun A B ↦ by
    rw [Stacks.PullbackSheafTensor.braiding_eq_strict,
      Stacks.PullbackSheafTensor.braiding_eq_strict]
    exact pullback_braiding_aux f A B

section Model

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

attribute [local instance] hasDerivedCategoryModulesX hasDerivedCategoryModulesY

/-- **Derived pullback is a braided monoidal functor** `D(𝒪_Y) ⥤ D(𝒪_X)`, for
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` and
`Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric` on both sides, extending
`derivedPullbackKFlatMonoidal`. -/
@[instance_reducible]
def derivedPullbackBraided :
    @Functor.Braided _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric Y.sheaf).toBraidedCategory _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.sheaf).toBraidedCategory
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) :=
  letI := pullbackBraided f
  CochainComplex.KFlatMonoidal.derivedFunctorBraided (StacksDraft.KFlat.modulePullback f)
    (Functor.mapHomologicalComplexTensorator_braiding (StacksDraft.KFlat.modulePullback f))
    (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatIso f)

/-- `derivedPullbackBraided` extends `derivedPullbackKFlatMonoidal`. -/
lemma derivedPullbackBraided_toMonoidal :
    (derivedPullbackBraided f).toMonoidal = derivedPullbackKFlatMonoidal f :=
  rfl

/-- **Derived pullback is a braided monoidal functor** `D(𝒪_Y) ⥤ D(𝒪_X)` for the re-seated
structures `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` and
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, whose tensor product is the
derived tensor product of [Stacks, Tag 06YU] on the nose, extending
`derivedPullbackCanonicalMonoidal`. -/
@[instance_reducible]
def derivedPullbackCanonicalBraided :
    @Functor.Braided _ _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.sheaf).toBraidedCategory
      _ _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) :=
  @MonoidalCategory.reseatFunctorBraided _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric Y.sheaf).toBraidedCategory _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.sheaf).toBraidedCategory _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackBraided f)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)

/-- `derivedPullbackCanonicalBraided` extends `derivedPullbackCanonicalMonoidal`. -/
lemma derivedPullbackCanonicalBraided_toMonoidal :
    (derivedPullbackCanonicalBraided f).toMonoidal = derivedPullbackCanonicalMonoidal f :=
  rfl

/-- **The oplax tensorator of `Lf^*` commutes with the symmetries** ([Stacks, Tag 079U]): for
`K`, `M` in `D(𝒪_Y)`, `Lf^*(β_{K,M}) ≫ δ(M, K) = δ(K, M) ≫ β_{Lf^*K, Lf^*M}`, for the monoidal
structure `derivedPullbackCanonicalMonoidal` and the symmetries `canonicalDerivedSymmetric`. -/
theorem derivedPullbackCanonicalMonoidal_δ_braiding
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
        (@BraidedCategory.braiding _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric
            Y.sheaf).toBraidedCategory K M).hom ≫
      @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal M K =
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K M ≫
      (@BraidedCategory.braiding _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric
            X.sheaf).toBraidedCategory
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj M)).hom :=
  @Functor.map_braiding_comp_δ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.sheaf).toBraidedCategory
    _ _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackCanonicalBraided f) K M

end Model

end Stacks.Cohomology.DerivedPullbackTensor

end
