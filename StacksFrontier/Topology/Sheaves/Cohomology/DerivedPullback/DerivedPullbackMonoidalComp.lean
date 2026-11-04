module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditionalModels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctorComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The composition isomorphism of derived pullbacks is monoidal

For morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of [Stacks, Tag 0D5S] is a monoidal natural isomorphism for the
monoidal structures of [Stacks, Tag 079U] on the three derived pullbacks, at arbitrary models of
the three derived categories.

## Main results

All in the namespace `Stacks.Cohomology.DerivedPullbackTensor`:

* `isMonoidal_modulePullbackComp_hom` — the composition law `g^* ⋙ f^* ≅ (f ≫ g)^*` of sheaves
  of modules is monoidal for the structures of `Stacks.PullbackSheafTensor.monoidal`.
* `isMonoidal_derivedPullbackCompIsoCanonical_hom` — the composition isomorphism is monoidal for
  `derivedPullbackKFlatMonoidal`.
* `isMonoidal_derivedPullbackCompIsoCanonical_hom_canonical` — the same for
  `derivedPullbackCanonicalMonoidal`.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction

universe w₁ w₂ w₃ u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The tensor product of two morphisms for `SheafOfModules.monoidalCategorySheafTensor` is their
tensor product for `Stacks.PullbackGradedAlgebra.monoidalCategory`: the two structures have the
same whiskerings. -/
lemma tensorHom_eq_strict
    {A A' B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (u : A ⟶ A') (v : B ⟶ B') :
    u ⊗ₘ v = @MonoidalCategoryStruct.tensorHom _ _
      (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct _ _ _ _ u v :=
  (tensorHom_def u v).trans ((congrArg₂ (· ≫ ·) (Stacks.RingedSpace.whiskerRight_eq_strict u B)
    (Stacks.RingedSpace.whiskerLeft_eq_strict A' v)).trans
      (@tensorHom_def _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory X) _ _ _ _ u v).symm)

/-- The unit half of `isMonoidal_modulePullbackComp_hom`, in the spelling of
`RingedSpaceModuleAdjunction`. -/
private lemma modulePullbackComp_unit_aux :
    (modulePullbackObjUnitIso f).inv ≫ (modulePullback f).map (modulePullbackObjUnitIso g).inv ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
          (SheafOfModules.unit (structureSheafRing Z)) =
      (modulePullbackObjUnitIso (f ≫ g)).inv := by
  have h : (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
        (SheafOfModules.unit (structureSheafRing Z)) ≫ (modulePullbackObjUnitIso (f ≫ g)).hom =
      (modulePullback f).map (modulePullbackObjUnitIso g).hom ≫ (modulePullbackObjUnitIso f).hom :=
    Stacks.PullbackTensorCoherence.pullbackUnitComparison_comp f g
  rw [← cancel_mono (modulePullbackObjUnitIso (f ≫ g)).hom, Iso.inv_hom_id, Category.assoc,
    Category.assoc, h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

section Strict

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The tensor half of `isMonoidal_modulePullbackComp_hom`, for the monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory`: it is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp` with the comparisons inverted. -/
private lemma modulePullbackComp_tensor_aux (A B : SheafOfModules.{u}
    (Stacks.RingedSpace.structureRingSheaf Z)) :
    letI := Stacks.PullbackTensor.isIso_comparison (f ≫ g) A B
    inv (Stacks.PullbackTensorCoherence.pullbackTensorComparison f
        ((Stacks.RingedSpace.pullbackFunctor g).obj A)
        ((Stacks.RingedSpace.pullbackFunctor g).obj B)) ≫
      (Stacks.RingedSpace.pullbackFunctor f).map
        (inv (Stacks.PullbackTensorCoherence.pullbackTensorComparison g A B)) ≫
        (Stacks.PullbackTensorCoherence.pullbackCompIso f g).hom.app (A ⊗ B) =
      ((Stacks.PullbackTensorCoherence.pullbackCompIso f g).hom.app A ⊗ₘ
        (Stacks.PullbackTensorCoherence.pullbackCompIso f g).hom.app B) ≫
        inv (Stacks.PullbackTensorCoherence.pullbackTensorComparison (f ≫ g) A B) := by
  rw [IsIso.eq_comp_inv, Category.assoc, Category.assoc,
    Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp, Functor.map_inv,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

end Strict

/-- **The composition law for pullback of sheaves of modules is monoidal**, for the monoidal
structures `Stacks.PullbackSheafTensor.monoidal` whose oplax tensorator is the comparison of
[Stacks, Tag 01CD]. -/
theorem isMonoidal_modulePullbackComp_hom :
    NatTrans.IsMonoidal
      (@id (StacksDraft.KFlat.modulePullback g ⋙ StacksDraft.KFlat.modulePullback f ≅
          StacksDraft.KFlat.modulePullback (f ≫ g))
        (Stacks.DerivedPullback.Composition.modulePullbackComp f g)).hom where
  unit := modulePullbackComp_unit_aux f g
  tensor A B := by
    rw [tensorHom_eq_strict]
    exact modulePullbackComp_tensor_aux f g A B

attribute [local instance] abelianStructureSheafRing

section Model

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
  [HasDerivedCategory.{w₃} (SheafOfModules.{u} (structureSheafRing Z))]

attribute [local instance] hasDerivedCategoryModulesX

/-- **The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of [Stacks, Tag 0D5S] is monoidal**
for the monoidal structures `derivedPullbackKFlatMonoidal` of [Stacks, Tag 079U], at arbitrary
models of the three derived categories. -/
theorem isMonoidal_derivedPullbackCompIsoCanonical_hom :
    @NatTrans.IsMonoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
      (@Functor.LaxMonoidal.comp _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
        (derivedPullbackKFlatMonoidal g).toLaxMonoidal
        (derivedPullbackKFlatMonoidal f).toLaxMonoidal)
      (derivedPullbackKFlatMonoidal (f ≫ g)).toLaxMonoidal := by
  have := isMonoidal_modulePullbackComp_hom f g
  have key :=
    DerivedPushforwardComposition.derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models
      f g
  exact CochainComplex.KFlatMonoidal.isMonoidal_derivedFunctorMonoidal_comp
    (kFlat_pullbackComplex g) (kFlat_pullbackComplex f) (kFlat_pullbackComplex (f ≫ g))
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    _ _ _ (derivedPullbackKFlatIso g) (derivedPullbackKFlatIso f) (derivedPullbackKFlatIso (f ≫ g))
    (@id (StacksDraft.KFlat.modulePullback g ⋙ StacksDraft.KFlat.modulePullback f ≅
          StacksDraft.KFlat.modulePullback (f ≫ g))
        (Stacks.DerivedPullback.Composition.modulePullbackComp f g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
    (fun K ↦ key K.obj)

/-- **The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of [Stacks, Tag 0D5S] is monoidal**
for the monoidal structures `derivedPullbackCanonicalMonoidal`, whose tensor products are the
derived tensor products of [Stacks, Tag 06YU] on the nose. -/
theorem isMonoidal_derivedPullbackCompIsoCanonical_hom_canonical :
    @NatTrans.IsMonoidal _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf) _ _
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
      (@Functor.LaxMonoidal.comp _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf) _ _
        (derivedPullbackCanonicalMonoidal g).toLaxMonoidal
        (derivedPullbackCanonicalMonoidal f).toLaxMonoidal)
      (derivedPullbackCanonicalMonoidal (f ≫ g)).toLaxMonoidal :=
  @NatTrans.IsMonoidal.reseat_comp _ _ _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _ _ _ _ _ _ _ _
    (derivedPullbackKFlatMonoidal g) (derivedPullbackKFlatMonoidal f)
    (derivedPullbackKFlatMonoidal (f ≫ g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
    (isMonoidal_derivedPullbackCompIsoCanonical_hom f g)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)

end Model

end Stacks.Cohomology.DerivedPullbackTensor

end
