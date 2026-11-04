module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonTensorObj
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# The composition law for pullback is monoidal

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. Pullback of sheaves of modules
is multiplicative: `Stacks.DerivedPullback.Composition.modulePullbackComp` is an isomorphism
`f^* g^* ≅ (f ≫ g)^*`. This file proves that this isomorphism is monoidal for the monoidal
structures `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` on the pullback functors,
whose tensorator is the comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of pullback with the tensor
product.

## Main definitions

* `Stacks.PullbackTensorCoherence.pullbackCompIso`: the composition law `f^* g^* ≅ (f ≫ g)^*`.

## Main results

* `Stacks.PullbackTensorCoherence.tensorSheaf_map_eq_tensorHom`: the tensor product bifunctor on
  a pair of morphisms is their monoidal tensor product.
* `Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp`: the comparison of pullback with
  the tensor product is compatible with the composition law.
* `Stacks.PullbackTensorCoherence.pullbackUnitComparison_comp`: the comparison of pullback with
  the structure sheaf is compatible with the composition law.
* `Stacks.PullbackTensorCoherence.isMonoidal_pullbackCompIso_hom`: the composition law for
  pullback is a monoidal natural isomorphism.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097) — pullback is
  multiplicative.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules

open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

section Comp

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition law for pullback of sheaves of modules, `f^* g^* ≅ (f ≫ g)^*`. -/
noncomputable abbrev pullbackCompIso :
    pullbackFunctor g ⋙ pullbackFunctor f ≅ pullbackFunctor (f ≫ g) :=
  Stacks.DerivedPullback.Composition.modulePullbackComp f g

variable {A B A' B' : SheafOfModules.{u} (structureRingSheaf Z)}

/-- The tensor product bifunctor applied to a pair of morphisms `(u, v)` is the monoidal tensor
product `u ⊗ₘ v`. -/
theorem tensorSheaf_map_eq_tensorHom (u : A ⟶ A') (v : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Z)).presheaf, ((Z)).IsSheaf⟩))).map ((u, v) : ((A, B) : _ × _) ⟶ (A', B')) = u ⊗ₘ v :=
  tensor_hom_ext (A := A) (B := B) fun U a b ↦
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
        _ _ _ u v U a b).trans
      (tensorHom_tmul u v U a b).symm

/-- The inverse of the composition law carries the pullback-unit image of a section along
`f ≫ g` to its iterated pullback-unit image along `g` and then `f`. -/
theorem pullbackCompIso_app_inv_pullbackUnit (M : SheafOfModules.{u} (structureRingSheaf Z))
    (U : (Opens Z.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((pullbackCompIso f g).app M).inv.val.app
        ((opensMap f).op.obj ((opensMap g).op.obj U)) (pullbackUnit (f ≫ g) M U x) =
      pullbackUnit f ((pullbackFunctor g).obj M) ((opensMap g).op.obj U)
        (pullbackUnit g M U x) := by
  rw [← Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit f g M U x]
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app ((pullbackCompIso f g).app M) _ _

end Comp

section Monoidal

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The comparison of pullback with the tensor product is compatible with the composition law
for pullback. -/
theorem pullbackTensorComparison_comp (A B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (pullbackCompIso f g).hom.app (A ⊗ B) ≫ pullbackTensorComparison (f ≫ g) A B =
      (pullbackFunctor f).map (pullbackTensorComparison g A B) ≫
        pullbackTensorComparison f ((pullbackFunctor g).obj A) ((pullbackFunctor g).obj B) ≫
          ((pullbackCompIso f g).hom.app A ⊗ₘ (pullbackCompIso f g).hom.app B) := by
  rw [← tensorSheaf_map_eq_tensorHom]
  exact Stacks.PullbackTensorComposition.comparison_comp f g A B

/-- The comparison of pullback with the structure sheaf is compatible with the composition law
for pullback. -/
theorem pullbackUnitComparison_comp :
    (pullbackCompIso f g).hom.app (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) ≫
        pullbackUnitComparison (f ≫ g) =
      (pullbackFunctor f).map (pullbackUnitComparison g) ≫ pullbackUnitComparison f := by
  refine ((pullbackCompIso f g).app
    (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z)))).eq_inv_comp.mp
      (pullback_hom_ext (f ≫ g) fun U r ↦ ?_)
  show (pullbackUnitComparison (f ≫ g)).val.app ((opensMap (f ≫ g)).op.obj U)
        (pullbackUnit (f ≫ g) (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) U r) =
      (pullbackUnitComparison f).val.app ((opensMap f).op.obj ((opensMap g).op.obj U))
        (((pullbackFunctor f).map (pullbackUnitComparison g)).val.app
          ((opensMap f).op.obj ((opensMap g).op.obj U))
          (((pullbackCompIso f g).app
                (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z)))).inv.val.app
            ((opensMap f).op.obj ((opensMap g).op.obj U))
            (pullbackUnit (f ≫ g) (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) U r)))
  rw [pullbackCompIso_app_inv_pullbackUnit, pullbackUnit_naturality,
    pullbackUnitComparison_pullbackUnit g U r,
    pullbackUnitComparison_pullbackUnit f ((opensMap g).op.obj U) (sharp g U r),
    pullbackUnitComparison_pullbackUnit (f ≫ g) U r]
  rfl

/-- The composition law for pullback is a monoidal natural isomorphism for the monoidal
structures `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, whose tensorator is the
comparison of pullback with the tensor product. -/
theorem isMonoidal_pullbackCompIso_hom :
    letI := pullbackComparisonMonoidal f
    letI := pullbackComparisonMonoidal g
    letI := pullbackComparisonMonoidal (f ≫ g)
    NatTrans.IsMonoidal (pullbackCompIso f g).hom :=
  let := pullbackComparisonMonoidal f
  let := pullbackComparisonMonoidal g
  let := pullbackComparisonMonoidal (f ≫ g)
  { unit := by
      dsimp only [Functor.LaxMonoidal.comp_ε]
      rw [pullbackComparisonMonoidal_epsilon, pullbackComparisonMonoidal_epsilon,
        pullbackComparisonMonoidal_epsilon,
        ← cancel_mono (pullbackUnitComparison (f ≫ g)), Category.assoc, Category.assoc,
        pullbackUnitComparison_comp, Functor.map_inv, IsIso.inv_hom_id_assoc,
        IsIso.inv_hom_id, IsIso.inv_hom_id]
    tensor := fun M N ↦ by
      dsimp only [Functor.LaxMonoidal.comp_μ]
      rw [pullbackComparisonMonoidal_mu, pullbackComparisonMonoidal_mu,
        pullbackComparisonMonoidal_mu, IsIso.eq_comp_inv, Category.assoc, Category.assoc,
        pullbackTensorComparison_comp, Functor.map_inv, IsIso.inv_hom_id_assoc,
        IsIso.inv_hom_id_assoc] }

end Monoidal

end Stacks.PullbackTensorCoherence

end
