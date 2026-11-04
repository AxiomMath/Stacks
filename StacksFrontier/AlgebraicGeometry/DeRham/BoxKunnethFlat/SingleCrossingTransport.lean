module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleCrossing

/-!
# The transpose of the crossing map, transported along equalities of modules

The box comparison at modules `𝓤'`, `𝓥'` is the transpose of the comparison of Stacks 01CD at
modules `𝓤 = 𝓤'`, `𝓥 = 𝓥'` followed by the degreewise crossing legs, transported.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.homEquiv_crossingLegs_eqToHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.DeRhamDirectImage
open scoped CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

section Transport

variable {W X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y) (g : W ⟶ S)
  (hp : p ≫ a = g) (hq : q ≫ b = g)

/-- The box comparison as the transpose of the comparison followed by the degreewise crossing
legs, in the spelling of the naive crossing map. -/
theorem tensorMap_eq_homEquiv_naive (U : Modules X.toRingedSpace) (V : Modules Y.toRingedSpace) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
        (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj U)),
        ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj V))))
        (Y := (((pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj U)),
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj V))))
        ((relativeInverseImageToPullbackOfFactors p a g hp U),
        (relativeInverseImageToPullbackOfFactors q b g hq V)) ≫
        inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj U)
            ((_root_.pullback q.toLRSHom.toShHom).obj V)) =
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase g)).homEquiv _ _
        ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso (toInverseImageBase g)
            ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors p a g
            hp)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj U))
            ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors q b g
            hq)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj V))).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf).map
              (crossingLegOfFactors p a g hp U)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf).obj _).map
              (crossingLegOfFactors q b g hq V)) :=
  (tensorMap_relativeInverseImageToPullbackOfFactors_eq_homEquiv_crossingLegs a b p q g hp hq
    U V).trans rfl

/-- The target of the transposed crossing map is the target of the box comparison, transported
along equalities of the modules. -/
theorem crossingTarget_eq (U U' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
    X.toRingedSpace) (hU : U = U')
    (V V' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y.toRingedSpace)
        (hV : V = V') :
    (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase g)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf).obj
        ((StacksDraft.KFlat.modulePullback p.toLRSHom.toShHom).obj U)).obj
        ((StacksDraft.KFlat.modulePullback q.toLRSHom.toShHom).obj V)) =
        (pushforward (toInverseImageBase g)).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj
        (((_root_.pullback p.toLRSHom.toShHom).obj U'),
        ((_root_.pullback q.toLRSHom.toShHom).obj V'))) := by
  subst hU hV
  rfl

/-- **The transpose of the comparison followed by the degreewise crossing legs is the box
comparison**, transported along equalities of the modules. -/
theorem homEquiv_crossingLegs_eqToHom
    (U U' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)
    (hU : U = U')
    (V V' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y.toRingedSpace)
        (hV : V = V') :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (toInverseImageBase g)).homEquiv _ _
        ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso (toInverseImageBase g)
            ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors p a g
            hp)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj U))
            ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors q b g
            hq)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj V))).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf).map
              (crossingLegOfFactors p a g hp U)).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
              W.toRingedSpace.sheaf).obj _).map (crossingLegOfFactors q b g hq V)) ≫
      eqToHom (crossingTarget_eq p q g U U' hU V V' hV) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase g).sheaf).map
        ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors p a g hp)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map (eqToHom hU)))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase g).sheaf).obj _).map
          ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors q b g hq)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map (eqToHom hV))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
          (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
          ((pushforward (toInverseImageBase a)).obj U')),
          ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
          ((pushforward (toInverseImageBase b)).obj V'))))
          (Y := (((pushforward (toInverseImageBase g)).obj
          ((_root_.pullback p.toLRSHom.toShHom).obj U')),
          ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj V'))))
          ((relativeInverseImageToPullbackOfFactors p a g hp U'),
          (relativeInverseImageToPullbackOfFactors q b g hq V')) ≫
        inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj U')
            ((_root_.pullback q.toLRSHom.toShHom).obj V')) := by
  subst hU hV
  have h := (tensorMap_eq_homEquiv_naive a b p q g hp hq U V).symm
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
    Category.id_comp]
  exact (Category.comp_id _).trans h

end Transport

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
