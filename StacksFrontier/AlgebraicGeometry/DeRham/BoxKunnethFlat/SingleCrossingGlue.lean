module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleCrossingIdentity

/-!
# The naive crossing map against steps (4)–(5) at single complexes

For finite-order differential operator modules `𝓕` and `𝓖` placed in degrees `i` and `j`, the naive
crossing map followed by the isomorphism `θ` of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.pushforwardTotalSingleIso` is the map of
steps (4)–(5) of [Stacks, Tag 0FLR] from the degreewise pullbacks of the direct images.

## Main results

* `naiveCrossing_comp_pushforwardTotalSingleIso`: at single complexes, the naive crossing map
  followed by `θ` is the map of steps (4)–(5).

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
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

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : FiniteOrderDifferentialOperatorCategory a)
  (G : FiniteOrderDifferentialOperatorCategory b) (i j : ℤ)

/-- The comparison at the two terms, in the spelling of the crossing legs. -/
theorem comparisonAppIso_single_eq :
    (comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
        (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
        F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
        (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
        G.module))).X j)) = Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
        (toInverseImageBase (pullback.fst a b ≫ a)) ((StacksDraft.KFlat.modulePullback
        (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
        rfl)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)))
        ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors
        (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj
        (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X j))) :=
  rfl

/-- The identification of the terms, in the spelling of the transported crossing map. -/
theorem eqToHom_pushforward_tensor_single_ι :
    eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
        (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j (i + j)
        rfl = eqToHom (crossingTarget_eq (pullback.fst a b) (pullback.snd a b)
        (pullback.fst a b ≫ a) (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
        F.module).X i) (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module
        (single_module_eq a F i) (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
        G.module).X j) (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j).module
        (single_module_eq b G j)) ≫ HomologicalComplex.ιMapBifunctor
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
        (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j (i + j)
        rfl :=
  rfl

/-- The concrete second crossing leg in degree `j`. -/
theorem naiveCrossingLeg_snd_f : (Stacks.Cohomology.KunnethNaive.naiveCrossingLeg
    (toInverseImageBase b) (toInverseImageBase (pullback.fst a b ≫ a))
    (pullback.snd a b).toLRSHom.toShHom (relativeInverseImageProjectionOfFactors (pullback.snd a b)
    b (pullback.fst a b ≫ a) pullback.condition.symm)
    (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
    (pullback.fst a b ≫ a) pullback.condition.symm)
    ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j =
    (crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm
    (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X j)) :=
  naiveCrossingLeg_ofFactors_f (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm
    ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module) j

/-- First step: the first crossing leg. -/
theorem ι_naiveCrossing_step₁ : (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map
            ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase a)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
            (Stacks.Cohomology.BoxKunneth.fstProjection a b)
            (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)).f i)).app _
            ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
            _).map ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.snd a b).toLRSHom.toShHom
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm)
            (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j)) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map ((crossingLegOfFactors (pullback.fst a b) a
            (pullback.fst a b ≫ a) rfl (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module).X i)))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).obj _).map
            ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.snd a b).toLRSHom.toShHom
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm)
            (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j)) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl := by
  rw [naiveCrossingLeg_fst_f]
  rfl

/-- Second step: the second crossing leg. -/
theorem ι_naiveCrossing_step₂ : (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map ((crossingLegOfFactors (pullback.fst a b) a
            (pullback.fst a b ≫ a) rfl (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module).X i)))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).obj _).map
            ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.snd a b).toLRSHom.toShHom
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm)
            (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j)) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map ((crossingLegOfFactors (pullback.fst a b) a
            (pullback.fst a b ≫ a) rfl (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module).X i)))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).obj _).map
            ((crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module).X j)))) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl := by
  rw [naiveCrossingLeg_snd_f]
  rfl

/-- Third step: the comparison at the two terms. -/
theorem ι_naiveCrossing_step₃ : (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map ((crossingLegOfFactors (pullback.fst a b) a
            (pullback.fst a b ≫ a) rfl (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module).X i)))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).obj _).map
            ((crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module).X j)))) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
            (toInverseImageBase (pullback.fst a b ≫ a)) ((StacksDraft.KFlat.modulePullback
            (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
            rfl)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)))
            ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj
            (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X j)))).hom
            ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).map
            ((crossingLegOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)))).app
            _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
            _).map ((crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module).X j)))) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl := by
  rw [comparisonAppIso_single_eq]
  rfl

/-- The naive crossing side on the summand, with the crossing legs of the box comparison. -/
theorem ι_naiveCrossing_eq_crossingLegs :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map
            ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase a)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
            (Stacks.Cohomology.BoxKunneth.fstProjection a b)
            (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)).f i)).app _
            ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
            _).map ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.snd a b).toLRSHom.toShHom
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm)
            (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j)) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl =
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
          ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
              (toInverseImageBase (pullback.fst a b ≫ a)) ((StacksDraft.KFlat.modulePullback
              (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
              rfl)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj
              (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)))
              ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors
              (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
              ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj
              (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X
              j)))).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).map
                (crossingLegOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
                (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X
                i))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
                (pullback a b).toRingedSpace.sheaf).obj _).map
                (crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
                pullback.condition.symm (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
                j).obj G.module).X j))) ≫
        eqToHom (crossingTarget_eq (pullback.fst a b) (pullback.snd a b) (pullback.fst a b ≫ a)
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module
            (single_module_eq a F i) (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module).X j) (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X
            j).module (single_module_eq b G j))) ≫ HomologicalComplex.ιMapBifunctor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl :=
  (ι_naiveCrossing_step₁ a b F G i j).trans ((ι_naiveCrossing_step₂ a b F G i j).trans
    ((ι_naiveCrossing_step₃ a b F G i j).trans
      ((congrArg (_ ≫ ·) (eqToHom_pushforward_tensor_single_ι a b F G i j)).trans
        (Category.assoc _ _ _).symm)))

/-- The naive crossing side on the summand, as the box comparison. -/
theorem ι_naiveCrossing_eq_boxComparison :
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
          ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
              (toInverseImageBase (pullback.fst a b ≫ a)) ((StacksDraft.KFlat.modulePullback
              (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
              rfl)).obj ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj
              (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)))
              ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors
              (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
              ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj
              (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X
              j)))).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).map
                (crossingLegOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
                (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X
                i))).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
                (pullback a b).toRingedSpace.sheaf).obj _).map
                (crossingLegOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
                pullback.condition.symm (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
                j).obj G.module).X j))) ≫
        eqToHom (crossingTarget_eq (pullback.fst a b) (pullback.snd a b) (pullback.fst a b ≫ a)
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module
            (single_module_eq a F i) (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module).X j) (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X
            j).module (single_module_eq b G j))) ≫ HomologicalComplex.ιMapBifunctor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl =
      (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).map ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
              rfl)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
              pullback.condition.symm)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map
              (eqToHom (single_module_eq b G j)))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
          (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).map
          (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.fst a b) a
          (pullback.fst a b ≫ a) rfl)).obj ((pushforward (toInverseImageBase a)).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.snd a b) b
          (pullback.fst a b ≫ a) pullback.condition.symm)).obj
          ((pushforward (toInverseImageBase b)).obj ((((HomologicalComplex.single _
          (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (Y := (((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (relativeInverseImageToPullbackOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module),
          relativeInverseImageToPullbackOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
          pullback.condition.symm ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X
          j).module)) ≫
        inverseImageTensorLax (pullback.fst a b ≫ a) ((_root_.pullback
            (pullback.fst a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) i).obj F).X i).module)) ((_root_.pullback
            (pullback.snd a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) j).obj G).X j).module)))) ≫ HomologicalComplex.ιMapBifunctor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl :=
  congrArg (· ≫ HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
      (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j (i + j)
      rfl)
    (homEquiv_crossingLegs_eqToHom a b (pullback.fst a b) (pullback.snd a b) (pullback.fst a b ≫ a)
        rfl
      pullback.condition.symm (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
          F.module).X i) (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module
          (single_module_eq a F i) (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
          G.module).X j) (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j).module
          (single_module_eq b G j))

/-- The box comparison on the summand, in the spelling of steps (4)–(5). -/
theorem boxComparison_eq_ψ :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
        ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
              rfl)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
              pullback.condition.symm)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map
              (eqToHom (single_module_eq b G j)))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
          (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).map
          (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.fst a b) a
          (pullback.fst a b ≫ a) rfl)).obj ((pushforward (toInverseImageBase a)).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.snd a b) b
          (pullback.fst a b ≫ a) pullback.condition.symm)).obj
          ((pushforward (toInverseImageBase b)).obj ((((HomologicalComplex.single _
          (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (Y := (((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (relativeInverseImageToPullbackOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module),
          relativeInverseImageToPullbackOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
          pullback.condition.symm ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X
          j).module)) ≫
        inverseImageTensorLax (pullback.fst a b ≫ a) ((_root_.pullback
            (pullback.fst a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) i).obj F).X i).module)) ((_root_.pullback
            (pullback.snd a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) j).obj G).X j).module))) ≫ HomologicalComplex.ιMapBifunctor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).map ((StacksDraft.KFlat.modulePullback
          (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map
              (eqToHom (single_module_eq b G j)))) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl :=
  rfl

/-- The first component of `ψ`. -/
theorem singleBoxComparison_step₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor
    (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
    ((StacksDraft.KFlat.modulePullback (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((pushforwardSingleIso a F i).hom.f i))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl = ((Stacks.SheafOfModules.Tensor.sheafTensor
            (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
            ((StacksDraft.KFlat.modulePullback (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl := by
  rw [pushforwardSingleIso_hom_f a F i]
  rfl

/-- The second component of `ψ`. -/
theorem singleBoxComparison_step₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor
    (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
    ((StacksDraft.KFlat.modulePullback (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl = ((Stacks.SheafOfModules.Tensor.sheafTensor
            (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
            ((StacksDraft.KFlat.modulePullback (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map
              (eqToHom (single_module_eq b G j)))) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl := by
  rw [pushforwardSingleIso_hom_f b G j]
  rfl

/-- The box comparison on the summand, in the form of `ι_singleBoxComparison`. -/
theorem boxComparison_eq_ι_singleBoxComparison :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase (pullback.fst a b ≫ a)).sheaf).map
        ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a)
              rfl)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
              (eqToHom (single_module_eq a F i))))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
          (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
              pullback.condition.symm)).map
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map
              (eqToHom (single_module_eq b G j)))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
          (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).map
          (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.fst a b) a
          (pullback.fst a b ≫ a) rfl)).obj ((pushforward (toInverseImageBase a)).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.snd a b) b
          (pullback.fst a b ≫ a) pullback.condition.symm)).obj
          ((pushforward (toInverseImageBase b)).obj ((((HomologicalComplex.single _
          (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (Y := (((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module))),
          ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
          ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j).module)))))
          (relativeInverseImageToPullbackOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
          ((((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i).module),
          relativeInverseImageToPullbackOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
          pullback.condition.symm ((((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X
          j).module)) ≫
        inverseImageTensorLax (pullback.fst a b ≫ a) ((_root_.pullback
            (pullback.fst a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) i).obj F).X i).module)) ((_root_.pullback
            (pullback.snd a b).toLRSHom.toShHom).obj ((((HomologicalComplex.single _
            (ComplexShape.up ℤ) j).obj G).X j).module)))) ≫ HomologicalComplex.ιMapBifunctor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).map ((StacksDraft.KFlat.modulePullback
          (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((pushforwardSingleIso a F i).hom.f i))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl :=
  (Category.assoc _ _ _).trans ((boxComparison_eq_ψ a b F G i j).trans
    ((singleBoxComparison_step₁ a b F G i j).trans (singleBoxComparison_step₂ a b F G i j)).symm)

/-- A composite of two functors preserving zero morphisms sends zero objects to zero objects. -/
private theorem isZero_obj_obj_of_isZero {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] {X : C} (h : IsZero X) :
    IsZero (G.obj (F.obj X)) :=
  G.map_isZero (F.map_isZero h)

/-- **The naive crossing map followed by `θ` is the map of steps (4)–(5)**, at single complexes. -/
theorem naiveCrossing_comp_pushforwardTotalSingleIso :
    (Stacks.Cohomology.KunnethNaive.naiveCrossing (toInverseImageBase a) (toInverseImageBase b)
        (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
        (pullback.snd a b).toLRSHom.toShHom (Stacks.Cohomology.BoxKunneth.fstProjection a b)
        (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
        pullback.condition.symm) (toInverseImageBase_comp_relativeInverseImageProjection
        (pullback.fst a b) a) (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors
        (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)) ≫
        (pushforwardTotalSingleIso a b F G i j).hom = singleBoxComparison a b F G i j := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := ((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
      ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
      F.module)))) (K₂ := ((pullbackComplex (relativeInverseImageProjectionOfFactors
      (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
      ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
      G.module)))) (F := (Stacks.SheafOfModules.Tensor.sheafTensor
      (inverseImageBase (pullback.fst a b ≫ a)).sheaf))
    (fun i' j' hij => ?_)
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h
    have hn : i' + j' = n := hij
    subst hn
    exact (ι_naiveCrossing_pushforwardTotalSingleIso a b F G i' j').trans
      ((ι_naiveCrossing_eq_crossingLegs a b F G i' j').trans
        ((ι_naiveCrossing_eq_boxComparison a b F G i' j').trans
          ((boxComparison_eq_ι_singleBoxComparison a b F G i' j').trans
            (ι_singleBoxComparison a b F G i' j').symm)))
  · exact (Stacks.ConcentratedComplex.isZero_obj_obj_X_X _ _ _ i j
      (fun k hk => isZero_obj_obj_of_isZero (StacksDraft.KFlat.modulePushforward _)
        (StacksDraft.KFlat.modulePullback _) (HomologicalComplex.isZero_single_obj_X _ _ _ k hk))
      (fun k hk => isZero_obj_obj_of_isZero (StacksDraft.KFlat.modulePushforward _)
        (StacksDraft.KFlat.modulePullback _) (HomologicalComplex.isZero_single_obj_X _ _ _ k hk))
      i' j' (not_and_or.mp h)).eq_of_src _ _

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
