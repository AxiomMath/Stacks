module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleCrossingAssembly

/-!
# The relative box map at single complexes is an isomorphism

For `a : X ⟶ S`, `b : Y ⟶ S` quasi-compact and quasi-separated, and finite-order differential
operator modules `𝓕`, `𝓖` with `𝓖` flat over `S`, the relative box map of [Stacks, Tag 0FLR] at
`𝓕[-i]` and `𝓖[-j]` is an isomorphism: along `τ : X ⟶ (X, a^{-1}𝒪_S)` it is the scheme Künneth
map of [Stacks, Tag 0FU4] at `𝓕[-i]` and `𝓖[-j]`, up to isomorphisms.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_single`.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.DeRhamDirectImage
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open scoped CategoryTheory.Prod

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace Stacks.Cohomology.BoxKunnethFlat

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : FiniteOrderDifferentialOperatorCategory a)
  (G : FiniteOrderDifferentialOperatorCategory b) (i j : ℤ)

/-- **The relative box map at single complexes is an isomorphism**: at `𝓕[-i]` and `𝓖[-j]` with
`𝓖` flat over `S`, for `a` and `b` quasi-compact and quasi-separated. -/
theorem isIso_relativeBoxMap_single [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b]
    [QuasiSeparated b] (hG : IsFlatOver b.toLRSHom.toShHom G.module) :
    IsIso (relativeBoxMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)) := by
  have hX : IsIso
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
      (toInverseImageBase a) ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
      F.module)) :=
      Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
      (toInverseImageBase a) (isClosedEmbedding_toInverseImageBase a)
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)
  have hY : IsIso
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
      (toInverseImageBase b) ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
      G.module)) :=
      Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
      (toInverseImageBase b) (isClosedEmbedding_toInverseImageBase b)
      ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)
  have hW : IsIso
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
      (toInverseImageBase (pullback.fst a b ≫ a)) ((totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (pullback a b).toRingedSpace.sheaf)).obj ((pullbackComplex
      ((pullback.fst a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶ X.toRingedSpace)).obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module),
      (pullbackComplex ((pullback.snd a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶
      Y.toRingedSpace)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
      G.module)))) :=
    Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
        (toInverseImageBase (pullback.fst a b ≫ a)) (isClosedEmbedding_toInverseImageBase
        (pullback.fst a b ≫ a))
        ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (pullback a b).toRingedSpace.sheaf)).obj ((pullbackComplex
        ((pullback.fst a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶ X.toRingedSpace)).obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module),
        (pullbackComplex ((pullback.snd a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶
        Y.toRingedSpace)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
        G.module)))
  exact isIso_kunnethMap_of_crossing (toInverseImageBase a) (inverseImageBaseProjection a)
      (toInverseImageBase b) (inverseImageBaseProjection b)
      (toInverseImageBase (pullback.fst a b ≫ a)) (inverseImageBaseProjection
      (pullback.fst a b ≫ a)) ((pullback.fst a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶
      X.toRingedSpace) ((pullback.snd a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶
      Y.toRingedSpace) (Stacks.Cohomology.BoxKunneth.fstProjection a b)
      (Stacks.Cohomology.BoxKunneth.sndProjection a b)
      (Stacks.Cohomology.BoxKunneth.fstProjection_comp a b)
      (Stacks.Cohomology.BoxKunneth.sndProjection_comp a b)
    (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
        (toInverseImageBase_comp_sndProjection a b) (fst_comp_toInverseImageBase_comp a b)
        (snd_comp_toInverseImageBase_comp a b)
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)
        (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F))
        (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)) (pushforwardSingleIso a F i)
        (pushforwardSingleIso b G j)
    (pushforwardTotalSingleIso a b F G i j) (boxTotalComplexComparisonSingle a b F G i j)
    (naiveCrossing_comp_pushforwardTotalSingleIso a b F G i j).symm
    (isIso_kunnethMap_toInverseImageBase a b F G i j hG) _
    (boxTotalComplexDerivedComparison_single_eq a b F G i j)

end Stacks.Cohomology.BoxKunnethFlat

end
