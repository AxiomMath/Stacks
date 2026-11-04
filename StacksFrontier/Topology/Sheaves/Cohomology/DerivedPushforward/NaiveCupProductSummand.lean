module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite

/-!
# The naive cup product on one summand of the total tensor complex

Let `f : X ⟶ Y` be a morphism of ringed spaces and `𝒦^•`, `ℳ^•` complexes of `𝒪_X`-modules. The
naive cup product `Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct` is defined as an
adjoint transpose under `f^* ⊣ f_*`. This file computes it on each summand
`f_*𝒦^i ⊗ f_*ℳ^j` of each total degree `n`. There it is the two-sided lax comparison
`f_*𝒦^i ⊗_{𝒪_Y} f_*ℳ^j ⟶ f_*(𝒦^i ⊗_{𝒪_X} ℳ^j)`, followed by `f_*` of the inclusion of the
summand.

## Main definitions

* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupLax`: the lax comparison
  `f_*M ⊗_{𝒪_Y} f_*N ⟶ f_*(M ⊗_{𝒪_X} N)`. It is the adjoint transpose of the comparison
  `f^*(f_*M ⊗ f_*N) ≅ f^*f_*M ⊗ f^*f_*N` of Stacks 01CD followed by the counit in each factor.

## Main results

* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.ιMapBifunctor_naiveCupProduct_f`: the naive
  cup product on the summand indexed by `(i, j)` is `naiveCupLax` followed by `f_*` of the
  inclusion of that summand.
* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.ιMapBifunctor_totalComplexPair_map`: the
  total tensor complex of a pair of morphisms, on one summand.

## Implementation notes

The statements mix two spellings of the structure sheaf of a ringed space,
`Stacks.SheafOfModules.Tensor.ringSheaf` and `structureSheafRing`, and the two retyped functors
of `StacksFrontier.Homology.KFlat.Pullback`. These are unfolded at `implicit` transparency here, as
in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct`. The summand
formula for a morphism of total complexes is stated at the spelling `totalComplexPair` of the
complexes it is applied to. Rewriting with `HomologicalComplex.ι_mapBifunctorMap` directly would
ask Lean to identify two syntheses of the `HasZeroMorphisms` instance on these modules, and that
exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.NaiveCupProductOnRingedSpaces

universe u

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

/-- The total tensor complex, on a pair of morphisms of complexes of `𝒪_X`-modules, restricted
to the summand indexed by `(i, j)`: it is the tensor product of the two components followed by
the inclusion of that summand.  This is `HomologicalComplex.ι_mapBifunctorMap` at the spelling
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`. -/
theorem ιMapBifunctor_totalComplexPair_map {X : RingedSpace.{u, u}}
    {K K' L L' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (i j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n) :
    HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) i j n h ≫
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map (a ×ₘ b)).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (a.f i)).app (L.X j) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (K'.X i)).map (b.f j) ≫
        HomologicalComplex.ιMapBifunctor K' L' (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ) i j n h :=
  (congrArg (fun φ => HomologicalComplex.ιMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) i j n h ≫
      HomologicalComplex.Hom.f φ n)
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map _ a b)).trans
    (HomologicalComplex.ι_mapBifunctorMap a b _ (ComplexShape.up ℤ) i j n h)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The two-sided comparison `f_*M ⊗_{𝒪_Y} f_*N ⟶ f_*(M ⊗_{𝒪_X} N)`: the adjoint transpose of
the comparison of Stacks 01CD followed by the counit in each factor. -/
def naiveCupLax (M N : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
        ((StacksDraft.KFlat.modulePushforward f).obj M)).obj
        ((StacksDraft.KFlat.modulePushforward f).obj N) ⟶
      (StacksDraft.KFlat.modulePushforward f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) :=
  (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).homEquiv _ _
    ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso f _ _).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).counit.app M)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).counit.app N))

variable (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- **The naive cup product on the summand indexed by `(i, j)`.** On
`f_*𝒦^i ⊗_{𝒪_Y} f_*ℳ^j ⊆ Tot^n(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•)` the naive cup product is the lax
comparison `f_*𝒦^i ⊗_{𝒪_Y} f_*ℳ^j ⟶ f_*(𝒦^i ⊗_{𝒪_X} ℳ^j)` followed by `f_*` of the inclusion of
the summand `𝒦^i ⊗_{𝒪_X} ℳ^j ⊆ Tot^n(𝒦^• ⊗_{𝒪_X} ℳ^•)`. -/
theorem ιMapBifunctor_naiveCupProduct_f (i j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n) :
    HomologicalComplex.ιMapBifunctor ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ) i j n h ≫
      (naiveCupProduct f K M).f n =
    naiveCupLax f (K.X i) (M.X j) ≫ (StacksDraft.KFlat.modulePushforward f).map
      (HomologicalComplex.ιMapBifunctor K M (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) i j n h) := by
  let adj := RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f
  rw [naiveCupProduct_eq_unit_comp, HomologicalComplex.comp_f]
  show _ ≫ adj.unit.app _ ≫ (StacksDraft.KFlat.modulePushforward f).map
    ((naiveCupProductTranspose f K M).f n) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (StacksDraft.KFlat.modulePushforward f).map
    ((naiveCupProductTranspose f K M).f n)) (adj.unit.naturality
      (HomologicalComplex.ιMapBifunctor ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M) (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
        (ComplexShape.up ℤ) i j n h))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  show adj.unit.app _ ≫ (StacksDraft.KFlat.modulePushforward f).map
      ((StacksDraft.KFlat.modulePullback f).map (HomologicalComplex.ιMapBifunctor
        ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ) i j n h)) ≫
      (StacksDraft.KFlat.modulePushforward f).map ((naiveCupProductTranspose f K M).f n) = _
  refine (congrArg (adj.unit.app _ ≫ ·)
    (Functor.map_comp (StacksDraft.KFlat.modulePushforward f) _ _).symm).trans ?_
  have hT : (StacksDraft.KFlat.modulePullback f).map (HomologicalComplex.ιMapBifunctor
        ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ) i j n h) ≫
      (naiveCupProductTranspose f K M).f n =
      ((Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso f _ _).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
          (adj.counit.app (K.X i))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (K.X i)).map
          (adj.counit.app (M.X j))) ≫
        HomologicalComplex.ιMapBifunctor K M (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ) i j n h := by
    rw [naiveCupProductTranspose, HomologicalComplex.comp_f]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso_hom_app]
    refine (congrArg (· ≫ _)
      (Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_hom f
        ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M) i j n h)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (ιMapBifunctor_totalComplexPair_map
      ((complexAdjunction f).counit.app K) ((complexAdjunction f).counit.app M) i j n h)).trans ?_
    simp only [Category.assoc, Functor.id_obj, complexAdjunction_counit_app_f]
    rfl
  rw [hT]
  refine (congrArg (adj.unit.app _ ≫ ·)
    ((StacksDraft.KFlat.modulePushforward f).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (· ≫ _) ?_
  exact (adj.homEquiv_unit _ _ _).symm

end Stacks.Cohomology.NaiveCupProductOnRingedSpaces
