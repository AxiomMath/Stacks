module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProductSummand
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# The naive cup product along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` is the lax comparison

Let `f : X ⟶ S` be a morphism of schemes and `ι : (X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` the morphism of
ringed spaces `Stacks.DeRhamDirectImage.toInverseImageBase f`. Its direct image is restriction
of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`. This file identifies the two lax comparisons
`ι_*M ⊗_{f⁻¹𝒪_S} ι_*N ⟶ ι_*(M ⊗_{𝒪_X} N)` that exist for it:
* the one coming from the adjunction `ι^* ⊣ ι_*`, which is
  `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupLax`;
* the one coming from restriction of scalars, which is
  `Stacks.DeRhamDirectImage.inverseImageTensorLax`.
As a consequence the naive cup product along `ι` is `inverseImageTensorLax` on every summand of
the total tensor complex.

## Main results

* `Stacks.DeRhamDirectImage.naiveCupLax_toInverseImageBase`: the two lax comparisons agree.
* `Stacks.DeRhamDirectImage.ιMapBifunctor_naiveCupProduct_f_toInverseImageBase`: the naive cup
  product along `ι` on the summand indexed by `(i, j)` is `inverseImageTensorLax` followed by
  `ι_*` of the inclusion of that summand.

## The proof

Both comparisons are determined by their values on the canonical sections `x ⊗ y` of the tensor
product sheaf (`PresheafOfModules.tensorSheaf_hom_ext`). The adjoint transpose of the comparison
of Stacks 01CD sends `x ⊗ y` to `η x ⊗ η y`
(`Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul`). The counits then send this to
`ε(η x) ⊗ ε(η y)`, which is `x ⊗ y` by the triangle identity of `ι^* ⊣ ι_*`. That is the value of
`inverseImageTensorLax` (`Stacks.DeRhamDirectImage.inverseImageTensorLax_toTensorSheafSection`).

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.DeRhamDirectImage

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The two lax comparisons along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` agree.** The adjoint transpose of
the comparison of Stacks 01CD followed by the counits,
`Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupLax`, is the restriction-of-scalars
comparison `Stacks.DeRhamDirectImage.inverseImageTensorLax`. -/
theorem naiveCupLax_toInverseImageBase
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupLax (toInverseImageBase f) M N =
      inverseImageTensorLax f M N := by
  let adj := RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (toInverseImageBase f)
  have hsplit : Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupLax
      (toInverseImageBase f) M N =
      adj.homEquiv _ _ (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
        (toInverseImageBase f) ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj M)
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj N)).hom ≫
      (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (adj.counit.app M)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map (adj.counit.app N)) :=
    adj.homEquiv_naturality_right _ _
  apply PresheafOfModules.tensorSheaf_hom_ext
  intro U x y
  have hR := inverseImageTensorLax_toTensorSheafSection f M N U x y x y HEq.rfl HEq.rfl
  refine Eq.trans ?_ hR.symm
  rw [hsplit]
  have h1 := Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul (toInverseImageBase f)
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj M)
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj N) U x y
  refine (congrArg (fun z => (((RingedSpaceModuleAdjunction.modulePushforward
    (toInverseImageBase f)).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
      (adj.counit.app M)).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        (adj.counit.app N))).val.app U).hom z) h1).trans ?_
  have h2 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    X.toRingedSpace _ _ M N (adj.counit.app M) (adj.counit.app N) U.unop
    (((adj.unit.app ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj M)).val.app
      U).hom x)
    (((adj.unit.app ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj N)).val.app
      U).hom y)
  refine h2.trans ?_
  have htri : ∀ (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      (z : _), ((adj.counit.app P).val.app (op (unop U))).hom (((adj.unit.app
      ((StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).obj P)).val.app U).hom z) =
        z := fun P z =>
    congrArg (fun φ => (φ.val.app U).hom z) (adj.right_triangle_components P)
  rw [htri M x, htri N y]
  rfl

/-- **The naive cup product along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` on one summand.** For complexes
`𝒦^•`, `ℳ^•` of `𝒪_X`-modules, on the summand `ι_*𝒦^i ⊗_{f⁻¹𝒪_S} ι_*ℳ^j` of total degree `n`
the naive cup product is the lax comparison `inverseImageTensorLax` followed by `ι_*` of the
inclusion of the summand `𝒦^i ⊗_{𝒪_X} ℳ^j ⊆ Tot^n(𝒦^• ⊗_{𝒪_X} ℳ^•)`. -/
theorem ιMapBifunctor_naiveCupProduct_f_toInverseImageBase
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ) (i j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n) :
    HomologicalComplex.ιMapBifunctor
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
          (toInverseImageBase f)).obj K)
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
          (toInverseImageBase f)).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf) (ComplexShape.up ℤ)
        i j n h ≫
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct
        (toInverseImageBase f) K M).f n =
    inverseImageTensorLax f (K.X i) (M.X j) ≫
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).map
        (HomologicalComplex.ιMapBifunctor K M (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ) i j n h) :=
  (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.ιMapBifunctor_naiveCupProduct_f
    (toInverseImageBase f) K M i j n h).trans (by rw [naiveCupLax_toInverseImageBase]; rfl)

end Stacks.DeRhamDirectImage
