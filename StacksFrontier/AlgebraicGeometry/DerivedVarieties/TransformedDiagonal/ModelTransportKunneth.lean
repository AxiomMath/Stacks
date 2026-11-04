module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt

/-!
# The standard-model terms of Tag 0G0A in the vocabulary of the Künneth formula for Ext

`AlgebraicGeometry.derivedExternalTensorStd` and `AlgebraicGeometry.derivedExternalTensorMapStd`
are the derived external tensor product and its pure maps with every derived category taken at
`HasDerivedCategory.standard`. The Künneth formula for Ext of [Stacks, Tag 0FXZ],
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_fibreProduct`, is stated at that model
in the vocabulary of `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt`:
the exterior product `Stacks.Cohomology.DerivedKunnethExt.boxProd` and the tensor product of
morphisms `Stacks.Cohomology.DerivedKunnethExt.tensorMap` at the fibre product, with the derived
pullbacks `Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor` along the two projections.
This file records that the two vocabularies agree, by definitional equality, so that a statement
about the pure maps in either one can be read in the other.

## Main results

* `AlgebraicGeometry.derivedExternalTensorStd_eq_boxProd`: `K ⊠ L` at the standard model is the
  exterior product of the Künneth formula for Ext at the fibre product.
* `AlgebraicGeometry.derivedExternalTensorMapStd_eq_tensorMap`: the pure map `u ⊠ v` at the
  standard model is `tensorMap` of the two pulled-back morphisms.
* `AlgebraicGeometry.DiagonalResolution.transformedImagePairingStd_of_eq_tensorMap`: the pairing
  of `AlgebraicGeometry.DiagonalResolution.transformedImagePairingStd` on a generator, in that
  vocabulary.

## References

* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section DerivedExternalTensor

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **`K ⊠ L` at the standard model is the exterior product of the Künneth formula for Ext**,
`Lp^*K ⊗^𝐋 Lq^*L` on the fibre product with its two projections. -/
theorem derivedExternalTensorStd_eq_boxProd
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    derivedExternalTensorStd f g K L =
      Stacks.Cohomology.DerivedKunnethExt.boxProd (pullback.fst f g).toLRSHom.toShHom
        (pullback.snd f g).toLRSHom.toShHom K L :=
  rfl

/-- **The pure map `u ⊠ v` at the standard model** is the tensor product, at the fibre product,
of the pullbacks of `u` and `v` along the two projections, in the vocabulary of the Künneth
formula for Ext. -/
theorem derivedExternalTensorMapStd_eq_tensorMap
    {K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {L L' : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorMapStd f g u v =
      Stacks.Cohomology.DerivedKunnethExt.tensorMap (pullback f g).toRingedSpace
        ((Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor
          (pullback.fst f g).toLRSHom.toShHom).map u)
        ((Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor
          (pullback.snd f g).toLRSHom.toShHom).map v) :=
  rfl

end DerivedExternalTensor

namespace DiagonalResolution

attribute [local instance] CategoryTheory.Linear.fullSubcategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [Linear k X.Modules] [Linear k Y.Modules]
  (R : DiagonalResolution f) (g : Y ⟶ Spec (.of k)) (F : perfectDerived X ⥤ perfectDerived Y)

/-- The standard-model pairing of Tag 0G0A on a generator `(a, c)`, in the vocabulary of the
Künneth formula for Ext: the tensor product at `X ×_k Y` of the pullbacks of `single(a)` and of
`c` along the two projections. -/
theorem transformedImagePairingStd_of_eq_tensorMap {i j : ℕ} (p : R.ImagePairStd F i j) :
    R.transformedImagePairingStd g F i j (FreeAbelianGroup.of p) =
      Stacks.Cohomology.DerivedKunnethExt.tensorMap (pullback f g).toRingedSpace
        ((Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor
          (pullback.fst f g).toLRSHom.toShHom).map
            ((@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).map
              p.1))
        ((Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor
          (pullback.snd f g).toLRSHom.toShHom).map p.2) :=
  R.transformedImagePairingStd_of g F p

end DiagonalResolution

end AlgebraicGeometry

end
