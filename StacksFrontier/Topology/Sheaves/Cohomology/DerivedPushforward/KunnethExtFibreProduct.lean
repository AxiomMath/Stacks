module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethDischarged
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula for Ext at the fibre product of two schemes

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with its two
projections `p` and `q`, and let `f = p ≫ a = q ≫ b`.  For `K ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)` the
exterior product is `K ⊠ M = Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M`, and the Künneth morphism for Ext
(Equation 36.25.0.1) is the canonical morphism

`Ra_*R𝓗om(K, K') ⊗^𝐋_{𝒪_S} Rb_*R𝓗om(M, M') ⟶ Rf_*(R𝓗om(K ⊠ M, K' ⊠ M'))`.

It is an isomorphism when `a` and `b` are quasi-compact and quasi-separated, `X` and `Y` are Tor
independent over `S`, `K` and `M` are perfect, and `K'` and `M'` lie in `D_QCoh`.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_fibreProduct`: under these
  hypotheses the Künneth morphism for Ext at the fibre product is an isomorphism.

## References

* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.DerivedQCoh
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance 10000] HasDerivedCategory.standard

section FibreProduct

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes,
and let `X` and `Y` be Tor independent over `S`. Let `W = X ×_S Y` with its two projections `p`
and `q` and `f = p ≫ a`. If `K ∈ D(𝒪_X)` is perfect, `K' ∈ D_QCoh(𝒪_X)`, `M ∈ D(𝒪_Y)` is perfect
and `M' ∈ D_QCoh(𝒪_Y)`, then the Künneth morphism for Ext (Equation 36.25.0.1)

`Ra_*R𝓗om(K, K') ⊗^𝐋_{𝒪_S} Rb_*R𝓗om(M, M') ⟶ Rf_*(R𝓗om(K ⊠ M, K' ⊠ M'))`

is an isomorphism. -/
@[stacks 0FXZ]
theorem isIso_kunnethExtMap_fibreProduct
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : AlgebraicGeometry.TorIndependent a b)
    (K K' : DerivedCategory X.Modules) (M M' : DerivedCategory Y.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (hK' : IsDQCoh (R := X.ringCatSheaf) K')
    (hM : RingedSpace.IsPerfect (X := Y.toRingedSpace) M)
    (hM' : IsDQCoh (R := Y.ringCatSheaf) M') :
    IsIso (kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K K' M M') :=
  isIso_kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K K' M M'
    (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hTor
      (sheafHomObj X.toRingedSpace K K') (sheafHomObj Y.toRingedSpace M M')
      (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect X K K' hK hK')
      (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect Y M M' hM hM'))
    (isIso_boxSheafHomMap (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom K K' M M'
      (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
        (pullback.fst a b).toLRSHom.toShHom K hK K')
      (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
        (pullback.snd a b).toLRSHom.toShHom M hM M')
      (isIso_sheafHomTensorMap_of_isPerfect_space (pullback a b).toRingedSpace
        ((derivedPullbackFunctor (pullback.fst a b).toLRSHom.toShHom).obj K)
        ((derivedPullbackFunctor (pullback.fst a b).toLRSHom.toShHom).obj K')
        ((derivedPullbackFunctor (pullback.snd a b).toLRSHom.toShHom).obj M)
        ((derivedPullbackFunctor (pullback.snd a b).toLRSHom.toShHom).obj M')
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
          (pullback.fst a b).toLRSHom.toShHom K hK)
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
          (pullback.snd a b).toLRSHom.toShHom M hM)))

end FibreProduct

end Stacks.Cohomology.DerivedKunnethExt

end
