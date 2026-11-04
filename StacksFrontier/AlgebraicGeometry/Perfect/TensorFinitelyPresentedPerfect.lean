module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedNoetherianModel
import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0A1H

Let `f : X ⟶ S` be a morphism of finite presentation, `E ∈ D(𝒪_X)` perfect and `𝒢^•` a bounded
complex of finitely presented `𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a perfect object of `D(𝒪_S)` and its formation commutes with
arbitrary base change.

## Main results

* `AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`:
  [Stacks, Tag 0A1H].

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The perfectness half of [Stacks, Tag 0A1H] over an affine base.** -/
theorem isPerfect_derivedPushforward_tensor_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (hG : FlatProperSupportFinitelyPresented f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) :=
  isPerfect_derivedPushforward_tensor_of_singleDegree f E G hG fun M hfp hflat hsupp => by
    have := hfp
    obtain ⟨Z, hZ, hMZ⟩ := hsupp
    exact Scheme.isPerfect_derivedPushforward_tensor_singleDegree_of_isAffine f E hE M hflat
      (isProperOver_of_le f (show (⟨SheafOfModules.supp M, _⟩ : Closeds X) ≤ Z from hMZ) hZ)

/-- **The perfectness half of [Stacks, Tag 0A1H].** -/
theorem isPerfect_derivedPushforward_tensor {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (G : CochainComplex X.Modules ℤ)
    (hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  refine isPerfect_of_forall_isAffineOpen _ fun W hW => ?_
  have : IsAffine W.toScheme := hW
  have sq := (isPullback_morphismRestrict f W).flip
  have : LocallyOfFinitePresentation (f ∣_ W) := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiCompact (f ∣_ W) := MorphismProperty.of_isPullback sq hf.quasiCompact
  have : QuasiSeparated (f ∣_ W) := MorphismProperty.of_isPullback sq hf.quasiSeparated
  have := isIso_tensorFlatBaseChangeMap_of_isPullback f W.ι (f ∣_ W) (f ⁻¹ᵁ W).ι sq
    hf.quasiCompact hf.quasiSeparated (comp_toShHom_of_comm sq.w) E
    (fun n => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE n) G hG.minus
    hG.isQuasicoherent hG.isFlatOver
  exact isPerfect_of_iso_scheme
    (asIso (tensorFlatBaseChangeMap f W.ι (f ∣_ W) (f ⁻¹ᵁ W).ι (comp_toShHom_of_comm sq.w) E
      G)).symm
    (isPerfect_derivedPushforward_tensor_of_isAffine (f ∣_ W) _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE) _ (hG.pullback sq))

/-- **[Stacks, Tag 0A1H].** Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let
`E` be a perfect object of `D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented
`𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a perfect object of `D(𝒪_S)`, and its formation commutes with
arbitrary base change: for every cartesian square the canonical map
`Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` of
`AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism. -/
@[stacks 0A1H]
theorem isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : FinitePresentation f) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (G : CochainComplex X.Modules ℤ)
    (hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G) :=
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  ⟨isPerfect_derivedPushforward_tensor f hf E hE G hG, fun g f' g' hsq =>
    isIso_tensorFlatBaseChangeMap_of_isPullback f g f' g' hsq hf.quasiCompact hf.quasiSeparated _
      E (fun n => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE n) G
      hG.minus hG.isQuasicoherent hG.isFlatOver⟩

end AlgebraicGeometry

end
