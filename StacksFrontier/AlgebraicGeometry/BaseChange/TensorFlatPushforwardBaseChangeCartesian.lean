module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.FlatOverModel

/-!
# Base change for `Rf_*(E ⊗^L 𝒢^•)` with `𝒢^•` flat over the base, unconditionally

The three steps of the source proof of Stacks 0A1D, stated as Props in
`StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange`, are proved here, and
the conclusion follows.

## Main results

* `AlgebraicGeometry.globalBaseChangeIsIsoOfPointwise`: `GlobalBaseChangeIsIsoOfPointwise`, from
  Stacks 0DJ9 (`AlgebraicGeometry.isIso_derivedBaseChangeComp_of_pointwiseBaseChange`).
* `AlgebraicGeometry.pointwiseBaseChangeOfFlatOver`: `PointwiseBaseChangeOfFlatOver`, the stalk
  check of the proof of Stacks 0A1D
  (`AlgebraicGeometry.isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver`).
* `AlgebraicGeometry.pointwiseBaseChangeTensor`: `PointwiseBaseChangeTensor`, conclusion (1) of
  Stacks 0DJA
  (`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback`).
* `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent`: the
  canonical map of Stacks 0A1D is an isomorphism, with none of the three steps granted, for
  `𝒢^•` flat over `S` (its terms need not be quasi-coherent) and the two derived tensor products
  with quasi-coherent cohomology.  The base's
  `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback` states it under the source's
  hypotheses instead.

## Implementation notes

The stalk check needs neither quasi-coherence of the terms of `𝒢^•` nor quasi-coherence of the
cohomology of `E`; Stacks 0DJ9 needs the cohomology of the two derived tensor products to be
quasi-coherent, and those two memberships, `hK` and `hK'`, are hypotheses of
`isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent`.

## References

* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`GlobalBaseChangeIsIsoOfPointwise` holds**: it is Stacks 0DJ9,
`AlgebraicGeometry.isIso_derivedBaseChangeComp_of_pointwiseBaseChange`, quantified over all
cartesian squares. -/
@[stacks 0DJ9 "the conclusion over every cartesian square at once, in the spelling of \
GlobalBaseChangeIsIsoOfPointwise, with the conditions of Tag 0DJ8 read in form (1)"]
theorem globalBaseChangeIsIsoOfPointwise : GlobalBaseChangeIsIsoOfPointwise.{u} :=
  fun f g f' g' hsq hqc hqs w _ K K' φ hK hK' hp =>
    @isIso_derivedBaseChangeComp_of_pointwiseBaseChange _ _ _ _ f g f' g' hsq hqc hqs K K' φ hK
      hK' hp

/-- **`PointwiseBaseChangeOfFlatOver` holds**: the stalk check of the proof of Stacks 0A1D,
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver`, at every
point and in every degree.  Quasi-coherence of the terms is not used. -/
theorem pointwiseBaseChangeOfFlatOver : PointwiseBaseChangeOfFlatOver.{u} :=
  fun _ _ _ _ hsq w G hG _ hflat x' n =>
    isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver hsq w G hG hflat x' n

/-- **`PointwiseBaseChangeTensor` holds**: it is Stacks 0DJA (1),
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback`.

Cartesianness of the square is needed: for `X = S = S' = Spec ℤ/4`, `X' = Spec ℤ/2`,
`f = g = 𝟙`, `g' = f'` the quotient map, `K = 𝒪_X`, `K' = 𝒪_{X'}` and `φ` the canonical
isomorphism, the map of Stacks 0DJ7 is `ℤ/2 ⟶ ℤ/2`, while for `E = (ℤ/2)~` it is
`0 ⟶ Tor_1^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` in degree `-1`. -/
@[stacks 0DJA "(1), over every cartesian square at once, with the conditions of Tag 0DJ8 read in \
form (1)"]
theorem pointwiseBaseChangeTensor : PointwiseBaseChangeTensor.{u} :=
  fun _ _ _ _ hpb _ E K K' φ h x' n =>
    isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback hpb E K K' φ h x' n

/-- **The canonical map of Stacks 0A1D is an isomorphism**, with none of the three steps of the
source proof granted.  Let `f : X ⟶ S` be quasi-compact and quasi-separated, `E` an object of
`D(𝒪_X)` and `𝒢^•` a bounded-above complex of `𝒪_X`-modules flat over `S`.  For every
cartesian square the map

`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)`

of `tensorFlatBaseChangeMap` is an isomorphism, granted that the two derived tensor products have
quasi-coherent cohomology (`hK`, `hK'`), which is what Stacks 0DJ9 asks of them. -/
theorem isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj G))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj G)))).IsQuasicoherent) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E G) :=
  globalBaseChangeIsIsoOfPointwise f g f' g' hsq hqc hqs hsq.w sq _ _ _ hK hK'
    (pointwiseBaseChangeTensor f g f' g' hsq hsq.w E _ _ _
      (fun x' n => isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver hsq hsq.w
        G hGminus hGflat x' n))

end AlgebraicGeometry

end
