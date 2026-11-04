module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseChart
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompAssembly
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompTransport
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseRestriction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentDerivedPullbackOpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DJ9

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, `K ∈ D_QCoh(𝒪_X)`,
`K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` whose pointwise maps of Stacks 0DJ7 are invertible
at every point of `X'` and in every degree.  Then `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an
isomorphism.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComp_of_pointwiseBaseChange`: Stacks 0DJ9.
* `AlgebraicGeometry.pointwiseBaseChangeGlobalizes`: the same statement, quantified over all
  cartesian squares.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJ9.** For a cartesian square of schemes with `f` quasi-compact and
quasi-separated, an object `K` of `D_QCoh(𝒪_X)` and a morphism `φ : L(g')^*K ⟶ K'` to an object
of `D_QCoh(𝒪_{X'})` whose pointwise maps of Stacks 0DJ7 are invertible at every point of `X'` and
in every degree, the composition `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
@[stacks 0DJ9]
theorem isIso_derivedBaseChangeComp_of_pointwiseBaseChange (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (hp : PointwiseBaseChange f g f' g' sq.w K K' φ) :
    IsIso (derivedBaseChangeComp f g f' g' sq.w K K' φ) := by
  refine Stacks.Cohomology.BaseChangeCover.isIso_comp_of_affineOpens sq K K' φ
    fun V V' hV hV' hle U hU hUV => ?_
  refine Stacks.Cohomology.BaseChangeCover.repGood_of_chart sq V V' hV hV' hle U hU hUV K K' φ ?_
  intro ch
  have := ch.isOpenImmersion_incU
  have := ch.isOpenImmersion_incV
  have := ch.isOpenImmersion_incV'
  have := ch.isOpenImmersion_incU' sq
  exact isIso_comp_specMap_of_isQuasicoherent ch.isPushout _ _ _
    (isQuasicoherent_homology_derivedPullback_of_isOpenImmersion ch.incU K hK)
    (isQuasicoherent_homology_derivedPullback_of_isOpenImmersion ch.incU' K' hK')
    fun y n => isIso_baseChangeCohomologyMap_pullDatum sq (isPullback_specMap ch.isPushout)
      ch.incU ch.incU' ch.incV ch.incV' ch.wU'U.symm ch.wU.symm ch.wU'V'.symm ch.wV'.symm
      K K' φ y n (hp _ n)

/-- Stacks 0DJ9 over every cartesian square of schemes at once. -/
theorem pointwiseBaseChangeGlobalizes : PointwiseBaseChangeGlobalizes.{u} :=
  fun _ _ _ _ sq _ _ _ K K' φ hK hK' hp =>
    isIso_derivedBaseChangeComp_of_pointwiseBaseChange sq K K' φ hK hK' hp

end AlgebraicGeometry
