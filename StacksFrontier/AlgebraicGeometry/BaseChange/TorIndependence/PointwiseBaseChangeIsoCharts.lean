module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseBaseChangeIso

/-!
# Stacks 0DJ9 from the charts

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, `K ∈ D_QCoh(𝒪_X)`,
`K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`. Stacks 0DJ9 asks condition (1) of Stacks 0DJ8 for
`φ` on `X'`; its proof only uses that condition after pulling the datum back to the Cartesian
affine-open charts of the square. This module states 0DJ9 with that weaker hypothesis: condition
(1) of Stacks 0DJ8 for the pulled-back datum on the square of spectra of every chart. It is what
an argument has to supply when the datum is only understood chart by chart, for instance when the
pointwise statement is proved from an approximation that exists on affine opens only.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComp_of_chartwise`

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJ9, from condition (1) of Stacks 0DJ8 on the charts.** For a cartesian square of
schemes with `f` quasi-compact and quasi-separated, an object `K` of `D_QCoh(𝒪_X)` and a morphism
`φ : L(g')^*K ⟶ K'` to an object of `D_QCoh(𝒪_{X'})`, suppose that for every Cartesian
affine-open chart of the square the datum pulled back to the square of spectra of the chart has
invertible maps of Stacks 0DJ7 at every point and in every degree. Then the composition
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
theorem isIso_derivedBaseChangeComp_of_chartwise (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (hp : ∀ (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (n : ℤ),
      IsIso (baseChangeCohomologyMap (Spec.map ch.a) (Spec.map ch.b) (Spec.map ch.d)
        (Spec.map ch.c) (isPullback_specMap ch.isPushout).w
        ((derivedPullback ch.incU.toLRSHom.toShHom).obj K)
        ((derivedPullback ch.incU'.toLRSHom.toShHom).obj K')
        (Stacks.Cohomology.BaseChangeCover.pullDatum (Spec.map ch.c).toLRSHom.toShHom
          ch.incU'.toLRSHom.toShHom ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm ch.wU'U.symm) K K' φ) y n)) :
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
    (hp ch)

end AlgebraicGeometry

end
