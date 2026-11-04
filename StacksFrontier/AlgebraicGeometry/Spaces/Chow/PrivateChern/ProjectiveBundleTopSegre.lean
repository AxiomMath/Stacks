module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FirstChernCapChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow

/-!
# Injectivity of flat pullback along a projective bundle, from étale charts

Let `(π : P ⟶ X, ℒ)` be a proper flat morphism of good algebraic spaces of relative dimension `d`
with an invertible `ℒ` on `P`, and `Φ(α) = q_*(c₁(ℒ)^d ∩ q^*α)` on a base change `q : Y ×_X P ⟶ Y`.
The top-degree case of Stacks 0ERU, `Φ(α) ∼_rat α`, is local on `Y` for the étale topology: if
every point of `Y` lies in the image of an étale `g : W ⟶ Y` on which `Φ_W([Z']) ∼_rat [Z']` on
`|Z'|` for every integral closed subspace `Z' ⊆ W`, then `Φ_Y([Z]) = [Z]` for every integral
`Z ⊆ Y` (choose a chart through a point of `|Z|`; on it `Φ_W(g^*[Z]) ∼_rat g^*[Z]` on
`|g|^{-1}|Z|` by the reduction to integral cycles, and the étale descent of
`AlgebraicGeometry.Space.PrivateChern.topSegreCycle_flatPullbackMap_integralCycle_eq_of_etale`
applies), hence `Φ_Y(α) ∼_rat α` for every cycle. With Stacks 0EQY and Stacks 0EQC this is the
injectivity of `q^*` on Chow groups after every base change (the injectivity half of Stacks 0ERV).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.topSegreCycle_flatPullbackMap_integralCycle_eq_of_charts`:
  `Φ_Y([Z]) = [Z]` from étale charts.
* `AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_of_charts`: injectivity of the
  flat pullback after every base change, from étale charts on every base change.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-- **The top-degree identity on an integral subspace, from étale charts.** Let `q : Q ⟶ Y` be
proper and flat of relative dimension `d` between good algebraic spaces, `ℒ` invertible on `Q`.
Suppose that every point of `|Y|` lies in the image of an étale `g : W ⟶ Y` with a cartesian
square `(g', q_W)` over `(q, g)`, `q_W` proper and flat of relative dimension `d`, `g'` flat of
relative dimension `0`, such that `Φ_W([Z']) ∼_rat [Z']` on `|Z'|` for every integral
`Z' ⊆ W`, `Φ_W` being built from `q_W` and `g'^*ℒ`. Then `Φ_Y([Z]) = [Z]` for every integral
`Z ⊆ Y`. -/
theorem topSegreCycle_flatPullbackMap_integralCycle_eq_of_charts
    {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {q : Q ⟶ Y}
    (hq : q ≫ sY = sQ) (hqp : IsProper D.site D.base D.base_mem q) (d : ℕ)
    (hqf : IsFlat D.site D.base D.base_mem q)
    (hqd : HasRelativeDimension d D.site D.base D.base_mem q)
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hcharts : ∀ y : points D.site D.base D.base_mem Y,
      ∃ (W QW : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sW : W ⟶ D.space)
        (hW : D.IsGood sW) (sQW : QW ⟶ D.space) (hQW : D.IsGood sQW) (g : W ⟶ Y)
        (g' : QW ⟶ Q) (qW : QW ⟶ W) (_ : IsPullback g' qW q g) (_ : g ≫ sY = sW)
        (hqW : qW ≫ sW = sQW) (_ : g' ≫ sQ = sQW) (_ : IsEtale D.site D.base D.base_mem g)
        (_ : y ∈ Set.range (pointsMap D.site D.base D.base_mem W g))
        (hqWp : IsProper D.site D.base D.base_mem qW)
        (hqWf : IsFlat D.site D.base D.base_mem qW)
        (hqWd : HasRelativeDimension d D.site D.base D.base_mem qW)
        (_ : IsFlat D.site D.base D.base_mem g')
        (_ : HasRelativeDimension 0 D.site D.base D.base_mem g'),
        ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n)
          (Z' : IntegralClosedSubspace D.site D.base D.base_mem W)
          (hZ' : deltaDimension D sW Z' = k),
          RationallyEquivalentOn.{u + 1} D sW hW k
            (subspacePointSet D.site D.base D.base_mem W Z'.subspace)
            (topSegreCycle D sQW hQW sW hW hqW hqWp.2.1.2 (pullbackLine D sQW hQW sQ hQ g' L)
              (isInvertibleModule_pullbackLine D sQW hQW sQ hQ g' L hL) d k n hkn
              (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd k n hkn
                (integralCycle D sW k Z' hZ')))
            (integralCycle D sW k Z' hZ'))
    (k n : ℤ) (hkn : k + (d : ℤ) = n)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) (hZ : deltaDimension D sY Z = k) :
    topSegreCycle D sQ hQ sY hY hq hqp.2.1.2 L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn (integralCycle D sY k Z hZ)) =
      integralCycle D sY k Z hZ := by
  obtain ⟨W, QW, sW, hW, sQW, hQW, g, g', qW, sq, hg, hqW, hg', hget, ⟨w, hw⟩, hqWp, hqWf, hqWd,
    hg'f, hg'0, hchart⟩ := hcharts (Z.ambientGenericPoint D.site D.base D.base_mem)
  have hgf := isFlat_of_isEtale D.site D.base D.base_mem hget
  have hg0 := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem g hY.1 hget
  have hgq := isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hget
  have hT : (Z.preimagePointSet D.site D.base D.base_mem g).Nonempty :=
    ⟨w, by
      show pointsMap D.site D.base D.base_mem W g w ∈
        subspacePointSet D.site D.base D.base_mem Y Z.subspace
      rw [hw]
      exact ⟨_, rfl⟩⟩
  have hTc : IsClosed (Z.preimagePointSet D.site D.base D.base_mem g) :=
    Z.isClosed_preimagePointSet D.site D.base D.base_mem g hY.1
  refine topSegreCycle_flatPullbackMap_integralCycle_eq_of_etale D sY hY sQ hQ sW hW sQW hQW sq hq
    hg hqW hg' hqp d hqf hqd hgf hg0 hgq hqWp hqWf hqWd hg'f hg'0 L hL k n hkn Z hZ
    (flatPullbackMap_integralCycle_ne_zero_of_isEtale D sY hY sW hW hg hget hgf hg0 k Z hZ hT) ?_
  refine rationallyEquivalentOn_topSegreCycle_flatPullbackMap D sQW hQW sW hW hqW hqWp.2.1.2 d
    hqWf hqWd _ _ (k + ((0 : ℕ) : ℤ)) (n + ((0 : ℕ) : ℤ)) (by omega) _ hTc
    (fun Z' hZ' _ => hchart _ _ _ Z' hZ') _ ?_
  intro V hV
  have := subspacePointSet_subset_of_flatPullbackMap_ne_zero D sW hW sY hY g hg 0 hgf hg0 k
    (k + ((0 : ℕ) : ℤ)) rfl _ _
    (fun V' hV' => by rw [eq_of_integralCycleCoeff_ne_zero D Z hV']) V hV
  exact this

/-- **Injectivity of flat pullback after every base change, from étale charts.** Let
`(π : P ⟶ X, ℒ)` be a projective bundle datum of relative dimension `d` over a good `X`. Suppose
that on every base change `q : Q = Y ×_X P ⟶ Y` along a morphism of good algebraic spaces, with
`ℒ_Q` the inverse image of `ℒ`, every point of `|Y|` lies in the image of an étale chart on which
the top-degree identity holds for integral cycles, as in
`AlgebraicGeometry.Space.PrivateChern.topSegreCycle_flatPullbackMap_integralCycle_eq_of_charts`.
Then the flat pullback along `π` is injective on Chow groups after every base change. -/
theorem hasInjectiveChowBaseChange_of_charts {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {d : ℕ} (P : ProjectiveBundleDatum D sX hX d)
    (hcharts : ∀ ⦃Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sY : Y ⟶ D.space)
      (_ : D.IsGood sY) (f : Y ⟶ X) (_ : f ≫ sX = sY)
      (hQ : D.IsGood (pullback.fst f P.proj ≫ sY)) (y : points D.site D.base D.base_mem Y),
      let p : (⟨pullback f P.proj, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P.space, P.isGood.1⟩ := ObjectProperty.homMk (pullback.snd f P.proj)
      ∃ (W QW : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sW : W ⟶ D.space)
        (hW : D.IsGood sW) (sQW : QW ⟶ D.space) (hQW : D.IsGood sQW) (g : W ⟶ Y)
        (g' : QW ⟶ pullback f P.proj) (qW : QW ⟶ W) (_ : IsPullback g' qW (pullback.fst f P.proj) g)
        (_ : g ≫ sY = sW) (hqW : qW ≫ sW = sQW) (_ : g' ≫ pullback.fst f P.proj ≫ sY = sQW)
        (_ : IsEtale D.site D.base D.base_mem g)
        (_ : y ∈ Set.range (pointsMap D.site D.base D.base_mem W g))
        (hqWp : IsProper D.site D.base D.base_mem qW)
        (hqWf : IsFlat D.site D.base D.base_mem qW)
        (hqWd : HasRelativeDimension d D.site D.base D.base_mem qW)
        (_ : IsFlat D.site D.base D.base_mem g')
        (_ : HasRelativeDimension 0 D.site D.base D.base_mem g'),
        ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n)
          (Z' : IntegralClosedSubspace D.site D.base D.base_mem W)
          (hZ' : deltaDimension D sW Z' = k),
          RationallyEquivalentOn.{u + 1} D sW hW k
            (subspacePointSet D.site D.base D.base_mem W Z'.subspace)
            (topSegreCycle D sQW hQW sW hW hqW hqWp.2.1.2
              (pullbackLine D sQW hQW _ hQ g'
                ((modulePullback D.site D.base D.base_mem p).obj P.twist))
              (isInvertibleModule_pullbackLine D sQW hQW _ hQ g' _
                (modulePullbackInvertible p P.twist P.isInvertible_twist)) d k n hkn
              (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd k n hkn
                (integralCycle D sW k Z' hZ')))
            (integralCycle D sW k Z' hZ')) :
    HasInjectiveChowBaseChange.{u + 1} D sX P.proj d := by
  refine hasInjectiveChowBaseChange_of_topSegre D sX hX P.toBase P.isGood P.proj P.proj_comp
    P.isProper d P.isFlat P.hasRelativeDimension P.twist P.isInvertible_twist ?_
  intro Y sY hY f hf hQ hqc hflatq hdq
  have hqp : IsProper D.site D.base D.base_mem (pullback.fst f P.proj) :=
    isProper_of_isPullback D.site D.base D.base_mem hQ.1 P.isGood.1 hY.1 hX.1
      (IsPullback.of_hasPullback f P.proj).flip P.isProper
  refine ⟨fun k α hα =>
      PrivateChow.isRationallyEquivalentToZero_firstChernCapCycleMap D _ hQ _ _ k hα,
    fun k β hβ => isRationallyEquivalentToZero_properCyclePushforward D _ hQ sY hY rfl hqp k β hβ,
    fun k n hkn α =>
      isRationallyEquivalentToZero_topSegreCycle_flatPullbackMap_sub.{u + 1} D _ hQ sY hY
        rfl hqc d hflatq hdq _ _ k n hkn (fun Z hZ => ?_) α⟩
  rw [topSegreCycle_flatPullbackMap_integralCycle_eq_of_charts D _ hQ sY hY rfl hqp d hflatq hdq _
    _ (hcharts sY hY f hf hQ) k n hkn Z hZ]
  exact rationallyEquivalentOn_refl.{u + 1} D sY hY k _ _

end AlgebraicGeometry.Space.PrivateChern

end
