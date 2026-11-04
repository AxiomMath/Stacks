module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionChartSetup

/-!
# The order of vanishing of a pulled-back meromorphic section, read on a chart diagram

Let `f : X ⟶ Y` be a morphism of algebraic spaces along which meromorphic sections pull back
(Stacks 0EN8), with `X` decent, locally Noetherian and integral, let `ℒ` be an invertible
`𝒪_Y`-module with a regular meromorphic section `s`, and let `Z ⊆ X` be a prime divisor. On a
diagram `U ⟶ V` of affine étale charts over `f` with `ℒ` free over `V` on a generator `e` and a
point `u` of `U` over the generic point of `Z`, this file proves

`ord_{Z, f^*ℒ}(f^*s) = ord_{𝒪_{U, u}}(φ(s / e))`,

where `s / e ∈ 𝒦_Y(V)` is the chart ratio of `s`, read at the image `v` of `u` in `Q(𝒪_{V, v})`,
and `φ : Q(𝒪_{V, v}) → Q(𝒪_{U, u})` is induced by the stalk map, assumed to carry nonzerodivisors
to nonzerodivisors. No flatness of `f` is assumed.

## Main results

* `Space.orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map`: the formula
  above.

## References

* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (hXdec : IsDecentSpace B S hS X.1) (hXint : IsIntegralSpace B S hS X.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))

include hXdec hXint hXN in
/-- **The order of vanishing of a pulled-back meromorphic section on a chart diagram.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces along which meromorphic sections pull back, with
`X` decent, locally Noetherian and integral, and let `Y` satisfy the two hypotheses of Stacks
0EN6. Let `ℒ` be an invertible `𝒪_Y`-module, `s` a regular meromorphic section of `ℒ` and `Z` a
prime divisor of `X`. Let `d` be a diagram of affine étale charts over `f`, with `ℒ` free over
`d.V` on the compatible family `e`, and `u` a point of the chart of `X` over the generic point
of `Z`, such that the stalk map `φ : 𝒪_{d.V, v} ⟶ 𝒪_{d.U, u}` at `u` carries nonzerodivisors to
nonzerodivisors. Then

`ord_{Z, f^*ℒ}(f^*s) = ord_{𝒪_{d.U, u}}(φ(s / e))`,

the chart ratio `s / e` being read at `v` in `Q(𝒪_{d.V, v})`. -/
theorem orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map (f : X ⟶ Y)
    (hfm : PullbacksMeromorphicSections B S hS f.hom)
    (hwaY : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS Y, localRingDimension B S hS z = 0)
    (hfinY : HasLocallyFiniteIrreducibleComponents B S hS Y.1)
    (Z : PrimeDivisor B S hS X.1)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (hL : IsInvertibleModule Y L)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hefree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (u : chartScheme d.U) (hu : chartSchemeToPoints B S hS X.1 d.U u = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme d.U).presheaf.stalk u)]
    [Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u)]
    (hφ : ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map d.g).base u))⁰ ≤
      ((chartScheme d.U).presheaf.stalk u)⁰.comap
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    ∃ hc : IsUnit (IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
        (FractionRing ((chartScheme d.U).presheaf.stalk u))
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom hφ
        (chartPointMeromorphicMap B S hS Y d.V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV)
          (((BigFppfOver.toScheme B S hS).map d.g).base u)
          (chartRatio B S hS Y.1 Y.2 L d.V e hecompat hefree s))),
      orderOfVanishingSection.{u, u} B S hS X.2 hXdec Z
          ((modulePullback B S hS f).obj L) (pullbackMeromorphicSection B S hS f L hfm s)
          (Z.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS f).obj L)
            (modulePullbackInvertible f L hL) hXint hXN) =
        Ring.ordTotalFracInt ((chartScheme d.U).presheaf.stalk u) _ hc := by
  have : ∀ W : PrimeDivisor B S hS X.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have hLag := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have hwaX := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS X.2 hXint
  have hfinX := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hXN
  have hσ := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS f hfm L hLag s hs
  let eL : (W : SmallEtale B S hS X.1) → (W ⟶ d.U) →
      ((modulePullback B S hS f).obj L).val.obj (op W) := fun W k =>
    modulePullbackChartSectionRestrict B S hS f L d (e d.V (𝟙 d.V)) k
  have hLcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ d.U) (g : W' ⟶ W),
      (((modulePullback B S hS f).obj L).val.map g.op).hom (eL W k) = eL W' (g ≫ k) :=
    fun W W' k g => modulePullbackChartSectionRestrict_compat B S hS f L d _ W W' k g
  have hLfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ d.U),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eL W k :=
    fun W k => bijective_smul_modulePullbackChartSectionRestrict B S hS f L hLag d e hecompat
      hefree W k
  have heq : eL d.U (𝟙 d.U) = (modulePullbackChartFMap B S hS f L).app d (e d.V (𝟙 d.V)) :=
    modulePullbackChartSectionRestrict_id B S hS f L d _
  have hcY := IsUnit.map
    (chartPointMeromorphicMap B S hS Y d.V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV)
      (((BigFppfOver.toScheme B S hS).map d.g).base u))
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwaY hfinY L d.V hV e
      hecompat hefree s hs)
  have hc := hcY.map (IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
    (FractionRing ((chartScheme d.U).presheaf.stalk u))
    (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom hφ)
  refine ⟨hc, ?_⟩
  have hcX := IsUnit.map
    (chartPointMeromorphicMap B S hS X d.U hU
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU) u)
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwaX hfinX
      ((modulePullback B S hS f).obj L) d.U hU eL hLcompat hLfree _ hσ)
  have hratio := chartRatio_pullbackMeromorphicSection_chartDiagram B S hS f hfm L d e
    hecompat hefree eL hLcompat hLfree heq s
  have hread := chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_le B S hS f hfm d
    hU hV (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU)
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV) u hφ
    (chartRatio B S hS Y.1 Y.2 L d.V e hecompat hefree s)
  have hcomp :=
    (congrArg (chartPointMeromorphicMap B S hS X d.U hU
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU) u) hratio).trans
      hread.symm
  exact (Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
    B S hS hXdec hXint hXN hwaX hfinX ((modulePullback B S hS f).obj L)
    (modulePullbackInvertible f L hL) _ hσ d.U hU eL hLcompat hLfree u hu hcX).trans
    (Ring.ordTotalFracInt_congr ((chartScheme d.U).presheaf.stalk u) hcX hc hcomp)

end AlgebraicGeometry.Space

end
