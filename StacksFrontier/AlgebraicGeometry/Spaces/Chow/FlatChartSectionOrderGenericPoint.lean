module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatChartSectionOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint

/-!
# The dominating case: a prime divisor over the generic point has order of vanishing zero

Let `f : X ⟶ Y` be a **flat** morphism of decent, locally Noetherian, integral algebraic spaces
over a scheme `S`, let `ℒ` be an invertible `𝒪_Y`-module and `s` a regular meromorphic section of
it, and let `Z ⊆ X` be a prime divisor whose generic point `ξ` maps to the **generic point of
`Y`**.  This file proves

`ord_{Z, f^*ℒ}(f^*s) = 0`,

with `f^*s` the pullback of Stacks 0ENC, part (1) and the order of vanishing read at the
canonical ratio of Stacks 0EPR.

This is the case of **Stacks 0EQQ** in which the prime divisor of `X` lies over the generic
point of `Y` rather than over a prime divisor of `Y`; the case of a prime divisor lying over a
prime divisor is
`AlgebraicGeometry.Space.orderOfVanishingSection_pullbackMeromorphicSection_eq_length_mul`.

## Main results

* `Ring.exists_isUnit_algebraMap_eq_of_isField`: over a field, every unit of a fraction ring is
  the image of a unit of the field.
* `exists_isUnit_chartPointMeromorphicMap_chartRatio_of_eq_genericPoint`: the chart ratio of a
  regular meromorphic section, read at a point of an affine étale chart lying over the generic
  point of an integral algebraic space, is the image of a unit of the chart stalk.
* `orderOfVanishingSection_pullbackMeromorphicSection_eq_zero_of_eq_genericPoint`: the identity
  above.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

/-! ### Over a field, a unit of the fraction ring is the image of a unit -/

namespace Ring

/-- **Over a field, every unit of a fraction ring is the image of a unit.**  If `A` is a field
and `Q` a ring of fractions of `A`, then every unit `x` of `Q` is `algebraMap A Q r` for some unit
`r` of `A`. -/
theorem exists_isUnit_algebraMap_eq_of_isField {A Q : Type*} [CommRing A] [CommRing Q]
    [Algebra A Q] [IsFractionRing A Q] (hA : IsField A) {x : Q} (hx : IsUnit x) :
    ∃ r : A, IsUnit r ∧ algebraMap A Q r = x := by
  let : Field A := hA.toField
  have : Nontrivial Q := (IsFractionRing.injective A Q).nontrivial
  have hself : IsFractionRing A A :=
    IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mpr fun a ha =>
      isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero ha)
  obtain ⟨r, hr⟩ := (IsFractionRing.self_iff_surjective (K := Q)).mp hself x
  refine ⟨r, isUnit_iff_ne_zero.mpr fun h0 => ?_, hr⟩
  rw [h0, map_zero] at hr
  exact hx.ne_zero hr.symm

end Ring

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart ratio at a point over the generic point is the image of a unit -/

/-- **The chart ratio of a regular meromorphic section, read at a point over the generic point,
is the image of a unit of the chart stalk.**  Let `Y` be an integral algebraic space over `S`,
let `ℒ` be an `𝒪_Y`-module free over an affine étale chart `V` on a compatible family `e`, let
`s` be a regular meromorphic section of `ℒ` and let `v` be a point of the scheme of `V` lying
over the generic point of `Y`.  Then the reading of the chart ratio `s / e` at `v`
(`AlgebraicGeometry.Space.chartPointMeromorphicMap`) is the image of a unit of `𝒪_{V, v}`. -/
theorem exists_isUnit_chartPointMeromorphicMap_chartRatio_of_eq_genericPoint
    (Y : AlgebraicSpaces B S hS) (hYint : IsIntegralSpace B S hS Y.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS Y, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS Y.1)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s)
    (v : chartScheme V)
    (hv : chartSchemeToPoints B S hS Y.1 V v = genericPoint B S hS Y.2 hYint) :
    ∃ r : (chartScheme V).presheaf.stalk v, IsUnit r ∧
      chartPointMeromorphicMap B S hS Y V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwa hfin V hV) v
          (chartRatio B S hS Y.1 Y.2 L V e hecompat hebij s) =
        algebraMap ((chartScheme V).presheaf.stalk v)
          (FractionRing ((chartScheme V).presheaf.stalk v)) r := by
  have hdim : localRingDimension B S hS (chartSchemeToPoints B S hS Y.1 V v) = 0 := by
    rw [hv]
    exact localRingDimension_genericPoint_eq_zero B S hS Y.2 hYint
  have hfield : IsField ((chartScheme V).presheaf.stalk v) :=
    isField_stalk_chart_of_localRingDimension_eq_zero B S hS Y.2
      hYint.hasEtaleLocalProperty_isReduced hdim
      ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).mpr V.property)
      (chartPoint_chartSchemeToPoints B S hS Y V v)
  obtain ⟨r, hr, hrr⟩ := Ring.exists_isUnit_algebraMap_eq_of_isField hfield
    (IsUnit.map (chartPointMeromorphicMap B S hS Y V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwa hfin V hV) v)
      (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwa hfin L V hV e
        hecompat hebij s hs))
  exact ⟨r, hr, hrr.symm⟩

/-! ### The order of vanishing of a pulled-back section over the generic point -/

variable {X Y : AlgebraicSpaces B S hS}
    (hXdec : IsDecentSpace B S hS X.1)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))

include hXdec hXint hYint hXN hYN in
/-- **The dominating case of Stacks 0EQQ.**  Let `f : X ⟶ Y` be a flat morphism of decent,
locally Noetherian, integral algebraic spaces over `S`, let `ℒ` be an invertible `𝒪_Y`-module
and `s` a regular meromorphic section of it, and let `Z ⊆ X` be a prime divisor whose generic
point maps to the **generic point of `Y`**.  Then

`ord_{Z, f^*ℒ}(f^*s) = 0`,

with `f^*s` the pullback of Stacks 0ENC, part (1) and the order of vanishing read at the
canonical ratio of Stacks 0EPR.

The chart data is the same as for
`AlgebraicGeometry.Space.orderOfVanishingSection_pullbackMeromorphicSection_eq_length_mul`: a
diagram `d` of affine étale charts over `f` with `ℒ` free over the chart of `Y` on `eM` and
`f^*ℒ` free over the chart of `X` on `eL`, whose value at the identity chart is the image of
that of `eM`, and a point `u` of the chart scheme of `X` over the generic point of `Z`. -/
theorem orderOfVanishingSection_pullbackMeromorphicSection_eq_zero_of_eq_genericPoint
    (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) (ZX : PrimeDivisor B S hS X.1)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (hL : IsInvertibleModule Y L)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (eM : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → L.val.obj (op W))
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (eL : (W : SmallEtale B S hS X.1) → (W ⟶ d.U) →
      ((modulePullback B S hS f).obj L).val.obj (op W))
    (hLcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ d.U) (g : W' ⟶ W),
      (((modulePullback B S hS f).obj L).val.map g.op).hom (eL W k) = eL W' (g ≫ k))
    (hLfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ d.U),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eL W k)
    (heq : eL d.U (𝟙 d.U) = (modulePullbackChartFMap B S hS f L).app d (eM d.V (𝟙 d.V)))
    (u : chartScheme d.U)
    (hu : chartSchemeToPoints B S hS X.1 d.U u = ZX.genericPoint B S hS X.1)
    (hgen : pointsMap B S hS X.1 f.hom (ZX.genericPoint B S hS X.1) =
      genericPoint B S hS Y.2 hYint)
    [IsNoetherianRing ((chartScheme d.U).presheaf.stalk u)]
    [Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u)] :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    orderOfVanishingSection.{u, u} B S hS X.2 hXdec ZX
        ((modulePullback B S hS f).obj L)
        (pullbackMeromorphicSection B S hS f L
          (pullbacksMeromorphicSections_of_flat B S hS f.hom hf) s)
        (ZX.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS f).obj L)
          (modulePullbackInvertible f L hL) hXint hXN) = 0 := by
  have : ∀ W : PrimeDivisor B S hS X.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have hwaX := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS X.2 hXint
  have hfinX := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hXN
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  have hfm := pullbacksMeromorphicSections_of_flat B S hS f.hom hf
  have hσ := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS f hfm L hL s hs
  have hv : chartSchemeToPoints B S hS Y.1 d.V
      (((BigFppfOver.toScheme B S hS).map d.g).base u) = genericPoint B S hS Y.2 hYint := by
    rw [chartSchemeToPoints_chartDiagram B S hS f d u, hu]
    exact hgen
  obtain ⟨r, hr, hrr⟩ := exists_isUnit_chartPointMeromorphicMap_chartRatio_of_eq_genericPoint
    B S hS Y hYint hwaY hfinY L d.V hV eM hMcompat hMfree s hs _ hv
  have hratio := chartRatio_pullbackMeromorphicSection_chartDiagram B S hS f hfm L d eM
    hMcompat hMfree eL hLcompat hLfree heq s
  have hread := chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_isFlat B S hS f hf
    hfm d hU hV (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU)
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV) u
    (chartRatio B S hS Y.1 Y.2 L d.V eM hMcompat hMfree s)
  have hcr : chartPointMeromorphicMap B S hS X d.U hU
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU) u
        (chartRatio B S hS X.1 X.2 ((modulePullback B S hS f).obj L) d.U eL hLcompat hLfree
          (pullbackMeromorphicSection B S hS f L hfm s)) =
      algebraMap ((chartScheme d.U).presheaf.stalk u)
        (FractionRing ((chartScheme d.U).presheaf.stalk u))
        ((((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom r) := by
    rw [hratio, ← hread, hrr]
    exact IsLocalization.map_eq _ _
  exact ZX.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit B S hS hXdec hXint hXN
    hwaX hfinX ((modulePullback B S hS f).obj L) (modulePullbackInvertible f L hL) _ hσ
    d.U hU eL hLcompat hLfree u hu
    (hr.map (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom) hcr

end AlgebraicGeometry.Space

end
