module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Defs
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The order of vanishing of a meromorphic section along a flat morphism, read on one chart

Let `f : X ⟶ Y` be a **flat** morphism of decent, locally Noetherian, integral algebraic spaces
over a scheme `S`, let `ℒ` be an invertible `𝒪_Y`-module and `s` a regular meromorphic section of
it, let `Z' ⊆ Y` and `Z ⊆ X` be prime divisors with the generic point `ξ` of `Z` over the generic
point `ξ'` of `Z'`.  This file proves

`ord_{Z, f^*ℒ}(f^*s) = m · ord_{Z', ℒ}(s)`,

with `f^*s` the pullback of Stacks 0ENC, part (1)
(`AlgebraicGeometry.Space.pullbackMeromorphicSection`), both orders of vanishing read at the
canonical ratios of Stacks 0EPR, and `m` the colength

`m = length_{𝒪_{U, u}}(𝒪_{U, u} / 𝔪_{V, v} 𝒪_{U, u})`

of the extended maximal ideal along a diagram of affine étale charts `U` of `X` over `V` of `Y`,
with `u` over `ξ` and `v = g(u)` over `ξ'`.  This is the identity of Stacks 0EQQ at a single
prime divisor, with the multiplicity read on a chart stalk.

## Main results

* `Ring.ordTotalFracInt_map_of_flatHom`: for a flat local homomorphism `φ : A ⟶ A'` of
  one-dimensional Noetherian local rings and a unit `x` of `Q(A)`,
  `ord_{A'}(φ x) = length_{A'}(A'/𝔪_A A') · ord_A(x)` (Stacks 02M1).
* `AlgebraicGeometry.Space.chartRatio_pullbackMeromorphicSection_chartDiagram`: the chart ratio
  of a pulled-back meromorphic section, over an arbitrary diagram of étale charts.
* `AlgebraicGeometry.Space.chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_isFlat`:
  the germ square for the chart pullback of meromorphic functions along a flat morphism.
* `AlgebraicGeometry.Space.orderOfVanishingSection_pullbackMeromorphicSection_eq_length_mul`:
  the identity above.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

/-! ### The order of vanishing of a unit along a flat local homomorphism -/

namespace Ring

/-- Along a flat ring homomorphism `φ : A →+* A'` the nonzerodivisors of `A` are carried into
the nonzerodivisors of `A'`: `A⁰ ≤ A'⁰.comap φ`. -/
@[ega "IV 20.6.9" "partial"]
theorem nonZeroDivisors_le_comap_of_flatHom {A A' : Type*} [CommRing A] [CommRing A']
    {φ : A →+* A'} (hflat : φ.Flat) : A⁰ ≤ Submonoid.comap φ A'⁰ :=
  fun _ h => map_mem_nonZeroDivisors_of_flatHom hflat h

/-- **The order of vanishing of a unit of the total ring of fractions multiplies by the colength
of the extended maximal ideal.**  Let `φ : A ⟶ A'` be a flat local homomorphism of Noetherian
local rings of Krull dimension at most one and let the colength of `𝔪_A A'` be the natural
number `m`.  Then for every unit `x` of `Q(A)`,

`ord_{A'}(φ x) = m · ord_A(x)`. -/
theorem ordTotalFracInt_map_of_flatHom {A A' : Type*} [CommRing A] [CommRing A']
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [IsNoetherianRing A'] [IsLocalRing A'] [Ring.KrullDimLE 1 A']
    {Q : Type*} [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    {Q' : Type*} [CommRing Q'] [Algebra A' Q'] [IsFractionRing A' Q']
    {φ : A →+* A'} (hloc : IsLocalHom φ) (hflat : φ.Flat) {m : ℕ}
    (hm : Module.length A' (A' ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) = (m : ℕ∞))
    (x : Q) (hx : IsUnit x) :
    ordTotalFracInt A' (IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
        (nonZeroDivisors_le_comap_of_flatHom hflat) x)
        (hx.map (IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
          (nonZeroDivisors_le_comap_of_flatHom hflat))) =
      (m : ℤ) * ordTotalFracInt A x hx := by
  obtain ⟨a, b, hab'⟩ := Stacks.Chow.exists_regularFractionUnit_div (A := A) (Q := Q) hx.unit
  have hab : IsLocalization.mk' Q (a : A) b = x := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have hmul : hx.unit * Stacks.Chow.regularFractionUnit (Q := Q) b =
        Stacks.Chow.regularFractionUnit a := by
      rw [hab', inv_mul_cancel_right]
    exact ((congrArg Units.val hmul).symm.trans (congrArg (· * _) hx.unit_spec) :)
  have hmap : IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
        (nonZeroDivisors_le_comap_of_flatHom hflat) x =
      IsLocalization.mk' Q' (φ (a : A))
        (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : A'⁰) := by
    rw [← hab, IsLocalization.map_mk']
  rw [ordTotalFracInt_congr A' _ (hmap ▸ hx.map _) hmap,
    ordTotalFracInt_congr A hx (hab ▸ hx) hab.symm,
    ordTotalFracInt_map_mk'_of_flatHom (KA := Q) (KB := Q') hloc hflat hm a b]

end Ring

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The chart ratio of a pulled-back section, over an arbitrary chart diagram -/

/-- **The chart ratio of the pullback of a meromorphic section is the chart pullback of its
chart ratio**, over an arbitrary diagram `d` of étale charts over `f`.  Let `𝒩` be an
`𝒪_Y`-module free over the chart `d.V` of `Y` on a compatible family `eM`, and let `eL` be a
compatible family freely generating `f^*𝒩` over the chart `d.U` of `X` whose value at the
identity chart is the image of the value of `eM` at the identity chart under the chart component
of the unit of Stacks 03D7.  Then for every meromorphic section `t` of `𝒩`,

`(f^*t) / eL = f^♯(t / eM)`

in `𝒦_X(d.U)`. -/
theorem chartRatio_pullbackMeromorphicSection_chartDiagram (f : X ⟶ Y)
    (hfm : PullbacksMeromorphicSections B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (eM : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (eL : (W : SmallEtale B S hS X.1) → (W ⟶ d.U) →
      ((modulePullback B S hS f).obj M).val.obj (op W))
    (hLcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ d.U) (g : W' ⟶ W),
      (((modulePullback B S hS f).obj M).val.map g.op).hom (eL W k) = eL W' (g ≫ k))
    (hLfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ d.U),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eL W k)
    (heq : eL d.U (𝟙 d.U) =
      (modulePullbackChartFMap B S hS f M).app d (eM d.V (𝟙 d.V)))
    (t : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M) :
    chartRatio B S hS X.1 X.2 ((modulePullback B S hS f).obj M) d.U eL hLcompat hLfree
        (pullbackMeromorphicSection B S hS f M hfm t) =
      chartMeromorphicFunctionPullback B S hS f hfm d
        (chartRatio B S hS Y.1 Y.2 M d.V eM hMcompat hMfree t) := by
  refine chartRatio_eq_of_eval_eq B S hS X.1 X.2 ((modulePullback B S hS f).obj M) d.U eL
    hLcompat hLfree (pullbackMeromorphicSection B S hS f M hfm t) _ ?_
  rw [heq]
  refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS f M hfm t d _
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS Y.1 Y.2 M d.V eM
      hMcompat hMfree t)) ?_
  exact congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) d.U)
    (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hfm d _ _)

/-! ### The germ square for the chart pullback of meromorphic functions -/

attribute [local instance] chartMeromorphicFunctionAlgebra

/-- **The reading of a meromorphic function at a chart point, pushed along the stalk map.**  Let
`d` be a diagram of affine étale charts over a flat `f : X ⟶ Y`, with vertical morphism of
schemes `g : d.U → d.V`, and let `u` be a point of the scheme of `d.U`.  Reading a meromorphic
function `c` of `d.V` at `g(u)` and pushing it along the stalk map of `g` gives the same element
of `Q(𝒪_{d.U, u})` as reading the chart pullback of `c` at `u`. -/
theorem chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_isFlat (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) (hfm : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (hKU : IsFractionRing ((structurePresheaf B S hS X.1).obj (op d.U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U)))
    (hKV : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op d.V))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)))
    (u : chartScheme d.U)
    (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) :
    haveI : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
      hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
    IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
        (FractionRing ((chartScheme d.U).presheaf.stalk u))
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom
        (fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ u hx)
        (chartPointMeromorphicMap B S hS Y d.V hV hKV
          (((BigFppfOver.toScheme B S hS).map d.g).base u) c) =
      chartPointMeromorphicMap B S hS X d.U hU hKU u
        (chartMeromorphicFunctionPullback B S hS f hfm d c) := by
  have : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have := hKU
  have := hKV
  set g := (BigFppfOver.toScheme B S hS).map d.g with hg
  let ψ : FractionRing ((chartScheme d.V).presheaf.stalk (g.base u)) →+*
      FractionRing ((chartScheme d.U).presheaf.stalk u) :=
    IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
      (FractionRing ((chartScheme d.U).presheaf.stalk u)) (g.stalkMap u).hom
      (fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ u hx)
  have key : ψ.comp (chartPointMeromorphicMap B S hS Y d.V hV hKV (g.base u)) =
      (chartPointMeromorphicMap B S hS X d.U hU hKU u).comp
        (chartMeromorphicFunctionPullback B S hS f hfm d) := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS Y.1).obj (op d.V))⁰
      (RingHom.ext fun a => ?_)
    have hpull : chartMeromorphicFunctionPullback B S hS f hfm d
          (algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V))
            ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) a) =
        algebraMap ((structurePresheaf B S hS X.1).obj (op d.U))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U))
          (chartDiagramRestrict B S hS f d a) :=
      RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS f hfm d) a
    have h1 := chartPointMeromorphicMap_algebraMap B S hS Y d.V hV hKV (g.base u) a
    have h2 := chartPointMeromorphicMap_algebraMap B S hS X d.U hU hKU u
      (chartDiagramRestrict B S hS f d a)
    have h4 : ψ (algebraMap ((chartScheme d.V).presheaf.stalk (g.base u))
          (FractionRing ((chartScheme d.V).presheaf.stalk (g.base u)))
          (((chartScheme d.V).presheaf.germ ⊤ (g.base u) trivial).hom a)) =
        algebraMap ((chartScheme d.U).presheaf.stalk u)
          (FractionRing ((chartScheme d.U).presheaf.stalk u))
          ((g.stalkMap u).hom
            (((chartScheme d.V).presheaf.germ ⊤ (g.base u) trivial).hom a)) :=
      IsLocalization.map_eq _ _
    refine (congrArg ψ h1).trans (h4.trans (Eq.trans ?_ ((congrArg
      (chartPointMeromorphicMap B S hS X d.U hU hKU u) hpull).trans h2).symm))
    exact congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply g ⊤ u trivial a)
  exact RingHom.congr_fun key c

/-! ### The order of vanishing of a pulled-back section -/

variable (hXdec : IsDecentSpace B S hS X.1) (hYdec : IsDecentSpace B S hS Y.1)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))

include hXdec hYdec hXint hYint hXN hYN in
/-- **The order of vanishing of a meromorphic section pulls back with the multiplicity, on one
chart diagram.**  Let `f : X ⟶ Y` be a flat morphism of decent, locally Noetherian, integral
algebraic spaces over `S`, let `ℒ` be an invertible `𝒪_Y`-module and `s` a regular meromorphic
section of it, and let `Z ⊆ X` and `Z' ⊆ Y` be prime divisors.  Let `d` be a diagram of affine
étale charts over `f`, with `ℒ` free over the chart of `Y` on a compatible family `eM` and
`f^*ℒ` free over the chart of `X` on a compatible family `eL` whose value at the identity chart
is the image of that of `eM`; let `u` be a point of the chart scheme of `X` over the generic
point of `Z` whose image `v` under the vertical morphism of schemes lies over the generic point
of `Z'`.  If the colength of the extended maximal ideal `𝔪_{V, v} 𝒪_{U, u}` is the natural
number `m`, then

`ord_{Z, f^*ℒ}(f^*s) = m · ord_{Z', ℒ}(s)`,

with `f^*s` the pullback of Stacks 0ENC, part (1) and both orders of vanishing read at the
canonical ratios of Stacks 0EPR. -/
theorem orderOfVanishingSection_pullbackMeromorphicSection_eq_length_mul (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom)
    (ZX : PrimeDivisor B S hS X.1) (ZY : PrimeDivisor B S hS Y.1)
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
    (hv : chartSchemeToPoints B S hS Y.1 d.V
        (((BigFppfOver.toScheme B S hS).map d.g).base u) = ZY.genericPoint B S hS Y.1)
    [IsNoetherianRing ((chartScheme d.U).presheaf.stalk u)]
    [Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u)]
    [IsNoetherianRing ((chartScheme d.V).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map d.g).base u))]
    [Ring.KrullDimLE 1 ((chartScheme d.V).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map d.g).base u))]
    {m : ℕ}
    (hm : haveI : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
        hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
      Module.length ((chartScheme d.U).presheaf.stalk u)
        (((chartScheme d.U).presheaf.stalk u) ⧸
          Ideal.map (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom
            (maximalIdeal ((chartScheme d.V).presheaf.stalk
              (((BigFppfOver.toScheme B S hS).map d.g).base u)))) = (m : ℕ∞)) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    orderOfVanishingSection.{u, u} B S hS X.2 hXdec ZX
        ((modulePullback B S hS f).obj L)
        (pullbackMeromorphicSection B S hS f L
          (pullbacksMeromorphicSections_of_flat B S hS f.hom hf) s)
        (ZX.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS f).obj L)
          (modulePullbackInvertible f L hL) hXint hXN) =
      (m : ℤ) * orderOfVanishingSection.{u, u} B S hS Y.2 hYdec ZY L s
        (ZY.canonicalLocalRatio B S hS Y.2 hYdec L hL hYint hYN) := by
  have : ∀ W : PrimeDivisor B S hS X.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have hwaX := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS X.2 hXint
  have hfinX := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hXN
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  have hKX := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX d.U hU
  have hKY := isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV
  have hfm := pullbacksMeromorphicSections_of_flat B S hS f.hom hf
  have hσ := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS f hfm L hL s hs
  have hcY := IsUnit.map
    (chartPointMeromorphicMap B S hS Y d.V hV
      hKY
      (((BigFppfOver.toScheme B S hS).map d.g).base u))
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwaY hfinY L d.V hV eM
      hMcompat hMfree s hs)
  have hcX := IsUnit.map
    (chartPointMeromorphicMap B S hS X d.U hU
      hKX u)
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwaX hfinX
      ((modulePullback B S hS f).obj L) d.U hU eL hLcompat hLfree _ hσ)
  have hratio := chartRatio_pullbackMeromorphicSection_chartDiagram B S hS f hfm L d eM
    hMcompat hMfree eL hLcompat hLfree heq s
  have hread := chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_isFlat B S hS f hf
    hfm d hU hV hKX
    hKY u
    (chartRatio B S hS Y.1 Y.2 L d.V eM hMcompat hMfree s)
  have hcomp : chartPointMeromorphicMap B S hS X d.U hU
        hKX u
        (chartRatio B S hS X.1 X.2 ((modulePullback B S hS f).obj L) d.U eL hLcompat hLfree
          (pullbackMeromorphicSection B S hS f L hfm s)) =
      IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
        (FractionRing ((chartScheme d.U).presheaf.stalk u))
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom
        (fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ u hx)
        (chartPointMeromorphicMap B S hS Y d.V hV
          hKY
          (((BigFppfOver.toScheme B S hS).map d.g).base u)
          (chartRatio B S hS Y.1 Y.2 L d.V eM hMcompat hMfree s)) :=
    (congrArg (chartPointMeromorphicMap B S hS X d.U hU
      hKX u) hratio).trans
      hread.symm
  refine Eq.trans (ZX.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
    B S hS hXdec hXint hXN hwaX hfinX ((modulePullback B S hS f).obj L)
    (modulePullbackInvertible f L hL) _ hσ d.U hU eL hLcompat hLfree u hu hcX) ?_
  refine Eq.trans ?_ (congrArg ((m : ℤ) * ·)
    (ZY.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
      B S hS hYdec hYint hYN hwaY hfinY L hL s hs d.V hV eM hMcompat hMfree _ hv hcY).symm)
  refine Eq.trans (Ring.ordTotalFracInt_congr ((chartScheme d.U).presheaf.stalk u) hcX
    (hcomp ▸ hcX) hcomp) ?_
  exact Ring.ordTotalFracInt_map_of_flatHom (Q := FractionRing ((chartScheme d.V).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map d.g).base u)))
    (Q' := FractionRing ((chartScheme d.U).presheaf.stalk u))
    inferInstance (AlgebraicGeometry.Flat.stalkMap _ u) hm _ hcY

end AlgebraicGeometry.Space

end
