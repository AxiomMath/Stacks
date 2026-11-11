module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingStrictHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkFreeness
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison

/-!
# The order of vanishing along a prime divisor, compared on an arbitrary étale chart

Let `X` be a decent algebraic space, let `Z ⊆ X` be a prime divisor with generic point `ξ`, and
let `(U, u)` be *any* étale scheme chart of `X` with a point `u` above `ξ`. Stacks 0ENM compares
the order of vanishing along `Z` with the order of vanishing at `u` in the sense of Divisors,
Definition 02RJ, and the comparison carried by
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing` does so along the
canonical map `𝒪_{U, u} → 𝒪^h_{X, ξ}` — which exists only when `(U, u)` is an *elementary* étale
neighbourhood of `ξ`, since `𝒪^h_{X, ξ}` is the colimit over those.

A chart that trivializes an invertible module is not an elementary étale neighbourhood of the
point below each of its codimension-one points, and cannot be made one: the residue field map of
an elementary étale neighbourhood at its distinguished point is bijective, by Stacks 0BBP
(`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`), and shrinking to a
pointed open subscheme (`AlgebraicGeometry.Space.openRestrictionNeighborhood`) does not change
the residue field at the marked point, while an étale chart has a nontrivial finite separable
residue extension in general. The comparison on an arbitrary chart therefore has to be routed
the way the source routes it, through the strict henselization at a geometric point `ū` above
`ξ`:

`ord_{𝒪_{U, u}}(f) = ord_{𝒪_{X, ū}}(f) = ord_{𝒪^h_{X, ξ}}(f_ξ)`,

both steps being instances of `IsLocalRing.IsHenselization.ord_algebraMap`, since `𝒪_{X, ū}` is a
strict henselization of `𝒪_{U, u}` (Stacks 04KF) and of `𝒪^h_{X, ξ}` (Stacks 0EMZ) at once. The
two legs are stated separately here and then joined.

## Main results

* `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_mem_nonZeroDivisors` and
  `AlgebraicGeometry.Space.ord_chartLocalRingToEtaleLocalRing`: the canonical map
  `𝒪_{U, u} → 𝒪_{X, ū}` of Stacks 05VP carries nonzerodivisors to nonzerodivisors and leaves
  `Ring.ord` unchanged.
* `AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing`: there is a map
  `𝒪^h_{X, x} → 𝒪_{X, x̄}` carrying nonzerodivisors to nonzerodivisors and leaving `Ring.ord`
  unchanged, for every geometric point `x̄` above `x`.
* `AlgebraicGeometry.Space.functionFieldToEtaleFractionRing`: the induced map
  `R(U) = Q(𝒪_{U, u}) → Q(𝒪_{X, ū})`, the arbitrary-chart analogue of
  `AlgebraicGeometry.Space.PrimeDivisor.functionFieldToTotalFractionRing`.
* `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_comp_stalkMap`,
  `AlgebraicGeometry.Space.chartFunctionFieldMap` and
  `AlgebraicGeometry.Space.functionFieldToEtaleFractionRing_comp_chartFunctionFieldMap`, assembled
  into `AlgebraicGeometry.Space.functionFieldToEtaleFractionRing_chartFunctionFieldMap_stalkMap`:
  **that reading is natural in the chart.** The canonical map of Stacks 05VP is compatible with a
  morphism of charts of `X`, and so therefore is the reading of a rational function in
  `Q(𝒪_{X, ū})`; a comparison of two readings of one meromorphic section made over a *common*
  chart can therefore be pushed into `Q(𝒪_{X, ū})` along both legs.
* `AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap`: a
  rational function of the chart whose image in `Q(𝒪_{X, ū})` is a unit of `𝒪_{X, ū}` has order
  of vanishing zero at the chart point — the input of algebraic Hartogs.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_mk'_eq_ord_mk'_chart`: **the comparison of orders of
  vanishing at an arbitrary étale chart**, a variant of the comparison step of Stacks 0ENM (the
  lemma itself is `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_schematicLocus`). The order of
  vanishing along `Z` of a fraction of nonzerodivisors of `𝒪^h_{X, ξ}` is the order of vanishing at
  `u` of a fraction of nonzerodivisors of `𝒪_{U, u}`, as soon as numerator and denominator have the
  same images in `𝒪_{X, ū}`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingToEtaleFractionRing` and
  `AlgebraicGeometry.Space.PrimeDivisor.ord_chart_eq_zero_of_isUnit_of_etaleFractionRing_eq`: the
  induced map `Q(𝒪^h_{X, ξ}) → Q(𝒪_{X, ū})`, and the unit hypothesis of Stacks 0EPX read on a
  chart — a rational function of the chart with the same image in `Q(𝒪_{X, ū})` as a unit of
  `𝒪^h_{X, ξ}` has order of vanishing zero at the chart point.

## Implementation notes

The comparison is stated at the level of *ring elements* — two nonzerodivisors of `𝒪^h_{X, ξ}`
and two of `𝒪_{U, u}` with matching images in `𝒪_{X, ū}` — and not at the level of the induced
maps on total rings of fractions. Two reasons. First, `Ring.ord` is defined for any ring, so this
form needs no Noetherianness and no dimension bound on `𝒪_{X, ū}`, whereas evaluating an order of
vanishing on `Q(𝒪_{X, ū})` would need both. Second, the map `𝒪^h_{X, ξ} → 𝒪_{X, ū}` is not a
closed term of this development: Stacks 0EMZ produces it, pinned by lying over a neighbourhood
stalk, and `AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing` is the form in which a
consumer receives it. The hypothesis of the comparison is therefore `hψ`, that the given map
leaves `Ring.ord` unchanged, which is exactly what that producer supplies.

`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing` is *not* re-derived
from the comparison here. It could be, but only through the identification of the algebra
structure that Stacks 0EMZ produces on `𝒪_{X, ū}` over the stalk of the elementary étale
neighbourhood with the canonical map of Stacks 05VP; the stalk is taken at
`AlgebraicGeometry.Space.chartPoint` of the small étale neighbourhood the elementary one
determines, which is the distinguished point only up to the propositional equality
`AlgebraicGeometry.Space.chartPoint_smallEtaleNeighborhood`, so the identification is a transport
between two spellings of one stalk rather than an equation. The two statements are left
independent.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

include hX

/-! ### The leg from a scheme chart to the étale local ring -/

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP carries nonzerodivisors to
nonzerodivisors: it is the structure map of a strict henselization, which is flat. -/
theorem chartLocalRingToEtaleLocalRing_mem_nonZeroDivisors {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {r : ↥(chartLocalRing B S hS X V)}
    (hr : r ∈ (↥(chartLocalRing B S hS X V))⁰) :
    chartLocalRingToEtaleLocalRing B S hS X hX V r ∈
      ((etaleLocalRing B S hS X x : Type (u + 1)))⁰ := by
  let : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  let : Algebra ↥(chartLocalRing B S hS X V)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  let := isHenselization_chartLocalRingToEtaleLocalRing B S hS X hX V
  exact IsHenselization.algebraMap_mem_nonZeroDivisors
    (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
      (chartGeometricPoint V).residueField) hr

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP leaves the length of the quotient by
a principal ideal unchanged: it is the structure map of a strict henselization, which is flat and
local with the maximal ideal extended. -/
theorem ord_chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (r : ↥(chartLocalRing B S hS X V)) :
    Ring.ord (etaleLocalRing B S hS X x : Type (u + 1))
        (chartLocalRingToEtaleLocalRing B S hS X hX V r) =
      Ring.ord ↥(chartLocalRing B S hS X V) r := by
  let : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  let : Algebra ↥(chartLocalRing B S hS X V)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  let := isHenselization_chartLocalRingToEtaleLocalRing B S hS X hX V
  exact IsHenselization.ord_algebraMap
    (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
      (chartGeometricPoint V).residueField) r

/-! ### The leg from the henselian local ring to the étale local ring -/

/-- **The order of vanishing is read off the étale local ring at a geometric point above the
point.** For a decent algebraic space `X`, a point `x` with an elementary étale neighbourhood,
and a geometric point `x̄` above `x`, there is a ring map `𝒪^h_{X, x} → 𝒪_{X, x̄}` carrying
nonzerodivisors to nonzerodivisors and leaving `Ring.ord` unchanged.

The map is the structure map of Stacks 0EMZ, for which `𝒪_{X, x̄}` is a strict henselization of
`𝒪^h_{X, x}`; the two conclusions are then
`IsLocalRing.IsHenselization.algebraMap_mem_nonZeroDivisors` and
`IsLocalRing.IsHenselization.ord_algebraMap`. The chosen separable algebraic closure of the
residue field of the neighbourhood stalk is the absolute one, `SeparableClosure`. -/
theorem exists_ringHom_ord_henselianLocalRing (hdec : IsDecentSpace B S hS X)
    {x : points B S hS X} (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (xbar : GeometricPoint B S hS X) (hxbar : xbar.LiesOver x) :
    ∃ ψ : (henselianLocalRing B S hS X hX x hdec : Type (u + 1)) →+*
        (etaleLocalRing B S hS X xbar : Type (u + 1)),
      (∀ r ∈ ((henselianLocalRing B S hS X hX x hdec : Type (u + 1)))⁰,
          ψ r ∈ ((etaleLocalRing B S hS X xbar : Type (u + 1)))⁰) ∧
        ∀ r, Ring.ord (etaleLocalRing B S hS X xbar : Type (u + 1)) (ψ r) =
          Ring.ord (henselianLocalRing B S hS X hX x hdec : Type (u + 1)) r := by
  let : IsLocalRing (henselianLocalRing B S hS X hX x hdec : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX x hdec
  let : IsLocalRing (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX xbar
  obtain ⟨-, alg, algRes, -, -, hSH⟩ := exists_isHenselization_etaleLocalRing B S hS X hX x hdec
    U xbar hxbar
    (SeparableClosure (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u)))
  let := alg
  let := algRes
  let := hSH
  exact ⟨algebraMap _ _,
    fun _ hr => IsHenselization.algebraMap_mem_nonZeroDivisors
      (SeparableClosure (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))) hr,
    fun r => IsHenselization.ord_algebraMap
      (SeparableClosure (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))) r⟩

/-! ### The rational functions of a chart inside the fractions of the étale local ring -/

/-- The map from the function field of an integral étale scheme chart of `X` to the total ring of
fractions of the étale local ring of `X` at a geometric point lying under the chart point,
induced by the canonical map of Stacks 05VP.

This is the comparison the proof of Stacks 0EPX reads a rational function of a trivializing
chart through; it is the arbitrary-chart analogue of
`AlgebraicGeometry.Space.PrimeDivisor.functionFieldToTotalFractionRing`, whose target is the
total ring of fractions of the henselian local ring and which is available only on an elementary
étale neighbourhood of the generic point. -/
def functionFieldToEtaleFractionRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) [AlgebraicGeometry.IsIntegral (chartScheme V.chart)] :
    ↥(chartScheme V.chart).functionField →+*
      FractionRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
  IsLocalization.map (T := ((etaleLocalRing B S hS X x : Type (u + 1)))⁰) _
    (chartLocalRingToEtaleLocalRing B S hS X hX V)
    fun _ hr => chartLocalRingToEtaleLocalRing_mem_nonZeroDivisors B S hS X hX V hr

/-- The induced map on fractions sends the image of `c` to the image of its image. -/
theorem functionFieldToEtaleFractionRing_algebraMap {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    (c : ↥(chartLocalRing B S hS X V)) :
    functionFieldToEtaleFractionRing B S hS X hX V
        (algebraMap ↥(chartLocalRing B S hS X V) ↥(chartScheme V.chart).functionField c) =
      algebraMap (etaleLocalRing B S hS X x : Type (u + 1))
        (FractionRing (etaleLocalRing B S hS X x : Type (u + 1)))
        (chartLocalRingToEtaleLocalRing B S hS X hX V c) :=
  IsLocalization.map_eq ..

/-- The induced map on fractions sends `c / d` to the fraction of the images of `c` and `d`. -/
theorem functionFieldToEtaleFractionRing_mk' {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    (c : ↥(chartLocalRing B S hS X V)) (d : (↥(chartLocalRing B S hS X V))⁰) :
    functionFieldToEtaleFractionRing B S hS X hX V
        (IsLocalization.mk' (chartScheme V.chart).functionField c d) =
      IsLocalization.mk' (FractionRing (etaleLocalRing B S hS X x : Type (u + 1)))
        (chartLocalRingToEtaleLocalRing B S hS X hX V c)
        ⟨chartLocalRingToEtaleLocalRing B S hS X hX V (d : ↥(chartLocalRing B S hS X V)),
          chartLocalRingToEtaleLocalRing_mem_nonZeroDivisors B S hS X hX V d.2⟩ :=
  IsLocalization.map_mk' ..

/-! ### Naturality of the comparison in the chart -/

/-- **The canonical map of Stacks 05VP is natural in the chart.** Let `x̄` be a geometric point of
`X`, let `(U, u)` be a small étale neighbourhood of `x̄`, let `W` be any étale chart of `X` and let
`g : U ⟶ W` be a morphism of charts of `X`. Then the two maps `𝒪_{W, w} → 𝒪_{X, x̄}` agree: the
stalk map of `g` followed by the comparison at `(U, u)`, and the comparison at `W` carrying the
lift of `x̄` that `g` induces.

This is the commuting square of local rings of Stacks 05VU
(`AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing`) at the identity
of `X`, where the homomorphism of étale local rings of Stacks 04NG is the identity
(`AlgebraicGeometry.Space.etaleLocalRingMap_id`).

The second neighbourhood is `AlgebraicGeometry.Space.targetNeighborhood`, whose point is the
image of `u` on the nose, rather than an arbitrary small étale neighbourhood with a morphism to
it: the local ring of a neighbourhood depends on its chosen lift, so a neighbourhood merely
*isomorphic* to this one over `W` carries a different spelling of the same local ring. -/
theorem chartLocalRingToEtaleLocalRing_comp_stalkMap {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : SmallEtale B S hS X)
    (g : V.chart.obj.left ⟶ W.obj.left)
    (hcomm : V.chart.obj.hom ≫ 𝟙 X = yoneda.map g ≫ W.obj.hom) :
    (chartLocalRingToEtaleLocalRing B S hS X hX V).comp
        (((BigFppfOver.toScheme B S hS).map g).stalkMap (chartPoint B S hS X V)).hom =
      chartLocalRingToEtaleLocalRing B S hS X hX (targetNeighborhood B S hS V W g hcomm) := by
  refine Eq.trans (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS
    (𝟙 (⟨X, hX⟩ : AlgebraicSpaces B S hS)) x V W g hcomm) ?_
  exact congrArg (fun φ : (etaleLocalRing B S hS X x : Type (u + 1)) →+*
      (etaleLocalRing B S hS X x : Type (u + 1)) ↦
    φ.comp (chartLocalRingToEtaleLocalRing B S hS X hX
      (targetNeighborhood B S hS V W g hcomm))) (etaleLocalRingMap_id B S hS hX x)

/-- The map on function fields of two integral étale charts of `X` induced by a map of their
local rings carrying nonzerodivisors to nonzerodivisors — in particular by the stalk map of a
morphism of charts, which `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_comp_stalkMap`
identifies over `𝒪_{X, x̄}`.

The hypothesis `hψ₀` is a hypothesis rather than a conclusion for the reason given on
`AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingToEtaleFractionRing`: the map is
received from a producer which supplies that property with it. -/
def chartFunctionFieldMap {x : GeometricPoint B S hS X} (V V' : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [AlgebraicGeometry.IsIntegral (chartScheme V'.chart)]
    (ψ : ↥(chartLocalRing B S hS X V) →+* ↥(chartLocalRing B S hS X V'))
    (hψ₀ : ∀ r ∈ (↥(chartLocalRing B S hS X V))⁰, ψ r ∈ (↥(chartLocalRing B S hS X V'))⁰) :
    ↥(chartScheme V.chart).functionField →+* ↥(chartScheme V'.chart).functionField :=
  IsLocalization.map (T := (↥(chartLocalRing B S hS X V'))⁰) _ ψ fun r hr => hψ₀ r hr

omit hX in
/-- The induced map on function fields sends the image of `c` to the image of `ψ c`. -/
theorem chartFunctionFieldMap_algebraMap {x : GeometricPoint B S hS X}
    (V V' : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [AlgebraicGeometry.IsIntegral (chartScheme V'.chart)]
    (ψ : ↥(chartLocalRing B S hS X V) →+* ↥(chartLocalRing B S hS X V'))
    (hψ₀ : ∀ r ∈ (↥(chartLocalRing B S hS X V))⁰, ψ r ∈ (↥(chartLocalRing B S hS X V'))⁰)
    (c : ↥(chartLocalRing B S hS X V)) :
    chartFunctionFieldMap B S hS X V V' ψ hψ₀
        (algebraMap ↥(chartLocalRing B S hS X V) ↥(chartScheme V.chart).functionField c) =
      algebraMap ↥(chartLocalRing B S hS X V') ↥(chartScheme V'.chart).functionField (ψ c) :=
  IsLocalization.map_eq ..

/-- **The reading of a rational function of a chart in `Q(𝒪_{X, x̄})` is natural in the chart.**
If `ψ : 𝒪_{U, u} → 𝒪_{U', u'}` carries nonzerodivisors to nonzerodivisors and is compatible with
the two canonical maps of Stacks 05VP into `𝒪_{X, x̄}`, then reading a rational function of `U`
through `U'` gives the same element of `Q(𝒪_{X, x̄})` as reading it through `U` directly.

With `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_comp_stalkMap` for `hψ` this is the
compatibility of
`AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap` with a
refinement of the chart, which is what lets a comparison of two readings of one meromorphic
section made over a *common* chart be pushed into `Q(𝒪_{X, x̄})` along both legs.

Both sides are ring homomorphisms out of the total ring of fractions of `𝒪_{U, u}`, so they are
determined by their restriction to `𝒪_{U, u}` itself, where both are the structure map of
`Q(𝒪_{X, x̄})` after the canonical map at `(U, u)`. -/
theorem functionFieldToEtaleFractionRing_comp_chartFunctionFieldMap
    {x : GeometricPoint B S hS X} (V V' : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [AlgebraicGeometry.IsIntegral (chartScheme V'.chart)]
    (ψ : ↥(chartLocalRing B S hS X V) →+* ↥(chartLocalRing B S hS X V'))
    (hψ₀ : ∀ r ∈ (↥(chartLocalRing B S hS X V))⁰, ψ r ∈ (↥(chartLocalRing B S hS X V'))⁰)
    (hψ : (chartLocalRingToEtaleLocalRing B S hS X hX V').comp ψ =
      chartLocalRingToEtaleLocalRing B S hS X hX V) :
    (functionFieldToEtaleFractionRing B S hS X hX V').comp
        (chartFunctionFieldMap B S hS X V V' ψ hψ₀) =
      functionFieldToEtaleFractionRing B S hS X hX V := by
  refine IsLocalization.ringHom_ext (↥(chartLocalRing B S hS X V))⁰ (RingHom.ext fun c => ?_)
  change functionFieldToEtaleFractionRing B S hS X hX V'
      (chartFunctionFieldMap B S hS X V V' ψ hψ₀
        (algebraMap ↥(chartLocalRing B S hS X V) ↥(chartScheme V.chart).functionField c)) =
    functionFieldToEtaleFractionRing B S hS X hX V
      (algebraMap ↥(chartLocalRing B S hS X V) ↥(chartScheme V.chart).functionField c)
  rw [chartFunctionFieldMap_algebraMap, functionFieldToEtaleFractionRing_algebraMap,
    functionFieldToEtaleFractionRing_algebraMap]
  exact congrArg (algebraMap (etaleLocalRing B S hS X x : Type (u + 1))
    (FractionRing (etaleLocalRing B S hS X x : Type (u + 1)))) (RingHom.congr_fun hψ c)

/-- **The reading of a rational function of a chart in `Q(𝒪_{X, x̄})` is unchanged by refining
the chart**, in the form a consumer uses: a rational function of an étale chart `W` of `X` read
through a small étale neighbourhood `(U, u)` of `x̄` lying over `W` gives the same element of
`Q(𝒪_{X, x̄})` as reading it at `W` with the lift of `x̄` that the morphism induces.

This is
`AlgebraicGeometry.Space.functionFieldToEtaleFractionRing_comp_chartFunctionFieldMap` with its
hypothesis `hψ` discharged by
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_comp_stalkMap`.

Integrality of the coarse chart is asked for at the spelling
`(targetNeighborhood B S hS V W g hcomm).chart` and not at `W`, although the two are the same
chart definitionally: instance search does not unfold
`AlgebraicGeometry.Space.targetNeighborhood`, and stating it at `W` makes elaboration of this
statement exhaust its heartbeats rather than fail cleanly. A consumer holding
`IsIntegral (chartScheme W)` supplies it with `inferInstanceAs`. -/
theorem functionFieldToEtaleFractionRing_chartFunctionFieldMap_stalkMap
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x) (W : SmallEtale B S hS X)
    (g : V.chart.obj.left ⟶ W.obj.left)
    (hcomm : V.chart.obj.hom ≫ 𝟙 X = yoneda.map g ≫ W.obj.hom)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [AlgebraicGeometry.IsIntegral (chartScheme (targetNeighborhood B S hS V W g hcomm).chart)]
    (hψ₀ : ∀ r ∈ (↥(chartLocalRing B S hS X (targetNeighborhood B S hS V W g hcomm)))⁰,
      ((BigFppfOver.toScheme B S hS).map g).stalkMap (chartPoint B S hS X V) r ∈
        (↥(chartLocalRing B S hS X V))⁰)
    (f : ↥(chartScheme (targetNeighborhood B S hS V W g hcomm).chart).functionField) :
    functionFieldToEtaleFractionRing B S hS X hX V
        (chartFunctionFieldMap B S hS X (targetNeighborhood B S hS V W g hcomm) V
          (((BigFppfOver.toScheme B S hS).map g).stalkMap (chartPoint B S hS X V)).hom hψ₀ f) =
      functionFieldToEtaleFractionRing B S hS X hX
        (targetNeighborhood B S hS V W g hcomm) f :=
  RingHom.congr_fun (functionFieldToEtaleFractionRing_comp_chartFunctionFieldMap B S hS X hX
    (targetNeighborhood B S hS V W g hcomm) V _ hψ₀
    (chartLocalRingToEtaleLocalRing_comp_stalkMap B S hS X hX V W g hcomm)) f

/-! ### The order of vanishing of a rational function with unit image -/

/-- **A rational function of a chart whose image at a geometric point is a unit of the étale
local ring has order of vanishing zero at the chart point.** This is the step of the proof of
Stacks 0EPX that converts the unit hypothesis at the generic point of a prime divisor into the
input of algebraic Hartogs on the trivializing chart.

No Noetherianness and no dimension bound on `𝒪_{X, x̄}` are needed: both sides are read as a
difference of two `Ring.ord`s of `𝒪_{U, u}`, those are carried to `𝒪_{X, x̄}` unchanged by
`AlgebraicGeometry.Space.ord_chartLocalRingToEtaleLocalRing`, and there the numerator differs
from the denominator by the unit `w`, which `Ring.ord_mul_of_isUnit_left` discards. -/
theorem ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [IsLocallyNoetherian (chartScheme V.chart)]
    (hcoh : coheight (chartPoint B S hS X V) = 1)
    (f : ↥(chartScheme V.chart).functionField) (hf : f ≠ 0)
    {w : (etaleLocalRing B S hS X x : Type (u + 1))} (hw : IsUnit w)
    (hfw : functionFieldToEtaleFractionRing B S hS X hX V f =
      algebraMap (etaleLocalRing B S hS X x : Type (u + 1))
        (FractionRing (etaleLocalRing B S hS X x : Type (u + 1))) w) :
    (chartScheme V.chart).ord f (chartPoint B S hS X V) = 0 := by
  obtain ⟨⟨c, d⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors ↥(chartLocalRing B S hS X V)) f
  have hc : c ∈ (↥(chartLocalRing B S hS X V))⁰ :=
    mem_nonZeroDivisors_of_ne_zero fun h => hf (by simp [h])
  rw [functionFieldToEtaleFractionRing_mk'] at hfw
  have hmul : chartLocalRingToEtaleLocalRing B S hS X hX V c =
      w * chartLocalRingToEtaleLocalRing B S hS X hX V (d : ↥(chartLocalRing B S hS X V)) := by
    refine IsFractionRing.injective (etaleLocalRing B S hS X x : Type (u + 1))
      (FractionRing (etaleLocalRing B S hS X x : Type (u + 1))) ?_
    rw [map_mul, ← hfw]
    exact (IsLocalization.mk'_spec _ _ _).symm
  have hord : Ring.ord ↥(chartLocalRing B S hS X V) c =
      Ring.ord ↥(chartLocalRing B S hS X V) (d : ↥(chartLocalRing B S hS X V)) := by
    rw [← ord_chartLocalRingToEtaleLocalRing B S hS X hX V c,
      ← ord_chartLocalRingToEtaleLocalRing B S hS X hX V (d : ↥(chartLocalRing B S hS X V)),
      hmul, Ring.ord_mul_of_isUnit_left hw]
  rw [Scheme.ord_mk' hcoh ⟨c, hc⟩ d, hord]
  exact sub_self _

/-! ### The two orders of vanishing, compared on an arbitrary étale chart -/

variable (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- **The comparison of orders of vanishing at an arbitrary étale chart.** This is a variant of the
comparison step of the proof of Stacks 0ENM, not that lemma, which is
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_schematicLocus`. Let `Z` be a prime divisor of a
decent algebraic space `X` with generic point `ξ`, let `x̄` be a geometric point of `X`, and let
`(U, u)` be a small étale neighbourhood of `x̄` whose scheme is integral and locally Noetherian and
whose point has codimension one. Let `a / b` be a fraction of nonzerodivisors of `𝒪^h_{X, ξ}` and
`c / d` one of nonzerodivisors of `𝒪_{U, u}` whose numerators and denominators agree in `𝒪_{X, x̄}`,
along a map `ψ : 𝒪^h_{X, ξ} → 𝒪_{X, x̄}` leaving `Ring.ord` unchanged and the canonical map of
Stacks 05VP. Then the order of vanishing of `a / b` along `Z` is the order of vanishing of `c / d`
at `u` in the sense of Divisors, Definition 02RJ.

Both sides are a difference of two `Ring.ord`s, by
`AlgebraicGeometry.Space.PrimeDivisor.ord_mk'` and `AlgebraicGeometry.Scheme.ord_mk'`, and the
four `Ring.ord`s are pairwise equal: the canonical map of Stacks 05VP is the structure map of a
strict henselization, so it leaves `Ring.ord` unchanged
(`AlgebraicGeometry.Space.ord_chartLocalRingToEtaleLocalRing`), and `hψ` says the same of `ψ`.

The hypothesis `hψ` is supplied by
`AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing` at any geometric point above `ξ`;
unlike the elementary-neighbourhood comparison
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`, nothing here asks
that `(U, u)` be an elementary étale neighbourhood of `ξ`, which is what makes the statement
usable on a chart chosen for a different reason — in the proof of Stacks 0EPX, one trivializing
an invertible module. -/
theorem PrimeDivisor.ord_mk'_eq_ord_mk'_chart
    [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    {xbar : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood xbar)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [IsLocallyNoetherian (chartScheme V.chart)]
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hψ : ∀ r, Ring.ord (etaleLocalRing B S hS X xbar : Type (u + 1)) (ψ r) =
      Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec) r)
    (hcoh : coheight (chartPoint B S hS X V) = 1)
    (a b : (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰)
    (c d : (↥(chartLocalRing B S hS X V))⁰)
    (hac : ψ (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      chartLocalRingToEtaleLocalRing B S hS X hX V (c : ↥(chartLocalRing B S hS X V)))
    (hbd : ψ (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      chartLocalRingToEtaleLocalRing B S hS X hX V (d : ↥(chartLocalRing B S hS X V)))
    (hu : IsUnit (IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
      (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b)) :
    Z.ord B S hS hX hdec (IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b) hu =
      (chartScheme V.chart).ord
        (IsLocalization.mk' (chartScheme V.chart).functionField
          (c : ↥(chartLocalRing B S hS X V)) d) (chartPoint B S hS X V) := by
  have hca := (hψ (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).symm.trans
    ((congrArg (Ring.ord (etaleLocalRing B S hS X xbar : Type (u + 1))) hac).trans
      (ord_chartLocalRingToEtaleLocalRing B S hS X hX V _))
  have hdb := (hψ (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).symm.trans
    ((congrArg (Ring.ord (etaleLocalRing B S hS X xbar : Type (u + 1))) hbd).trans
      (ord_chartLocalRingToEtaleLocalRing B S hS X hX V _))
  rw [Z.ord_mk' B S hS hX hdec a b hu, Scheme.ord_mk' hcoh c d, hca, hdb]

/-! ### The unit hypothesis of Stacks 0EPX, read on a chart -/

variable {xbar : GeometricPoint B S hS X}

/-- The map `Q(𝒪^h_{X, ξ}) → Q(𝒪_{X, x̄})` induced by a map `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` carrying
nonzerodivisors to nonzerodivisors — in particular by the structure map of Stacks 0EMZ, which
`AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing` supplies together with that
property. -/
def PrimeDivisor.genericTotalFractionRingToEtaleFractionRing
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hψ₀ : ∀ r ∈ (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰,
      ψ r ∈ ((etaleLocalRing B S hS X xbar : Type (u + 1)))⁰) :
    Z.genericTotalFractionRing B S hS hX hdec →+*
      FractionRing (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
  IsLocalization.map (T := ((etaleLocalRing B S hS X xbar : Type (u + 1)))⁰) _ ψ
    fun r hr => hψ₀ r hr

/-- The induced map on fractions sends the image of `v` to the image of `ψ v`. -/
theorem PrimeDivisor.genericTotalFractionRingToEtaleFractionRing_algebraMap
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hψ₀ : ∀ r ∈ (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰,
      ψ r ∈ ((etaleLocalRing B S hS X xbar : Type (u + 1)))⁰)
    (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :
    Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec ψ hψ₀
        (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec) v) =
      algebraMap (etaleLocalRing B S hS X xbar : Type (u + 1))
        (FractionRing (etaleLocalRing B S hS X xbar : Type (u + 1))) (ψ v) :=
  IsLocalization.map_eq ..

/-- **The unit hypothesis of Stacks 0EPX forces order of vanishing zero on a chart.** If a
rational function `f` of an integral locally Noetherian étale chart has, in `Q(𝒪_{X, x̄})`, the
same image as the image of a *unit* of `𝒪^h_{X, ξ}` under the structure map of Stacks 0EMZ, then
`f` has order of vanishing zero at the chart point.

This is the composite of
`AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap` with the
computation of the induced map on fractions: a unit of `𝒪^h_{X, ξ}` has unit image in
`𝒪_{X, x̄}`. The hypothesis `hfv` is exactly the identification of the two ratios of a regular
meromorphic section — the one against a generator of `ℒ` over the chart and the one against the
generator at the generic point, `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio` —
which the proof of Stacks 0EPX makes by observing that the two generators differ by a unit of
`𝒪_{X, x̄}`. -/
theorem PrimeDivisor.ord_chart_eq_zero_of_isUnit_of_etaleFractionRing_eq
    (V : SmallEtaleNeighborhood xbar)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [IsLocallyNoetherian (chartScheme V.chart)]
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hψ₀ : ∀ r ∈ (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰,
      ψ r ∈ ((etaleLocalRing B S hS X xbar : Type (u + 1)))⁰)
    (hcoh : coheight (chartPoint B S hS X V) = 1)
    (f : ↥(chartScheme V.chart).functionField) (hf : f ≠ 0)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hv : IsUnit v)
    (hfv : functionFieldToEtaleFractionRing B S hS X hX V f =
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec ψ hψ₀
        (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec) v)) :
    (chartScheme V.chart).ord f (chartPoint B S hS X V) = 0 :=
  ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap B S hS X hX V hcoh f hf
    (hv.map ψ)
    (hfv.trans
      (Z.genericTotalFractionRingToEtaleFractionRing_algebraMap B S hS X hX hdec ψ hψ₀ v))

end AlgebraicGeometry.Space

end
