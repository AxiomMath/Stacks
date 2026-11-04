module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# The length at a geometric point depends only on the point underneath it

Let `X` be an algebraic space over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module.
The length of `F` at a geometric point `x̄` is
`AlgebraicGeometry.Space.geometricLength`, the length of the stalk `F_{x̄}` over the étale
local ring `𝒪_{X, x̄}`.  This file shows that number is the length of an ordinary Zariski
stalk on an étale scheme chart, and deduces that it does not change when the geometric point
is replaced by another one lying over the same point of `|X|`.

Two inputs make this possible, both already proved in this development.  The first is
Stacks 05VP: the comparison map
`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} → F_{x̄}` is an isomorphism for a quasi-coherent `F`
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`).  Combined with the fact that
the base change along `𝒪_{U, u} → 𝒪_{X, x̄}` preserves lengths
(`AlgebraicGeometry.Space.length_chartStalkTensorEtaleLocalRing`), it gives

`length_{𝒪_{X, x̄}} F_{x̄} = length_{𝒪_{U, u}} (φ^* F)_u`

for every small étale neighbourhood `(U, ū)` of `x̄` whose chart is a scheme.  The right-hand
side mentions the geometric point only through the point `u` of the chart that its chosen
lift sits over.  The second input is that the two sides of a domination of geometric points
share their charts: `AlgebraicGeometry.Space.neighborhoodAlong` turns a neighbourhood of `x̄`
into one of a geometric point dominating it with the *same* chart, and the point of the chart
is unchanged because a morphism of spectra of fields can only send the closed point to the
closed point.  Two geometric points above one point of `|X|` are dominated by a common third
(`AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`), so both of their lengths
are the length at that third one.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiLength` is the length of the Zariski stalk of the
  restriction of `F` to an étale scheme chart, at a point of that chart.  It is
  `AlgebraicGeometry.Space.chartZariskiModuleStalk` with the chart and the point supplied
  separately rather than packaged in a neighbourhood of a geometric point, which is what lets
  two different geometric points be compared on one chart.

## Main results

* `AlgebraicGeometry.Space.geometricLength_eq_chartZariskiLength`: the length of a
  quasi-coherent `F` at a geometric point is the length of the Zariski stalk of `φ^* F` at the
  point of any étale scheme chart under a lift of it.  This is the engine for everything else
  here.
* `AlgebraicGeometry.Space.geometricLength_eq_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.geometricLength_eq_iff_forall_etaleChart`: **Stacks 0EE1,
  conditions (1), (2) and (3).** The length at a geometric point is `d` exactly when it is `d`
  on some, equivalently on every, étale scheme chart neighbourhood.
* `AlgebraicGeometry.Space.geometricLength_eq_of_dominates`: the length is unchanged by
  passing to a geometric point that dominates the given one.
* `AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`: **Stacks 0EE1, independence of
  the geometric point.** Two geometric points lying over the same point of `|X|` give the
  same length, so `AlgebraicGeometry.Space.geometricLength` is a function of the point of
  `|X|`.  This is what makes the definition of Stacks 0EE2 at a point of `|X|` well posed,
  and it subsumes the clause already carried by
  `AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing`, which is the case
  `F = 𝒪_X` on one chart.
* `AlgebraicGeometry.Space.chartPoint_neighborhoodAlong`: the point of the chart is unchanged
  by restriction of a neighbourhood along a domination.

## Implementation notes

The quantification over charts is over the small étale neighbourhoods of the *geometric*
point, that is over pairs consisting of an étale scheme chart and a lift of `x̄` to it, rather
than over pairs `(U, u)` with `u ∈ U` mapping to the image of `x̄` in `|X|` as in Stacks
0EE1(3).  Every lift determines such a pair, so the statement proved here implies
Stacks 0EE1(3) for the pairs that carry a lift; that every pair carries one is Stacks 05VN,
`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale`, and only the direction used
below — a neighbourhood exists at all — is needed for the independence statement, which
quantifies over no chart.

`AlgebraicGeometry.Space.chartZariskiLength` repeats the body of
`AlgebraicGeometry.Space.chartZariskiModuleStalk` with `V.chart` and
`AlgebraicGeometry.Space.chartPoint` replaced by independent arguments; the two agree by
`rfl` (`AlgebraicGeometry.Space.chartZariskiLength_chart_chartPoint`).  Without that
re-indexing the comparison of two geometric points over one chart is an equation between
terms whose types are spelled through two different neighbourhoods, and the transport is
carried by `HEq`.

The module universe is `u` for the two statements that use quasi-coherence, because
Stacks 05VP is available only there; the definition itself is polymorphic.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The length of the Zariski stalk of `φ^* F` at a point `p` of an étale scheme chart `W` of
`X`, over the local ring `𝒪_{W, p}`.

This is `AlgebraicGeometry.Space.chartZariskiModuleStalk` with the chart and the point given
as separate arguments instead of being read off a small étale neighbourhood of a geometric
point; the two agree by
`AlgebraicGeometry.Space.chartZariskiLength_chart_chartPoint`.  It is the quantity named on
the right-hand side of conditions (2) and (3) of Stacks 0EE1, and it mentions no geometric
point. -/
def chartZariskiLength (W : SmallEtale B S hS X) (p : chartScheme W)
    (F : Modules.{u, m} B S hS X hX) : ℕ∞ :=
  Module.length ↥((chartScheme W).presheaf.stalk p)
    ((ModuleCat.restrictScalars
        (Opens.pointFiberStalkIso p (chartScheme W).presheaf).inv.hom).obj
      (Stacks.moduleStalkLarge (Opens.pointGrothendieckTopology p)
        (show Sheaf (Opens.grothendieckTopology (chartScheme W)) CommRingCat.{u} from
          (chartScheme W).sheaf)
        (restrictToChart B S hS hX F W)))

/-- The re-indexed length is the length of
`AlgebraicGeometry.Space.chartZariskiModuleStalk`: the latter is the former at the chart and
the chart point of the neighbourhood. -/
theorem chartZariskiLength_chart_chartPoint {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    chartZariskiLength.{u, m} B S hS hX V.chart (chartPoint B S hS X V) F =
      Module.length ↥(chartLocalRing B S hS X V)
        (chartZariskiModuleStalk.{u, m} B S hS X hX V F) :=
  rfl

/-- **Stacks 0EE1, conditions (1) and (3).** For a quasi-coherent `𝒪_X`-module `F`, the length
of `F` at a geometric point `x̄` is the length of the Zariski stalk of `φ^* F` at the point of
the chart under the chosen lift, for *every* small étale neighbourhood `(U, ū)` of `x̄` whose
chart is a scheme.

Stacks 05VP identifies `F_{x̄}` with `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`), and that base change preserves
lengths (`AlgebraicGeometry.Space.length_chartStalkTensorEtaleLocalRing`). -/
theorem geometricLength_eq_chartZariskiLength {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] :
    geometricLength B S hS ⟨X, hX⟩ x F =
      chartZariskiLength.{u, u} B S hS hX V.chart (chartPoint B S hS X V) F := by
  have : IsIso (chartStalkTensorComparison B S hS hX V F) :=
    isIso_chartStalkTensorComparison B S hS hX V F
  rw [chartZariskiLength_chart_chartPoint B S hS hX V F, geometricLength,
    ← length_chartStalkTensorEtaleLocalRing.{u, u} B S hS X hX V F]
  exact (LinearEquiv.length_eq
    (asIso (chartStalkTensorComparison B S hS hX V F)).toLinearEquiv).symm

/-- **Stacks 0EE1, conditions (1) and (3).** The length of a quasi-coherent `F` at a geometric
point `x̄` is `d` exactly when the length of the Zariski stalk of `φ^* F` is `d` at the point of
the chart under the chosen lift, for *every* small étale neighbourhood of `x̄` whose chart is a
scheme.

Every neighbourhood computes the same length
(`AlgebraicGeometry.Space.geometricLength_eq_chartZariskiLength`), and there is one
(`AlgebraicGeometry.Space.nonempty_smallEtaleNeighborhood`). -/
@[stacks 0EE1 "conditions (1) and (3)"]
theorem geometricLength_eq_iff_forall_etaleChart {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] (d : ℕ∞) :
    geometricLength B S hS ⟨X, hX⟩ x F = d ↔
      ∀ V : SmallEtaleNeighborhood x,
        chartZariskiLength.{u, u} B S hS hX V.chart (chartPoint B S hS X V) F = d := by
  have := nonempty_smallEtaleNeighborhood hX x
  simp only [← geometricLength_eq_chartZariskiLength B S hS hX _ F, forall_const]

/-- **Stacks 0EE1, conditions (1) and (2).** The length of a quasi-coherent `F` at a geometric
point `x̄` is `d` exactly when the length of the Zariski stalk of `φ^* F` is `d` at the point of
the chart under the chosen lift, for *some* small étale neighbourhood of `x̄` whose chart is a
scheme.

Together with `AlgebraicGeometry.Space.geometricLength_eq_iff_forall_etaleChart` this is the
exchange of quantifiers which Stacks 0EE1 asserts: the length agrees on some étale scheme
chart exactly when it agrees on every one. -/
@[stacks 0EE1 "conditions (1) and (2)"]
theorem geometricLength_eq_iff_exists_etaleChart {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] (d : ℕ∞) :
    geometricLength B S hS ⟨X, hX⟩ x F = d ↔
      ∃ V : SmallEtaleNeighborhood x,
        chartZariskiLength.{u, u} B S hS hX V.chart (chartPoint B S hS X V) F = d := by
  have := nonempty_smallEtaleNeighborhood hX x
  simp only [← geometricLength_eq_chartZariskiLength B S hS hX _ F, exists_const]

/-- The point of the chart is unchanged when a small étale neighbourhood of `x̄` is restricted
along a domination of `x̄` by `ȳ`.

The chart is literally the same, and the chosen lift is composed with the morphism of field
spectra witnessing the domination; that morphism sends the closed point to the closed point,
there being only one point in the spectrum of a field. -/
theorem chartPoint_neighborhoodAlong {x y : GeometricPoint B S hS X}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : X.map f.op x.val.value = y.val.value) (V : SmallEtaleNeighborhood x) :
    chartPoint B S hS X ((neighborhoodAlong f hf).obj V) = chartPoint B S hS X V :=
  congrArg ((BigFppfOver.toScheme B S hS).map V.point)
    (Subsingleton.elim (α := PrimeSpectrum x.val.carrier) _ _)

/-- **The length at a geometric point is unchanged by passing to a dominating geometric
point.** If `ȳ` dominates `x̄`, that is if the section defining `ȳ` is the restriction of the
one defining `x̄` along a morphism of their field spectra, then a quasi-coherent `F` has the
same length at `x̄` and at `ȳ`.

A small étale neighbourhood of `x̄` exists
(`AlgebraicGeometry.Space.nonempty_smallEtaleNeighborhood`), and restricting it along the
domination gives a neighbourhood of `ȳ` with the same chart and the same point of that chart
(`AlgebraicGeometry.Space.chartPoint_neighborhoodAlong`), so
`AlgebraicGeometry.Space.geometricLength_eq_chartZariskiLength` computes both lengths as one
and the same length of a Zariski stalk. -/
theorem geometricLength_eq_of_dominates {x y : GeometricPoint B S hS X}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : X.map f.op x.val.value = y.val.value) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] :
    geometricLength B S hS ⟨X, hX⟩ x F = geometricLength B S hS ⟨X, hX⟩ y F := by
  obtain ⟨V⟩ := nonempty_smallEtaleNeighborhood hX x
  rw [geometricLength_eq_chartZariskiLength B S hS hX V F,
    geometricLength_eq_chartZariskiLength B S hS hX ((neighborhoodAlong f hf).obj V) F,
    chartPoint_neighborhoodAlong B S hS f hf V]
  rfl

/-- **Stacks 0EE1: the length at a geometric point does not depend on the geometric point.**
Let `F` be a quasi-coherent `𝒪_X`-module and let `x̄` and `ȳ` be geometric points of `X` lying
over the same point `x` of `|X|`.  Then `F` has the same length at `x̄` as at `ȳ`.  So the
length of Stacks 0EE2 is a function of `x`, which is what makes that definition well posed.

The two points are dominated by a common third
(`AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`), and the length is
unchanged along a domination
(`AlgebraicGeometry.Space.geometricLength_eq_of_dominates`). -/
@[stacks 0EE1 "independence of the chosen geometric point above a point of the space"]
theorem geometricLength_eq_of_image_eq (x y : GeometricPoint B S hS X)
    (h : x.image = y.image) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] :
    geometricLength B S hS ⟨X, hX⟩ x F = geometricLength B S hS ⟨X, hX⟩ y F := by
  obtain ⟨r, ⟨fx, hfx⟩, ⟨fy, hfy⟩⟩ :=
    GeometricPoint.exists_common_extension x y (rfl : x.LiesOver x.image) h.symm
  exact (geometricLength_eq_of_dominates B S hS hX fx hfx F).trans
    (geometricLength_eq_of_dominates B S hS hX fy hfy F).symm

end AlgebraicGeometry.Space

end
