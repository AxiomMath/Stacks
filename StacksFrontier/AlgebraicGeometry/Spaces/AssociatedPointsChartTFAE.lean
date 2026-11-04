module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreChartScheme

/-!
# Ordinary association at a point of an étale scheme chart of a locally Noetherian space

Let `X` be a locally Noetherian algebraic space over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module. Conditions (4) and (5) of Stacks 0CTW read *ordinary*
association — Stacks 02OJ, the maximal ideal of the Zariski local ring is the annihilator of an
element of the Zariski stalk — off a point `u` of an étale scheme chart `f : U → X` above a
point `x` of `X`: condition (4) asks it of some such `f` and `u`, condition (5) of every one.

Both are equivalent to the conditions (1), (2) and (3) already stated for `X`. The chart's
scheme is locally Noetherian, by Stacks 03E8, so its local rings are Noetherian and ordinary
and weak association agree there by Stacks 05AR; the resulting weak association at `u` is
conditions (1) and (2), which are the weak association of `X` by Stacks 0CTW.

## Main results

* `AlgebraicGeometry.Space.isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint`:
  **Stacks 0CTW, conditions (4) and (5) at a point of a chart scheme.** Ordinary association at
  a point of an étale scheme chart is weak association of the point of `X` it lies over.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_exists_isAssociatedPoint_restrictToChart`
  and
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_forall_isAssociatedPoint_restrictToChart`:
  **Stacks 0CTW, condition (4)** and **condition (5)** themselves, each as an equivalence with
  the weak association of Stacks 0CTX.
* `AlgebraicGeometry.Space.exists_isAssociatedPoint_restrictToChart_iff_forall`: conditions (4)
  and (5) are equivalent to each other.
* `AlgebraicGeometry.Space.isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime` and
  `AlgebraicGeometry.Space.isAssociatedPoint_restrictToChart_iff_isAssociatedPrimeStacks`:
  conditions (4) and (5) against condition (3), respectively condition (6), at a geometric
  point.

## Implementation notes

Local Noetherianity of `X` is the étale-local scheme property of Stacks 03E6,
`AlgebraicGeometry.Space.HasEtaleLocalProperty` at `AlgebraicGeometry.IsLocallyNoetherian`,
which is the hypothesis the source carries; nothing here needs the quasi-compact and
quasi-separated Noetherianity of Stacks 03EA.

The step from the chart's local Noetherianity to Stacks 05AR is taken through the finite
generation of the maximal ideal of the chart's local ring,
`AlgebraicGeometry.Space.fg_maximalIdeal_stalk_chartScheme`, which is what the pointwise form
`AlgebraicGeometry.mem_associatedPoints_iff_mem_weaklyAssociatedPoints` of Stacks 05AR consumes.

Conditions (1) and (2) are taken in the chart-scheme form
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint`,
which quantifies over `AlgebraicGeometry.Space.SmallEtale` charts and points of their schemes
with no geometric point in the statement, so conditions (4) and (5) here quantify over exactly
the data conditions (1) and (2) do. Every point of `X` carries such a chart point, by
`AlgebraicGeometry.Space.exists_chartSchemeToPoints_eq`, which is what makes the some-chart and
every-chart forms equivalent rather than merely comparable.

Against conditions (3) and (6) the chart is instead an étale neighbourhood of a geometric
point, so that the geometric stalk is in scope. Condition (6) needs the maximal ideal of
`𝒪_{X, x̄}` to be finitely generated, and local Noetherianity of `X` supplies that: it makes
`𝒪_{X, x̄}` a Noetherian ring by
`AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian`, which is how
`AlgebraicGeometry.Space.isWeaklyAssociatedPrime_maximalIdeal_iff_isAssociatedPrimeStacks`
obtains it. So the same hypothesis `hLN` serves every result here.

## References

* [Stacks Project, Lemma 71.2.1 (Tag 0CTW)](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### Conditions (4) and (5) at a point of a chart scheme -/

/-- **Stacks 0CTW, conditions (4) and (5) at a point of a chart scheme.** Let `X` be a locally
Noetherian algebraic space, `F` a quasi-coherent `𝒪_X`-module and `w` a point of the scheme of
an étale chart `W` of `X`. Then `w` is *associated* to the restriction `F|_W`, in the Zariski
sense of Stacks 02OJ, exactly when the point of `X` it lies over is weakly associated to `F` in
the sense of Stacks 0CTX.

The chart's scheme is locally Noetherian by Stacks 03E8, so the maximal ideal of `𝒪_{W, w}` is
finitely generated and association at `w` is weak association at `w` by Stacks 05AR; that is
conditions (1) and (2). -/
@[stacks 0CTW "conditions (4) and (5) at a point of a chart scheme"]
theorem isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (W : SmallEtale B S hS X.1) (w : chartScheme W) :
    Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F W) w ↔
      IsWeaklyAssociatedPoint B S hS X F (chartSchemeToPoints B S hS X.1 W w) :=
  (mem_associatedPoints_iff_mem_weaklyAssociatedPoints (restrictToChart B S hS X.2 F W) w
    (fg_maximalIdeal_stalk_chartScheme B S hS X hLN W w)).trans
    (isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X F W w)

/-! ### Conditions (4) and (5) themselves -/

/-- **Stacks 0CTW, condition (4).** Let `X` be a locally Noetherian algebraic space and `F` a
quasi-coherent `𝒪_X`-module. A point `x` of `X` is weakly associated to `F` exactly when there
is *some* étale scheme chart `W` of `X` and some point `w` of its scheme above `x` which is
associated to the restriction `F|_W`. -/
@[stacks 0CTW "condition (4)"]
theorem isWeaklyAssociatedPoint_iff_exists_isAssociatedPoint_restrictToChart
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔
      ∃ (W : SmallEtale B S hS X.1) (w : chartScheme W),
        chartSchemeToPoints B S hS X.1 W w = x ∧
          Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F W) w := by
  constructor
  · intro hx
    obtain ⟨W, w, rfl⟩ := exists_chartSchemeToPoints_eq B S hS X x
    exact ⟨W, w, rfl,
      (isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X hLN F W w).mpr hx⟩
  · rintro ⟨W, w, rfl, h⟩
    exact (isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X hLN F W w).mp h

/-- **Stacks 0CTW, condition (5).** Let `X` be a locally Noetherian algebraic space and `F` a
quasi-coherent `𝒪_X`-module. A point `x` of `X` is weakly associated to `F` exactly when
*every* point of the scheme of *every* étale chart of `X` lying above `x` is associated to the
restriction of `F` to that chart. -/
@[stacks 0CTW "condition (5)"]
theorem isWeaklyAssociatedPoint_iff_forall_isAssociatedPoint_restrictToChart
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔
      ∀ (W : SmallEtale B S hS X.1) (w : chartScheme W),
        chartSchemeToPoints B S hS X.1 W w = x →
          Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F W) w := by
  constructor
  · rintro hx W w rfl
    exact (isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X hLN F W w).mpr
      hx
  · intro h
    obtain ⟨W, w, rfl⟩ := exists_chartSchemeToPoints_eq B S hS X x
    exact (isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X hLN F W w).mp
      (h W w rfl)

/-- **Stacks 0CTW, conditions (4) and (5).** On a locally Noetherian algebraic space ordinary
association of some point of some étale scheme chart above `x` is ordinary association of every
point of every such chart. -/
@[stacks 0CTW "conditions (4) and (5)"]
theorem exists_isAssociatedPoint_restrictToChart_iff_forall
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    (∃ (W : SmallEtale B S hS X.1) (w : chartScheme W),
        chartSchemeToPoints B S hS X.1 W w = x ∧
          Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F W) w) ↔
      ∀ (W : SmallEtale B S hS X.1) (w : chartScheme W),
        chartSchemeToPoints B S hS X.1 W w = x →
          Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F W) w :=
  (isWeaklyAssociatedPoint_iff_exists_isAssociatedPoint_restrictToChart
      B S hS X hLN F x).symm.trans
    (isWeaklyAssociatedPoint_iff_forall_isAssociatedPoint_restrictToChart B S hS X hLN F x)

/-! ### Conditions (4) and (5) against conditions (3) and (6) -/

/-- **Stacks 0CTW, conditions (4) and (5) against condition (3).** Let `X` be a locally
Noetherian algebraic space, `F` a quasi-coherent `𝒪_X`-module and `φ : (U, ū) → (X, x̄)` an
étale neighbourhood of a geometric point whose chart `U` is a scheme. Then `u` is associated to
`φ^*F` exactly when the maximal ideal of `𝒪_{X, x̄}` is a weakly associated prime of the
geometric stalk `F_{x̄}`. -/
@[stacks 0CTW "conditions (4) and (5) against condition (3)"]
theorem isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
        (chartPoint B S hS X.1 V) ↔
      letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
        (geometricModuleStalk B S hS X xbar F).isModule
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) := by
  refine Iff.trans ?_ (isWeaklyAssociatedPoint_restrictToChart_iff B S hS X V F)
  exact mem_associatedPoints_iff_mem_weaklyAssociatedPoints
    (restrictToChart B S hS X.2 F V.chart) (chartPoint B S hS X.1 V)
    (fg_maximalIdeal_stalk_chartScheme B S hS X hLN V.chart (chartPoint B S hS X.1 V))

/-- **Stacks 0CTW, conditions (4) and (5) against condition (6).** In the situation of
`AlgebraicGeometry.Space.isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime`, `u` is
associated to `φ^*F` exactly when the maximal ideal of the étale local ring `𝒪_{X, x̄}` is an
associated prime of the geometric stalk `F_{x̄}`. -/
@[stacks 0CTW "conditions (4) and (5) against condition (6)"]
theorem isAssociatedPoint_restrictToChart_iff_isAssociatedPrimeStacks
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
      (geometricModuleStalk B S hS X xbar F).isModule
    (Stacks.Divisors.IsAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
        (chartPoint B S hS X.1 V) ↔
      IsAssociatedPrimeStacks (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) := by
  let : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have : IsNoetherianRing (etaleLocalRing B S hS X.1 xbar) :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X.1 X.2 hLN xbar
  exact (isAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime B S hS X hLN V F).trans
    (isWeaklyAssociatedPrime_maximalIdeal_iff_isAssociatedPrimeStacks B S hS X F xbar
      (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)).fg_of_isNoetherianRing)

end AlgebraicGeometry.Space

end
