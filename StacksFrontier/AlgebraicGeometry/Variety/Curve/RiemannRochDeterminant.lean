module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# `deg(c₁(ℰ) ∩ [X]_1)` at arbitrary constant rank, as a function of `ℰ`

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` and `ℰ` a finite
locally free `𝒪_X`-module of constant rank `r`. Equation [Stacks, Tag 0BRY] reads

`deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`.

Here `c₁(ℰ)` is the first Chern class of [Stacks, Tag 02SO] of the determinant line bundle
`⋀^r ℰ`, which is invertible by `AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`.
This is the reading of the proof of [Stacks, Tag 0AZ3], which reduces the arbitrary-rank case to
the invertible case by additivity of the degree ([Stacks, Tag 0AYS]) and of the first Chern class.

## Main definitions

The elided prefix is `AlgebraicGeometry`.

* `curveDeterminantChernRule` — the first Chern class component rule of `ℰ`: the rule
  `Stacks.Chow.firstChernComponentCycleRule` of the determinant `⋀^r ℰ`.
* `curveChernDegreeDet` — the integer `deg(c₁(ℰ) ∩ [X]_1)` at that rule.

## Main results

* `curveChernDegreeDet_eq_curveDegree_exteriorPower` — `deg(c₁(ℰ) ∩ [X]_1) = deg(⋀^r ℰ)` at
  every rank.
* `curveDegree_eq_curveChernDegreeDet_one` — equation 0BRY at rank one.
* `curveDegree_eq_curveChernDegreeDet_of_curveDegree_exteriorPower` — equation 0BRY at arbitrary
  constant rank, from the equation `deg(ℰ) = deg(⋀^r ℰ)`, the first equality of
  [Stacks, Tag 0DJ5].
* `curveDegree_eq_curveDegree_exteriorPower_of_componentDegree` — `deg(ℰ) = deg(⋀^r ℰ)` holds on
  `X` as soon as it holds on each reduced one-dimensional component, by [Stacks, Tag 0AYW].
* `curveDegree_eq_curveChernDegreeDet_of_componentDegree` — equation 0BRY at arbitrary constant
  rank from the component degrees.
* `curveDegree_eq_curveChernDegreeDet_of_devissage` — equation 0BRY at positive rank on a proper
  curve, given `AlgebraicGeometry.ExteriorDevissage`.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.Chow
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-! ### The determinant line bundle, in the spelling the component rule asks for -/

/-- The determinant of a module of constant rank is invertible, with the structure sheaf written
as `AlgebraicGeometry.Scheme.sheaf` and its sheaf condition as
`AlgebraicGeometry.Scheme.ringCatSheaf`. -/
theorem isInvertible_exteriorPower_self_ringCatSheaf (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.exteriorPower E (r : ℤ)) :=
  Scheme.Modules.isInvertible_exteriorPower_self E r

attribute [local instance] isInvertible_exteriorPower_self_ringCatSheaf
  Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self

/-! ### The first Chern class of `ℰ` and the integer `deg(c₁(ℰ) ∩ [X]_1)` -/

/-- The first Chern class component rule of a finite locally free module `ℰ` of constant rank
`r`: the rule `Stacks.Chow.firstChernComponentCycleRule` of the determinant bundle `⋀^r ℰ`. -/
def curveDeterminantChernRule (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    FirstChernComponentCycleRule (fieldChowSituation k) p 0 :=
  firstChernComponentCycleRule (fieldChowSituation k) p 0
    (Scheme.Modules.exteriorPower E (r : ℤ))

/-- The integer `deg(c₁(ℰ) ∩ [X]_1)` of equation [Stacks, Tag 0BRY], for `ℰ` finite locally free
of constant rank `r` on a proper scheme of dimension at most one over a field: the degree of the
zero cycle cut out of the fundamental one-cycle by the first Chern class of the determinant of
`ℰ`. -/
def curveChernDegreeDet (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] : ℤ :=
  curveChernDegree k p hdim (curveDeterminantChernRule k p E r)

/-! ### The Chow side of equation 0BRY, computed at every rank -/

/-- `deg(c₁(ℰ) ∩ [X]_1) = deg(⋀^r ℰ)` for `ℰ` finite locally free of any constant rank `r` on a
proper scheme of dimension at most one over a field. -/
theorem curveChernDegreeDet_eq_curveDegree_exteriorPower (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    curveChernDegreeDet k p hdim E r =
      curveDegree k p hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1 :=
  (curveDegree_eq_curveChernDegree_of_isInvertible k p hdim
    (Scheme.Modules.exteriorPower E (r : ℤ))).symm

/-! ### Equation 0BRY in this reading -/

/-- Equation [Stacks, Tag 0BRY] at rank one: `deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`. -/
theorem curveDegree_eq_curveChernDegreeDet_one (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1] :
    curveDegree k p hdim E 1 = curveChernDegreeDet k p hdim E 1 :=
  (curveDegree_exteriorPower_one_eq k p hdim E).trans
    (curveChernDegreeDet_eq_curveDegree_exteriorPower k p hdim E 1).symm

/-- Equation [Stacks, Tag 0BRY] at arbitrary constant rank, given the first equality of
[Stacks, Tag 0DJ5]: `deg(ℰ) = deg(⋀^r ℰ)` implies `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`. -/
theorem curveDegree_eq_curveChernDegreeDet_of_curveDegree_exteriorPower
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hdet : curveDegree k p hdim E r =
      curveDegree k p hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1) :
    curveDegree k p hdim E r = curveChernDegreeDet k p hdim E r :=
  hdet.trans (curveChernDegreeDet_eq_curveDegree_exteriorPower k p hdim E r).symm

/-! ### The remaining equation is componentwise -/

/-- `deg(ℰ) = deg(⋀^r ℰ)` holds as soon as the degrees of `ℰ` and of `⋀^r ℰ` agree on each
reduced one-dimensional component. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_componentDegree
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hcomp : ∀ ξ : genericPointsOne X,
      componentDegree k p hdim E r ξ =
        componentDegree k p hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1 ξ) :
    curveDegree k p hdim E r =
      curveDegree k p hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1 := by
  simp only [
    Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree,
    hcomp]

/-- Equation [Stacks, Tag 0BRY] at arbitrary constant rank, `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, as
soon as the degrees of `ℰ` and of its determinant agree on each reduced one-dimensional
component. -/
theorem curveDegree_eq_curveChernDegreeDet_of_componentDegree
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hcomp : ∀ ξ : genericPointsOne X,
      componentDegree k p hdim E r ξ =
        componentDegree k p hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1 ξ) :
    curveDegree k p hdim E r = curveChernDegreeDet k p hdim E r :=
  curveDegree_eq_curveChernDegreeDet_of_curveDegree_exteriorPower k p hdim E r
    (curveDegree_eq_curveDegree_exteriorPower_of_componentDegree k p hdim E r hcomp)

/-- Equation [Stacks, Tag 0BRY] at positive constant rank on a proper curve satisfying
`AlgebraicGeometry.ExteriorDevissage`: `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`. -/
theorem curveDegree_eq_curveChernDegreeDet_of_devissage [IsCurve k p]
    (hdev : ExteriorDevissage X) (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    curveDegree k p hdim E (n + 1) = curveChernDegreeDet k p hdim E (n + 1) :=
  curveDegree_eq_curveChernDegreeDet_of_curveDegree_exteriorPower k p hdim E (n + 1)
    (curveDegree_eq_curveDegree_exteriorPower_of_devissage k p hdev hdim n E)

end AlgebraicGeometry

end
