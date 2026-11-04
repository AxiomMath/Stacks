module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Riemann-Roch for an invertible module on a proper scheme of dimension at most one

Let `k` be a field and let `X` be a proper scheme over `k` of dimension at most one, not assumed
integral nor of dimension exactly one. For every invertible `𝒪_X`-module `ℒ` of rank one,

`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`

with `c₁` given by the component rule `Stacks.Chow.firstChernComponentCycleRule` of `ℒ`, and
consequently

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.cycleDegree_firstChernComponentCycle`: the degree on `X` of a component cycle
  is the degree, on the component, of the rule's value there.
* `AlgebraicGeometry.val_meromorphicDivisorCycle_eq`: on an integral scheme of delta-dimension one,
  the divisor cycle of a meromorphic section is its component cycle.
* `AlgebraicGeometry.componentDegree_eq_cycleDegree_firstChernComponentCycle`: on each reduced
  one-dimensional component `C(ξ)` of `X`, the degree of `ℒ|_{C(ξ)}` is the degree of the zero
  cycle the component rule of `ℒ` assigns to `C(ξ)`.
* `AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_isInvertible`:
  `deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`.
* `AlgebraicGeometry.eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible_of_isProper`:
  `χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.Chow Stacks.Divisors
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-! ### The degree of a component cycle is computed on the component -/

/-- The degree on `X` of the component cycle of `W` is the degree, on `W`, of the rule's value at
`W`. -/
theorem cycleDegree_firstChernComponentCycle
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    (s : (fieldChowSituation k).S) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension (fieldChowSituation k) (W.subschemeι ≫ p) = ((1 : ℤ) : EInt))
    [IsProper (W.subschemeι ≫ p)] :
    cycleDegree (fieldChowSituation k) p s
        (firstChernComponentCycle (fieldChowSituation k) p 0 chern W hW hDim) =
      cycleDegree (fieldChowSituation k) (W.subschemeι ≫ p) s (chern W hW hDim) := by
  rw [firstChernComponentCycle, cycleDegree_apply, cycleDegree_apply,
    properPushforward_properPushforward]

/-! ### The two divisor cycles of one meromorphic section -/

/-- On an integral scheme of delta-dimension one, the divisor cycle
`Stacks.Chow.meromorphicDivisorCycle` of a meromorphic section `t` is its component cycle
`Stacks.Chow.chernComponentCycle`. -/
theorem val_meromorphicDivisorCycle_eq (C : ChowSituation.{u}) {V : Scheme.{u}} (q : V ⟶ C.S)
    [LocallyOfFiniteType q] [IsIntegral V] [IsLocallyNoetherian V]
    (hq : schemeDeltaDimension C q = ((1 : ℤ) : EInt)) {M : V.Modules}
    (hM : ∀ x : V, IsTrivializedNear M x) (t : M.presheaf.stalk (genericPoint V)) :
    ((meromorphicDivisorCycle C q hq hM t).val : CycleGroup C q 0) =
      chernComponentCycle C q hq hM t := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hx : ∃ Z : Stacks.Divisors.PrimeDivisor V, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [meromorphicDivisorCycle_genericPoint, chernComponentCycle_genericPoint]
  · rw [meromorphicDivisorCycle_eq_zero C q hq hM t x (not_exists.mp hx),
      chernComponentCycle_eq_zero C q hq hM t x (not_exists.mp hx)]

/-! ### The component degrees of an invertible module -/

/-- On the reduced one-dimensional component `C(ξ)` of a proper scheme `X` of dimension at most one
over `k`, the degree of `ℒ|_{C(ξ)}` for an invertible module `ℒ` of rank one is the degree of the
zero cycle that the component rule `Stacks.Chow.firstChernComponentCycleRule` of `ℒ` assigns to
`C(ξ)`. -/
theorem componentDegree_eq_cycleDegree_firstChernComponentCycle
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (ξ : genericPointsOne X) :
    componentDegree k p hdim L 1 ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0
          (firstChernComponentCycleRule (fieldChowSituation k) p 0 L)
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
          (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
          (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2)) := by
  classical
  set W : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X))
  have hWint : IsIntegral W.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1
  have hDim : schemeDeltaDimension (fieldChowSituation k) (W.subschemeι ≫ p) = ((1 : ℤ) : EInt) :=
    schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2
  have hprop : IsProper (W.subschemeι ≫ p) := isProper_reducedComponentι_comp k p ξ
  have hcurve : IsCurve k (W.subschemeι ≫ p) := isCurve_reducedComponentι_comp k p ξ
  have hnoeth : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have hdimW : topologicalKrullDim W.subscheme ≤ 1 :=
    topologicalKrullDim_reducedComponent_le X hdim ξ
  have hM : SheafOfModules.IsInvertible W.subscheme.sheaf.obj W.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback W.subschemeι).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (Scheme.Hom.toLRSHom W.subschemeι).toShHom L ‹_›
  have hM' : SheafOfModules.IsInvertible W.subscheme.presheaf W.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback W.subschemeι).obj L) := hM
  have hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback W.subschemeι).obj L) 1 :=
    isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ L 1
  obtain ⟨t, ht⟩ := exists_ne_zero_genericStalk_of_isInvertible
    ((Scheme.Modules.pullback W.subschemeι).obj L)
  have htriv : ∀ x : W.subscheme,
      IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x := fun x =>
    isTrivializedNear_of_isInvertible _ x
  have hleft : componentDegree k p hdim L 1 ξ =
      curveDegree k (W.subschemeι ≫ p) hdimW
        ((Scheme.Modules.pullback W.subschemeι).obj L) 1 := rfl
  have hintegralcase := curveDegree_one_eq_curveChernDegree_of_isCurve k (W.subschemeι ≫ p) hdimW
    ((Scheme.Modules.pullback W.subschemeι).obj L)
  have hcap : firstChernClassCapOfInvertible (fieldChowSituation k) (W.subschemeι ≫ p) 0
        ((Scheme.Modules.pullback W.subschemeι).obj L)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (W.subschemeι ≫ p)
          (𝟙 W.subscheme) 1) =
      QuotientAddGroup.mk
        ((meromorphicDivisorCycle (fieldChowSituation k) (W.subschemeι ≫ p) hDim htriv t).val :
          CycleGroup (fieldChowSituation k) (W.subschemeι ≫ p) 0) :=
    firstChernClassCapOfInvertible_fundamentalCycle_eq_mk (fieldChowSituation k)
      (W.subschemeι ≫ p) hDim ((Scheme.Modules.pullback W.subschemeι).obj L) t ht
  have hrule : (QuotientAddGroup.mk
        (firstChernComponentCycleRule (fieldChowSituation k) p 0 L W hWint hDim) :
        chowGroup (fieldChowSituation k) (W.subschemeι ≫ p) 0) =
      QuotientAddGroup.mk
        (chernComponentCycle (fieldChowSituation k) (W.subschemeι ≫ p) hDim htriv t) :=
    (firstChernComponentClass_eq_mk (fieldChowSituation k) p 0 L W hWint hDim).symm.trans
      (firstChernComponentClass_eq_mk_of_ne_zero (fieldChowSituation k) p 0 L W hDim ht)
  have hgoalL : componentDegree k p hdim L 1 ξ =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
          (W.subschemeι ≫ p) (IsLocalRing.closedPoint k)
        (QuotientAddGroup.mk
          (chernComponentCycle (fieldChowSituation k) (W.subschemeι ≫ p) hDim htriv t)) := by
    rw [hleft, hintegralcase, curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible, hcap,
      val_meromorphicDivisorCycle_eq]
  rw [hgoalL, cycleDegree_firstChernComponentCycle k p
    (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) (IsLocalRing.closedPoint k) W
    hWint hDim, ← hrule]
  exact chowDegree_mk _ _ _ _ _

/-! ### Riemann-Roch for an invertible module -/

/-- For an invertible module `ℒ` of rank one on a proper scheme `X` of dimension at most one over a
field, `deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`, with `c₁` the component rule
`Stacks.Chow.firstChernComponentCycleRule` of `ℒ`. -/
theorem curveDegree_eq_curveChernDegree_of_isInvertible (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    curveDegree k p hdim L 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) :=
  curveDegree_eq_curveChernDegree_of_componentDegree k p hdim L 1
    (firstChernComponentCycleRule (fieldChowSituation k) p 0 L)
    (componentDegree_eq_cycleDegree_firstChernComponentCycle k p hdim L)

/-- Riemann-Roch for an invertible module `ℒ` of rank one on a proper scheme `X` of dimension at
most one over a field: `χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`, with `c₁` the component rule
`Stacks.Chow.firstChernComponentCycleRule` of `ℒ`. -/
@[sga "6 XIII 4.6" "more general", sga "7 X 1.4" "more general"]
theorem eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible_of_isProper
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] [L.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k p L =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible k p hdim L
    (curveDegree_eq_curveChernDegree_of_isInvertible k p hdim L)

end AlgebraicGeometry

end
