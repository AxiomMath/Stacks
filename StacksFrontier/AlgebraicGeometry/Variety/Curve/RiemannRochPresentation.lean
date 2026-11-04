module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.CyclePresentation
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRoch
public import StacksCore.Tactic.StacksAttribute

/-!
# The fundamental one-cycle of a proper scheme of dimension at most one

Let `X` be a proper scheme of dimension at most one over a field `k`. The fundamental one-cycle
`[X]_1` is the sum, weighted by `componentMultiplicity`, of the one-cycles of the reduced
one-dimensional irreducible components of `X`, indexed by
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X`. Over this family of components,
the degree of a finite locally free module `ℰ` is the degree of `c₁(ℰ) ∩ [X]_1` as soon as, on
each component `C(ξ)`, the degree of `ℰ|_{C(ξ)}` is the degree of the zero cycle the first Chern
class component rule assigns to `C(ξ)`.

## Main results

* `AlgebraicGeometry.schemeDeltaDimension_vanishingIdeal_closure_eq_one`: the reduced closed
  subscheme on the closure of a one-dimensional generic point has delta-dimension one over
  `Stacks.Chow.fieldChowSituation k`.
* `AlgebraicGeometry.cycleAssociatedToClosedSubscheme_vanishingIdeal_closure_apply`: the
  one-cycle of such a reduced component, pushed into `X`, is the indicator of the component's
  generic point.
* `AlgebraicGeometry.cycleAssociatedToClosedSubscheme_id_eq_finsum`: `[X]_1` is the
  `componentMultiplicity`-weighted sum of the one-cycles of the reduced one-dimensional
  components of `X`.
* `AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_genericPointsOne`,
  `AlgebraicGeometry.curveDegree_eq_curveChernDegreeOfModule_of_genericPointsOne`: the degree of
  `ℰ` is the degree of `c₁(ℰ) ∩ [X]_1`, given a component formula for the degree of `ℰ` and the
  degree formula on each component.
* `AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_componentDegree`,
  `AlgebraicGeometry.curveDegree_eq_curveChernDegreeOfModule_of_componentDegree`: the degree of
  `ℰ` is the degree of `c₁(ℰ) ∩ [X]_1`, given the degree formula on each component.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.Chow Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- The reduced closed subscheme on the closure of a one-dimensional generic point of `X` has
delta-dimension one over `Stacks.Chow.fieldChowSituation k`. -/
theorem schemeDeltaDimension_vanishingIdeal_closure_eq_one {x : X} (hx : x ∈ genericPointsOne X) :
    schemeDeltaDimension (fieldChowSituation k)
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι ≫ p) =
      ((1 : ℤ) : EInt) := by
  have := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion,
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure]
  exact congrArg (fun z : ℤ => (z : EInt))
    ((mem_genericPointsOne_iff_relativeDimension_eq_one k p
      (mem_genericPointsOne_iff.mp hx).1).mp hx)

open Classical in
/-- Pushed into `X` along the closed immersion of the reduced closed subscheme on `closure {z}`,
for `z` a one-dimensional generic point, the one-cycle associated to that subscheme is the
indicator of `z`. -/
theorem cycleAssociatedToClosedSubscheme_vanishingIdeal_closure_apply
    {z : X} (hz : z ∈ genericPointsOne X) (y : X) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subschemeι 1).1
        y =
      if y = z then 1 else 0 := by
  classical
  have := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure z
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))
  have hgen : genericPoint I.subscheme ∈ genericPoints I.subscheme :=
    Stacks.Chow.genericPoint_mem_genericPoints I.subscheme
  have hzgen : I.subschemeι (genericPoint I.subscheme) = z :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure z
  split_ifs with hy
  · subst hy
    have hreldim : relativeDimension (fieldChowSituation k).dimensionFunction p
        (I.subschemeι (genericPoint I.subscheme)) = 1 := by
      rw [hzgen]
      exact (mem_genericPointsOne_iff_relativeDimension_eq_one k p
        (mem_genericPointsOne_iff.mp hz).1).mp hz
    have heq := Stacks.Chow.cycleAssociatedToClosedSubscheme_apply (fieldChowSituation k) p
      I.subschemeι 1 ⟨genericPoint I.subscheme, hgen⟩ hreldim
    rwa [hzgen, Stacks.Chow.componentMultiplicity_eq_one I.subschemeι hgen] at heq
  · apply Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) p
      I.subschemeι 1 y
    rintro ⟨η, hη, -⟩
    rw [Set.mem_singleton_iff.mp ((Set.ext_iff.mp genericPoints_eq_singleton η.1).mp η.2),
      hzgen] at hη
    exact hy hη.symm

/-- The fundamental one-cycle `[X]_1` of `X` is the sum, weighted by `componentMultiplicity`, of
the one-cycles of the reduced closed subschemes on the closures of the points of
`genericPointsOne X`. -/
theorem cycleAssociatedToClosedSubscheme_id_eq_finsum
    [Fintype (genericPointsOne X)] (x : X) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1).1 x =
      ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X))).subschemeι
          1).1 x := by
  classical
  have key (ξ : genericPointsOne X) := cycleAssociatedToClosedSubscheme_vanishingIdeal_closure_apply
    k p ξ.2 x
  rw [cycleAssociatedToClosedSubscheme_id_apply k p x, finsum_eq_sum_of_fintype]
  simp only [key, mul_ite, mul_one, mul_zero]
  by_cases hx : x ∈ genericPointsOne X
  · rw [dif_pos hx, Finset.sum_eq_single ⟨x, hx⟩ (fun ξ _ hne => ?_) (by simp)]
    · simp
    · exact if_neg fun h => hne (Subtype.ext h.symm)
  · rw [dif_neg hx]
    exact (Finset.sum_eq_zero fun ξ _ => if_neg fun h : x = ξ.1 => hx (h ▸ ξ.2)).symm

/-- Let `ℰ` be finite locally free of rank `r` on a proper scheme `X` of dimension at most one over
`k`, and `chern` a first Chern class component rule. If the degree of `ℰ` is
`∑ᶠ ξ, componentMultiplicity X ξ * d ξ` over the reduced one-dimensional components `C(ξ)`, and
each `d ξ` is the degree of the zero cycle `chern` assigns to `C(ξ)`, then the degree of `ℰ` is
`curveChernDegree k p hdim chern`. -/
theorem curveDegree_eq_curveChernDegree_of_genericPointsOne (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    (d : genericPointsOne X → ℤ)
    (hcomponents : curveDegree k p hdim E r =
      ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) * d ξ)
    (hintegral : ∀ ξ : genericPointsOne X, d ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0 chern
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
          (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
          (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2))) :
    curveDegree k p hdim E r = curveChernDegree k p hdim chern := by
  have : Fintype (genericPointsOne X) :=
    (finite_genericPointsOne_of_isProper k p).fintype
  refine curveDegree_eq_curveChernDegree k p hdim E r chern
    (fun ξ : genericPointsOne X =>
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
    (fun ξ => Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
    (fun ξ => schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2)
    (fun ξ => (componentMultiplicity X ξ : ℤ))
    (cycleAssociatedToClosedSubscheme_id_eq_finsum k p) d ?_ hintegral
  rwa [finsum_eq_sum_of_fintype] at hcomponents

/-- The form of `curveDegree_eq_curveChernDegree_of_genericPointsOne` for the first Chern class
component rule `curveFirstChernRule k p E r chern` of a Chern class cycle rule of rank `r`. -/
theorem curveDegree_eq_curveChernDegreeOfModule_of_genericPointsOne
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    (d : genericPointsOne X → ℤ)
    (hcomponents : curveDegree k p hdim E r =
      ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) * d ξ)
    (hintegral : ∀ ξ : genericPointsOne X, d ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0 (curveFirstChernRule k p E r chern)
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
          (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
          (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2))) :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r chern :=
  curveDegree_eq_curveChernDegree_of_genericPointsOne k p hdim E r
    (curveFirstChernRule k p E r chern) d hcomponents hintegral

/-! ### The degree formula given the formula on each component -/

/-- Let `ℰ` be finite locally free of rank `r` on a proper scheme `X` of dimension at most one over
`k`, and `chern` a first Chern class component rule. If on each reduced one-dimensional component
`C(ξ)` of `X` the degree of `ℰ|_{C(ξ)}` is the degree of the zero cycle `chern` assigns to `C(ξ)`,
then the degree of `ℰ` is `curveChernDegree k p hdim chern`. -/
theorem curveDegree_eq_curveChernDegree_of_componentDegree (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    (hintegral : ∀ ξ : genericPointsOne X, componentDegree k p hdim E r ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0 chern
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
          (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
          (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2))) :
    curveDegree k p hdim E r = curveChernDegree k p hdim chern :=
  curveDegree_eq_curveChernDegree_of_genericPointsOne k p hdim E r chern
    (componentDegree k p hdim E r)
    (Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree
      k p hdim E r) hintegral

/-- The form of `curveDegree_eq_curveChernDegree_of_componentDegree` for the first Chern class
component rule `curveFirstChernRule k p E r chern` of a Chern class cycle rule of rank `r`. -/
theorem curveDegree_eq_curveChernDegreeOfModule_of_componentDegree
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    (hintegral : ∀ ξ : genericPointsOne X, componentDegree k p hdim E r ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0 (curveFirstChernRule k p E r chern)
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
          (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
          (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2))) :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r chern :=
  curveDegree_eq_curveChernDegree_of_componentDegree k p hdim E r
    (curveFirstChernRule k p E r chern) hintegral

end AlgebraicGeometry

end
