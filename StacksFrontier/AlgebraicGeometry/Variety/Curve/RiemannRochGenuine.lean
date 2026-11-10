module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesSegre
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochFull
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Determinant
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleGeometry

/-!
# Equation 0BRY with the Chern classes of Stacks 02U0

Let `k` be a field, `X` a proper scheme over `k` of dimension at most one and `ℰ` a finite locally
free `𝒪_X`-module of constant rank `r`. This file proves

  `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`

with `c₁(ℰ) ∩ -` the intersection with the first Chern class of [Stacks, Tag 02U5], read off the
Chern classes of [Stacks, Tag 02U0] (`Stacks.Chow.GenuineChern.chernCycleRule`). The proof is the
source's: by [Stacks, Tag 0AYW] both sides are sums over the reduced one-dimensional components
`C` of `X`, and on each `C` the class `c₁(ℰ|_C) ∩ [C]` is `c₁(det ℰ|_C) ∩ [C]`
(`Stacks.Chow.GenuineChern.firstChern_eq_firstChernClassCapChow_exteriorPower`, [Stacks, Tag 02UI]
and the splitting of [Stacks, Tag 0AYP] behind it), whose degree is `deg(det ℰ|_C) = deg(ℰ|_C)`.

## Main results

* `AlgebraicGeometry.componentDegree_eq_cycleDegree_chernCycleRule` — on each reduced
  one-dimensional component `C` of `X`, `deg(ℰ|_C)` is the degree of the zero cycle
  `c₁(ℰ|_C) ∩ [C]`.
* `AlgebraicGeometry.curveDegree_eq_curveChernDegreeOfModule_chernCycleRule` — the equation, at
  the component rule of the classes of Stacks 02U0.
* `AlgebraicGeometry.chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree` — the equation,
  through the operation `c₁(ℰ) ∩ -` of Stacks 02U5 on the fundamental cycle `[X]_1`.
* `AlgebraicGeometry.curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental` — **equation
  [Stacks, Tag 0BRY]** and [Stacks, Tag 0AZ3], `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, at every constant
  rank. Equation [Stacks, Tag 0BRZ] built on it is
  `AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add` of
  `StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochChern`.

## References

* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.Chow
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

/-- A cycle transported along an equality of degrees has the transported class. -/
theorem mk_cycleGroupOfEq {C : ChowSituation.{u}} {Y : Scheme.{u}} {q : Y ⟶ C.S}
    [LocallyOfFiniteType q] {d e : ℤ} (h : d = e) (α : CycleGroup C q d) :
    QuotientAddGroup.mk' (rationalEquivalences C q e) (cycleGroupOfEq h α) =
      chowGroupCast C q h (QuotientAddGroup.mk' (rationalEquivalences C q d) α) := by
  subst h; rfl

/-- The cap product of Stacks 02SO commutes with transport along an equality of degrees. -/
theorem chowGroupCast_firstChernClassCapOfInvertible {C : ChowSituation.{u}} {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] {d e : ℤ} (h : d = e)
    (α : CycleGroup C q (d + 1)) :
    chowGroupCast C q h (firstChernClassCapOfInvertible C q d L α) =
      firstChernClassCapOfInvertible C q e L (cycleGroupOfEq (by rw [h]) α) := by
  subst h; rfl

/-- Transporting the class of a pushed-forward cycle along an equality of degrees is pushing
forward the transported cycle. -/
theorem chowGroupCast_mk_properPushforward {C : ChowSituation.{u}} {W Y : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (ι : W ⟶ Y) [IsProper ι] (h : ι ≫ sY = sW) {d e : ℤ} (he : d = e) (γ : CycleGroup C sW d) :
    chowGroupCast C sY he
        (QuotientAddGroup.mk' (rationalEquivalences C sY d) (properPushforward C sW sY ι h d γ)) =
      QuotientAddGroup.mk' (rationalEquivalences C sY e)
        (properPushforward C sW sY ι h e (cycleGroupOfEq he γ)) := by
  subst he; rfl

attribute [local instance] isInvertible_exteriorPower_self_ringCatSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
  (hdet : ∀ {T : Scheme.{u}} (q : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q]
    (F : T.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (d : ℤ)
    (α : chowGroup (fieldChowSituation k) q d),
    GenuineChern.firstChern F (fieldChowSituation k) q r d α =
      firstChernClassCapChow (fieldChowSituation k) (d - 1) q
        (Scheme.Modules.exteriorPower F (r : ℤ))
        (chowGroupCast (fieldChowSituation k) q (by omega) α))

include hdet in
/-- **The integral case of equation 0BRY, on a component.** On the reduced one-dimensional
component `C(ξ)` of `X`, the degree of `ℰ|_{C(ξ)}` is the degree of the zero cycle the rule of
Stacks 02U0 assigns to `C(ξ)`, a representative of `c₁(ℰ|_{C(ξ)}) ∩ [C(ξ)]`. -/
theorem componentDegree_eq_cycleDegree_chernCycleRule (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (ξ : genericPointsOne X) :
    componentDegree k p hdim E (n + 1) ξ =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0
          (curveFirstChernRule k p E (n + 1)
            (GenuineChern.chernCycleRule (fieldChowSituation k) (n + 1)))
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
  have : IsProper (W.subschemeι ≫ p) := isProper_reducedComponentι_comp k p ξ
  have hdimW : topologicalKrullDim W.subscheme ≤ 1 :=
    topologicalKrullDim_reducedComponent_le X hdim ξ
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback W.subschemeι).obj E) (n + 1) :=
    isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E (n + 1)
  set F := (Scheme.Modules.pullback W.subschemeι).obj E
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower F ((n + 1 : ℕ) : ℤ)) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F (n + 1)
  set z := cycleAssociatedToClosedSubscheme (fieldChowSituation k) (W.subschemeι ≫ p)
    (𝟙 W.subscheme) 1
  set c := firstChernClassCapOfInvertible (fieldChowSituation k) (W.subschemeι ≫ p) 0
    (Scheme.Modules.exteriorPower F ((n + 1 : ℕ) : ℤ)) z
  -- the left side: the degree of `det(ℰ|_W)` on the curve `W`, as a cap product
  have hleft : componentDegree k p hdim E (n + 1) ξ =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
        (W.subschemeι ≫ p) (IsLocalRing.closedPoint k) c := by
    change curveDegree k (W.subschemeι ≫ p) hdimW F (n + 1) = _
    rw [curveDegree_eq_curveDegree_exteriorPower_of_isProper k (W.subschemeι ≫ p) hdimW (n + 1) F,
      curveDegree_eq_curveChernDegree_of_isInvertible k (W.subschemeι ≫ p) hdimW
        (Scheme.Modules.exteriorPower F ((n + 1 : ℕ) : ℤ)),
      curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible]
  -- the right side: the class of the rule's value at `W` is `c₁(ℰ|_W) ∩ [W]`
  have h1 := firstChern_eq_bundleChernCapFamily_one F n (fieldChowSituation k) (W.subschemeι ≫ p)
    1 (QuotientAddGroup.mk' _ z)
  rw [hdet] at h1
  have hR : (QuotientAddGroup.mk' _ (curveFirstChernRule k p E (n + 1)
        (GenuineChern.chernCycleRule (fieldChowSituation k) (n + 1)) W hWint hDim) :
        chowGroup (fieldChowSituation k) (W.subschemeι ≫ p) 0) = c := by
    rw [curveFirstChernRule, dite_eq_left (Nat.succ_pos n)]
    unfold firstChernComponentCycleRuleOfRank chernClassComponentCycleOn
    rw [mk_cycleGroupOfEq, GenuineChern.mk_chernCycleRule_succ]
    calc _ = chowGroupCast (fieldChowSituation k) (W.subschemeι ≫ p) (show (1 : ℤ) - 1 = 0 by simp)
          (chowGroupCast (fieldChowSituation k) (W.subschemeι ≫ p) (by simp)
            (bundleChernCapFamily F n (fieldChowSituation k) (W.subschemeι ≫ p) 1
              (QuotientAddGroup.mk' _ z) ⟨1, by omega⟩)) := by
          rw [chowGroupCast_chowGroupCast]; rfl
      _ = _ := by
          rw [← h1, ← mk_cycleGroupOfEq, firstChernClassCapChow_mk,
            chowGroupCast_firstChernClassCapOfInvertible]
          rfl
  rw [hleft, cycleDegree_firstChernComponentCycle k p
    (curveFirstChernRule k p E (n + 1)
      (GenuineChern.chernCycleRule (fieldChowSituation k) (n + 1)))
    (IsLocalRing.closedPoint k) W hWint hDim, ← hR]
  exact chowDegree_mk (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) _ _ _

include hdet in
/-- **Equation [Stacks, Tag 0BRY] with the Chern classes of Stacks 02U0.** On a proper scheme `X`
of dimension at most one over a field `k`, a finite locally free `𝒪_X`-module `ℰ` of constant rank
`r` satisfies `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, where `c₁(ℰ) ∩ -` is the intersection with the first
Chern class of Stacks 02U5 built from the classes of Stacks 02U0
(`Stacks.Chow.GenuineChern.chernCycleRule`), zero in rank zero. -/
theorem curveDegree_eq_curveChernDegreeOfModule_chernCycleRule_of_det
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r
      (GenuineChern.chernCycleRule (fieldChowSituation k) r) := by
  rcases r with _ | n
  · exact curveDegree_eq_curveChernDegreeOfModule_rank_zero k p hdim E _
  · exact curveDegree_eq_curveChernDegreeOfModule_of_componentDegree k p hdim E (n + 1) _
      (componentDegree_eq_cycleDegree_chernCycleRule k p hdet hdim E n)

/-- **The degree of `c₁(ℰ) ∩ [X]_1` computed by the operation of Stacks 02U5.** The degree of the
zero cycle class `c₁(ℰ) ∩ [X]_1`, for the intersection with the first Chern class of Stacks 02U5 at
the classes of Stacks 02U0, is the integer `curveChernDegreeOfModule` at the rule of those
classes. -/
theorem chowDegree_firstChernCapOnCycles_fundamental (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
        (IsLocalRing.closedPoint k)
        (chowGroupCast (fieldChowSituation k) p (show (1 : ℤ) - 1 = 0 by simp)
          (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) p E r 1
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))) =
      curveChernDegreeOfModule k p hdim E r
        (GenuineChern.chernCycleRule (fieldChowSituation k) r) := by
  rcases r with _ | n
  · rw [curveChernDegreeOfModule_rank_zero, GenuineChern.firstChernCapOnCycles_zero]
    simp
  have : Fintype (genericPointsOne X) := (finite_genericPointsOne_of_isProper k p).fintype
  rw [curveChernDegreeOfModule, curveChernDegree_eq_sum k p hdim _
    (fun ξ : genericPointsOne X =>
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
    (fun ξ => Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
    (fun ξ => schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2)
    (fun ξ => (componentMultiplicity X ξ : ℤ))
    (cycleAssociatedToClosedSubscheme_id_eq_finsum k p),
    GenuineChern.firstChernCapOnCycles_succ,
    GenuineChern.chernCapOnCycles_sum (fieldChowSituation k) p E (n + 1) 1 ⟨1, by omega⟩
    (fun ξ : genericPointsOne X =>
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ.1} : Set X)))
    (fun ξ => Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure ξ.1)
    (fun ξ => schemeDeltaDimension_vanishingIdeal_closure_eq_one k p ξ.2)
    (fun ξ => (componentMultiplicity X ξ : ℤ)) _
    (cycleAssociatedToClosedSubscheme_id_eq_finsum k p),
    chowGroupCast_chowGroupCast, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_zsmul, map_zsmul, smul_eq_mul]
  congr 1
  unfold GenuineChern.chernCapOnCycles
  rw [chernClassCap_integral_cycle (fieldChowSituation k) p E (n + 1) _ 1 ⟨1, by omega⟩ _ _
    (Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure t.1)
    (schemeDeltaDimension_vanishingIdeal_closure_eq_one k p t.2)]
  rw [chernClassComponentCycle, ← QuotientAddGroup.mk'_apply, chowGroupCast_mk_properPushforward]
  exact chowDegree_mk (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) _ _ _

include hdet in
/-- **Equation [Stacks, Tag 0BRY] read through the operation of Stacks 02U5.** On a proper scheme
`X` of dimension at most one over a field, for `ℰ` finite locally free of constant rank `r`,
`deg(c₁(ℰ) ∩ [X]_1) = deg(ℰ)`, with `c₁(ℰ) ∩ -` the intersection of Stacks 02U5 with the first
Chern class of Stacks 02U0, zero in rank zero. -/
theorem chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree_of_det
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
        (IsLocalRing.closedPoint k)
        (chowGroupCast (fieldChowSituation k) p (show (1 : ℤ) - 1 = 0 by simp)
          (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) p E r 1
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))) =
      curveDegree k p hdim E r := by
  rw [chowDegree_firstChernCapOnCycles_fundamental k p hdim E r,
    curveDegree_eq_curveChernDegreeOfModule_chernCycleRule_of_det k p hdet hdim E r]

omit hdet

/-- The identity `c₁(ℰ) = c₁(⋀ʳ ℰ)` on Chow groups over a field, in the form the statements above
consume, from `Stacks.Chow.GenuineChern.firstChern_eq_firstChernClassCapChow_exteriorPower`. -/
theorem firstChern_eq_firstChernClassCapChow_exteriorPower_field
    {T : Scheme.{u}}
    (q : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] (F : T.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (d : ℤ)
    (α : chowGroup (fieldChowSituation k) q d) :
    GenuineChern.firstChern F (fieldChowSituation k) q r d α =
      firstChernClassCapChow (fieldChowSituation k) (d - 1) q
        (Scheme.Modules.exteriorPower F (r : ℤ))
        (chowGroupCast (fieldChowSituation k) q (by omega) α) :=
  GenuineChern.firstChern_eq_firstChernClassCapChow_exteriorPower
    (GenuineChern.topHalf _)
    (GenuineChern.flatCompat_of _ GenuineChern.bundleBaseChangeHolds) (GenuineChern.subAdditive _)
    r q F d α

/-- **Equation [Stacks, Tag 0BRY] with the Chern classes of Stacks 02U0.** On a proper scheme `X`
of dimension at most one over a field `k`, a finite locally free `𝒪_X`-module `ℰ` of constant rank
`r` satisfies `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, where `c₁(ℰ) ∩ -` is the intersection with the first
Chern class of Stacks 02U5 built from the classes of Stacks 02U0
(`Stacks.Chow.GenuineChern.chernCycleRule`), zero in rank zero. -/
theorem curveDegree_eq_curveChernDegreeOfModule_chernCycleRule
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r
      (GenuineChern.chernCycleRule (fieldChowSituation k) r) :=
  curveDegree_eq_curveChernDegreeOfModule_chernCycleRule_of_det k p
    (fun q _ F r _ d α ↦ firstChern_eq_firstChernClassCapChow_exteriorPower_field k q F r d α)
    hdim E r

/-- **Equation [Stacks, Tag 0BRY] read through the operation of Stacks 02U5.** On a proper scheme
`X` of dimension at most one over a field, for `ℰ` finite locally free of constant rank `r`,
`deg(c₁(ℰ) ∩ [X]_1) = deg(ℰ)`, with `c₁(ℰ) ∩ -` the intersection of Stacks 02U5 with the first
Chern class of Stacks 02U0, zero in rank zero. -/
theorem chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
        (IsLocalRing.closedPoint k)
        (chowGroupCast (fieldChowSituation k) p (show (1 : ℤ) - 1 = 0 by simp)
          (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) p E r 1
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))) =
      curveDegree k p hdim E r :=
  chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree_of_det k p
    (fun q _ F r _ d α ↦ firstChern_eq_firstChernClassCapChow_exteriorPower_field k q F r d α)
    hdim E r

/-- **Equation [Stacks, Tag 0BRY]**, in the orientation of the source:
`deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)` for `ℰ` finite locally free of constant rank on a proper scheme of
dimension at most one over a field, with `c₁(ℰ) ∩ -` the operation of Stacks 02U5 at the Chern
classes of Stacks 02U0 and `deg` the degree of Stacks 0AZ1.

Two conventions are fixed here. In rank zero Stacks 02U5 defines no `c₁`; the total Chern class
of a module of rank zero is `1`, so `c₁ = 0`, and `GenuineChern.firstChernCapOnCycles` is zero
there by definition. The operation of Stacks 02U5 extends `[W] ↦ i_*(c₁(i^*ℰ) ∩ [W])` over
cycles through representatives of the classes of Stacks 02U0 (`GenuineChern.chowRep`); the choice
does not matter here, since `[X]_1` is a finite sum of fundamental cycles of one-dimensional
components and on each the class is the one of Stacks 02U0
(`GenuineChern.chernCapOnCycles_integral_cycle`). -/
@[stacks 0BRY, stacks 0AZ3]
theorem curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    curveDegree k p hdim E r =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
        (IsLocalRing.closedPoint k)
        (chowGroupCast (fieldChowSituation k) p (show (1 : ℤ) - 1 = 0 by simp)
          (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) p E r 1
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))) :=
  (chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree k p hdim E r).symm

end AlgebraicGeometry

end
