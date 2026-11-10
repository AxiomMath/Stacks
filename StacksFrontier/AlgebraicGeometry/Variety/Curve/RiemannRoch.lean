module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.TrivialChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.ZeroDimensional
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# Riemann-Roch on a proper scheme of dimension at most one

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`. The degree of
a finite locally free `𝒪_X`-module `ℰ` of constant rank `r` is `χ(X, ℰ) - r·χ(X, 𝒪_X)`, which is
`AlgebraicGeometry.curveDegree`. This file introduces the other side of the Riemann-Roch formula,
the degree of the zero cycle `c₁(ℰ) ∩ [X]_1`, and states the two equations

* `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, and
* `χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + r·χ(X, 𝒪_X)`,

the second of which follows from the first and the defining formula for the degree.

## Main definitions

* `AlgebraicGeometry.curveChernDegree` — the integer `deg(c₁ ∩ [X]_1)` at an arbitrary first
  Chern class component rule: the cap product of Stacks 02SO, applied to the fundamental one-cycle
  of `X` and composed with the degree homomorphism `A_0(X) ⟶ ℤ` of Stacks 0AZ1.
* `AlgebraicGeometry.curveFirstChernRule` — the component rule of `ℰ` itself, read off the Chern
  classes of Stacks 02U0.
* `AlgebraicGeometry.curveChernDegreeOfModule` — the integer `deg(c₁(ℰ) ∩ [X]_1)`, the previous
  two composed.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible` — for an invertible module the
  definition is the degree of the cap product of Stacks 02SO.
* `curveChernDegree_eq_sum` — on a presentation `[X]_1 = ∑ n_j [W_j]` of the fundamental one-cycle
  by integral closed subschemes of delta-dimension one, the degree of `c₁(ℰ) ∩ [X]_1` is
  `∑ n_j · deg(c₁(ℰ|_{W_j}) ∩ [W_j])`.
* `curveDegree_eq_curveChernDegreeOfModule` — equation 0BRY from a presentation of the
  fundamental one-cycle whose component cycles compute the component degrees of `ℰ`.
* `curveDegree_eq_curveChernDegreeOfModule_rank_zero` — equation 0BRY at rank zero.
* `curveChernDegree_eq_zero_of_topologicalKrullDim_le_zero` — on a scheme of dimension at most
  zero the degree of `c₁ ∩ [X]_1` vanishes at every component rule.
* `curveDegree_eq_curveChernDegree_of_isInvertible_of_topologicalKrullDim_le_zero` and
  `curveDegree_eq_curveChernDegreeOfModule_of_isInvertible_of_topologicalKrullDim_le_zero` —
  equation 0BRY for an invertible module on a scheme of dimension at most zero, in both readings
  of `c₁`.
* `curveDegree_eq_curveChernDegreeOfModule_of_iso_biprodPow_of_topologicalKrullDim_le_zero` —
  equation 0BRY on a scheme of dimension at most zero for a module isomorphic to `𝒪_X^{⊞ r}`.
* `eulerCharacteristic_eq_curveChernDegreeOfModule_add` — equation 0BRZ, the Riemann-Roch formula,
  given equation 0BRY for `ℰ`.
* `eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible` — equation 0BRZ for an invertible
  module, given equation 0BRY for it.
* `eulerCharacteristic_eq_curveChernDegreeOfModule_add_rank_zero` and
  `eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible_of_topologicalKrullDim_le_zero` —
  equation 0BRZ at rank zero, and for an invertible module on a scheme of dimension at most zero.

## Implementation notes

The first Chern class cap product of Stacks 02SO is `Stacks.Chow.firstChernClassCap`, which takes
its value on an integral closed subscheme `W` as the explicit datum
`Stacks.Chow.FirstChernComponentCycleRule`. For an invertible module that datum is a function of
the module, `Stacks.Chow.firstChernComponentCycleRule`. For a module of arbitrary constant rank
the classes `c_j(ℰ|_W) ∩ [W]` of Stacks 02U0 are the explicit datum
`Stacks.Chow.ChernClassCycleRule`; applied to `ℰ` it gives the component rule
`Stacks.Chow.firstChernComponentCycleRuleOfRank`, and `AlgebraicGeometry.curveFirstChernRule` is
that rule, so `AlgebraicGeometry.curveChernDegreeOfModule` is a function of `ℰ` and of the
Stacks 02U0 datum. At rank zero `curveFirstChernRule` is the zero rule.

The degree homomorphism of Stacks 0AZ1 takes a point of the base as an argument. The base here is
the spectrum of a field, whose space has one point; the closed point of the local ring `k` is
used.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U1](https://stacks.math.columbia.edu/tag/02U1)
* [Stacks Project, Tag 02U2](https://stacks.math.columbia.edu/tag/02U2)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- The degree of the zero cycle `c₁(ℰ) ∩ [X]_1` on a proper scheme of dimension at most one over
a field, for the first Chern class given by the component rule `chern`. -/
public def curveChernDegree (_hdim : topologicalKrullDim X ≤ 1)
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0) : ℤ :=
  chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
    (IsLocalRing.closedPoint k)
    (firstChernClassCap (fieldChowSituation k) p 0 chern
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))

/-- For an invertible module the component rule is the one of Stacks 02SO, so the degree of
`c₁(ℒ) ∩ [X]_1` is the degree of the cap product of Stacks 02SO at the fundamental one-cycle. -/
public theorem curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
        (IsLocalRing.closedPoint k)
        (firstChernClassCapOfInvertible (fieldChowSituation k) p 0 L
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1)) :=
  rfl

/-- On a presentation `[X]_1 = ∑ n_j [W_j]` of the fundamental one-cycle by integral closed
subschemes of delta-dimension one, the degree of `c₁(ℰ) ∩ [X]_1` is the sum of the degrees of the
component cycles weighted by the multiplicities. -/
public theorem curveChernDegree_eq_sum (hdim : topologicalKrullDim X ≤ 1)
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    {J : Type u} [Fintype J] (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension (fieldChowSituation k) ((W j).subschemeι ≫ p)
      = ((1 : ℤ) : EInt))
    (n : J → ℤ)
    (hpres : ∀ x : X,
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1).1 x =
        ∑ᶠ j : J, n j *
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (W j).subschemeι 1).1 x) :
    curveChernDegree k p hdim chern =
      ∑ j : J, n j * cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (firstChernComponentCycle (fieldChowSituation k) p 0 chern (W j) (hW j) (hDim j)) := by
  obtain ⟨β, hβ, hβx⟩ := firstChernClassCap_finsum (fieldChowSituation k) p 0 chern W hW hDim
    (locallyFinite_of_finite _) n _ hpres
  have hsum : β = ∑ j : J, n j •
      firstChernComponentCycle (fieldChowSituation k) p 0 chern (W j) (hW j) (hDim j) := by
    apply Subtype.ext
    ext x
    rw [hβx x, finsum_eq_sum_of_fintype]
    simp
  have key : ∀ γ : CycleGroup (fieldChowSituation k) p 0,
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
          (IsLocalRing.closedPoint k) (QuotientAddGroup.mk γ) =
        cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k) γ :=
    fun γ => chowDegree_mk (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_eq_zero k) p (IsLocalRing.closedPoint k) γ
  rw [curveChernDegree, hβ, key β, hsum, map_sum]
  simp

/-- **The reduction of the degree formula to the one-dimensional components.** On a proper scheme
of dimension at most one over a field, the degree of a finite locally free module of constant rank
is the degree of `c₁ ∩ [X]_1` at a first Chern class component rule whose component cycles compute
the component degrees of `ℰ`, over a presentation of the fundamental one-cycle by integral closed
subschemes of delta-dimension one. -/
public theorem curveDegree_eq_curveChernDegree (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    {J : Type u} [Fintype J] (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension (fieldChowSituation k) ((W j).subschemeι ≫ p)
      = ((1 : ℤ) : EInt))
    (n : J → ℤ)
    (hpres : ∀ x : X,
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1).1 x =
        ∑ᶠ j : J, n j *
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (W j).subschemeι 1).1 x)
    (d : J → ℤ) (hcomponents : curveDegree k p hdim E r = ∑ j : J, n j * d j)
    (hintegral : ∀ j, d j = cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
      (firstChernComponentCycle (fieldChowSituation k) p 0 chern (W j) (hW j) (hDim j))) :
    curveDegree k p hdim E r = curveChernDegree k p hdim chern := by
  rw [hcomponents, curveChernDegree_eq_sum k p hdim chern W hW hDim n hpres]
  exact Finset.sum_congr rfl fun j _ => by rw [hintegral j]

/-- The Riemann-Roch formula at an arbitrary first Chern class component rule `chern`: if the
degree of `ℰ` is the degree of `c₁ ∩ [X]_1` at `chern`, then
`χ(X, ℰ) = deg(c₁ ∩ [X]_1) + r · χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_eq_curveChernDegree_add (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0)
    (hdegree : curveDegree k p hdim E r = curveChernDegree k p hdim chern) :
    eulerCharacteristic k p E =
      curveChernDegree k p hdim chern +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  rw [← hdegree, curveDegree_eq_eulerCharacteristic_sub]
  ring

/-! ### Dimension at most zero: the fundamental one-cycle, and what vanishes with it -/

/-- **On a scheme of dimension at most zero over a field every point has delta-dimension at most
zero.** -/
public theorem relativeDimension_le_zero_of_topologicalKrullDim_le_zero
    (hdim0 : topologicalKrullDim X ≤ 0) (x : X) :
    relativeDimension (fieldChowSituation k).dimensionFunction p x ≤ 0 := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  exact relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k) (fun _ _ => rfl) p
    (T := (Set.univ : Set X)) isClosed_univ (r := 0)
    (by rw [topologicalKrullDim_univ]; simpa using hdim0) (Set.mem_univ x)

/-- **On a scheme of dimension at most zero the fundamental one-cycle `[X]_1` vanishes.** -/
public theorem cycleAssociatedToClosedSubscheme_one_eq_zero_of_topologicalKrullDim_le_zero
    (hdim0 : topologicalKrullDim X ≤ 0) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1 = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  refine (cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) p (𝟙 X) 1 x
    ?_).trans rfl
  rintro ⟨-, -, hx⟩
  have := relativeDimension_le_zero_of_topologicalKrullDim_le_zero k p hdim0 x
  lia

/-- **On a scheme of dimension at most zero the degree of `c₁ ∩ [X]_1` vanishes at every first
Chern class component rule.** -/
public theorem curveChernDegree_eq_zero_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0)
    (chern : FirstChernComponentCycleRule (fieldChowSituation k) p 0) :
    curveChernDegree k p hdim chern = 0 := by
  rw [curveChernDegree,
    cycleAssociatedToClosedSubscheme_one_eq_zero_of_topologicalKrullDim_le_zero k p hdim0,
    map_zero, map_zero]

open Stacks.AlgebraicGeometry.ComponentDegrees in
/-- **On a scheme of dimension at most zero that is proper over a field an invertible module has
degree zero.** -/
public theorem curveDegree_eq_zero_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    curveDegree k p hdim L 1 = 0 := by
  have := discreteTopology_of_isProper_of_topologicalKrullDim_le_zero k p hdim0
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  rw [← invertibleCurveDegree_eq_curveDegree_one k p hdim L,
    invertibleCurveDegree_eq_zero_of_discreteTopology k p hdim L]

/-- **Equation 0BRY for an invertible module on a scheme of dimension at most zero**, both sides
being zero. -/
public theorem curveDegree_eq_curveChernDegree_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    curveDegree k p hdim L 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) := by
  rw [curveDegree_eq_zero_of_isInvertible_of_topologicalKrullDim_le_zero k p hdim hdim0 L,
    curveChernDegree_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0]

/-! ### The first Chern class of `ℰ` itself -/

/-- **The first Chern class component rule of a finite locally free module `ℰ` of constant rank
`r`**, read off the Chern classes of Stacks 02U0.

At `r ≥ 1` this is `Stacks.Chow.firstChernComponentCycleRuleOfRank`: on an integral closed
subscheme `W ⊆ X` of delta-dimension one it is the cycle representing `c₁(ℰ|_W) ∩ [W]` that the
datum `chern` of Stacks 02U0 supplies. At `r = 0` it is
`Stacks.Chow.trivialChernComponentCycleRule`. -/
public def curveFirstChernRule (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r) :
    FirstChernComponentCycleRule (fieldChowSituation k) p 0 :=
  if hr : 0 < r then
    firstChernComponentCycleRuleOfRank (fieldChowSituation k) p E r
      (fun g => isFiniteLocallyFreeOfRank_pullback g E r) chern hr 0
  else trivialChernComponentCycleRule (fieldChowSituation k) p 0

/-- **The integer `deg(c₁(ℰ) ∩ [X]_1)`** of equations 0BRY and 0BRZ, for a finite locally free
module `ℰ` of constant rank `r` on a proper scheme of dimension at most one over a field: the
degree of the zero cycle `c₁(ℰ) ∩ [X]_1` at the component rule of `ℰ`. -/
public def curveChernDegreeOfModule (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r) : ℤ :=
  curveChernDegree k p hdim (curveFirstChernRule k p E r chern)

/-- At positive rank the component rule of `ℰ` is the one the Chern classes of Stacks 02U0 give,
so `deg(c₁(ℰ) ∩ [X]_1)` is the degree of the cap product at that rule. -/
public theorem curveChernDegreeOfModule_eq_curveChernDegree (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r) (hr : 0 < r) :
    curveChernDegreeOfModule k p hdim E r chern =
      curveChernDegree k p hdim (firstChernComponentCycleRuleOfRank (fieldChowSituation k) p E r
        (fun g => isFiniteLocallyFreeOfRank_pullback g E r) chern hr 0) := by
  rw [curveChernDegreeOfModule, curveFirstChernRule, dite_eq_left hr]

/-- The first Chern class of a module of rank zero is zero, so `deg(c₁(ℰ) ∩ [X]_1)` vanishes
there. -/
@[simp] public theorem curveChernDegreeOfModule_rank_zero (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    (chern : ChernClassCycleRule (fieldChowSituation k) 0) :
    curveChernDegreeOfModule k p hdim E 0 chern = 0 := by
  rw [curveChernDegreeOfModule, curveFirstChernRule, dite_eq_right (Nat.lt_irrefl 0),
    curveChernDegree,
    firstChernClassCap_trivialChernComponentCycleRule]
  simp

/-- The degree of a finite locally free module of rank zero vanishes. -/
@[simp] public theorem curveDegree_rank_zero (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] :
    curveDegree k p hdim E 0 = 0 := by
  have hz : Limits.IsZero E :=
    Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero E inferInstance
  have hterm : ∀ n : ℕ,
      (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k p E n) : ℤ) = 0 := by
    intro n
    have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_of_isZero k p hz n)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  rw [curveDegree]
  simp [hterm]

/-- **Equation 0BRY at rank zero**: for a finite locally free module of rank zero, both its
degree and the degree of `c₁(ℰ) ∩ [X]_1` are zero. -/
public theorem curveDegree_eq_curveChernDegreeOfModule_rank_zero
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    (chern : ChernClassCycleRule (fieldChowSituation k) 0) :
    curveDegree k p hdim E 0 = curveChernDegreeOfModule k p hdim E 0 chern := by
  rw [curveDegree_rank_zero, curveChernDegreeOfModule_rank_zero]

/-- **The reduction of the degree formula to the one-dimensional components, at the Stacks 02U0
datum of `ℰ`**: the degree of a finite locally free module of constant rank is the degree of
`c₁(ℰ) ∩ [X]_1` read off that datum, over a presentation of the fundamental one-cycle whose
component cycles compute the component degrees of `ℰ`. -/
public theorem curveDegree_eq_curveChernDegreeOfModule (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    {J : Type u} [Fintype J] (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension (fieldChowSituation k) ((W j).subschemeι ≫ p)
      = ((1 : ℤ) : EInt))
    (n : J → ℤ)
    (hpres : ∀ x : X,
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1).1 x =
        ∑ᶠ j : J, n j *
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (W j).subschemeι 1).1 x)
    (d : J → ℤ) (hcomponents : curveDegree k p hdim E r = ∑ j : J, n j * d j)
    (hintegral : ∀ j, d j = cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
      (firstChernComponentCycle (fieldChowSituation k) p 0 (curveFirstChernRule k p E r chern)
        (W j) (hW j) (hDim j))) :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r chern :=
  curveDegree_eq_curveChernDegree k p hdim E r (curveFirstChernRule k p E r chern) W hW hDim n
    hpres d hcomponents hintegral

/-- **Riemann-Roch, equation 0BRZ.** On a proper scheme of dimension at most one over a field,
if the degree of a finite locally free module `ℰ` of constant rank `r` is the degree of the zero
cycle `c₁(ℰ) ∩ [X]_1` (equation 0BRY, the hypothesis `hdegree`), then the Euler characteristic of
`ℰ` is that degree plus `r` times the Euler characteristic of the structure sheaf:

`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_eq_curveChernDegreeOfModule_add
    (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    (hdegree : curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r chern) :
    eulerCharacteristic k p E =
      curveChernDegreeOfModule k p hdim E r chern +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegree_add k p hdim E r (curveFirstChernRule k p E r chern)
    hdegree

/-- **Riemann-Roch, equation 0BRZ, for an invertible module.** For an invertible `𝒪_X`-module `ℒ`
with component rule `Stacks.Chow.firstChernComponentCycleRule`, if equation 0BRY holds for `ℒ`
(the hypothesis `hdegree`), then

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (hdegree : curveDegree k p hdim L 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L)) :
    eulerCharacteristic k p L =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  simpa using eulerCharacteristic_eq_curveChernDegree_add k p hdim L 1
    (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) hdegree

/-! ### Equation 0BRZ at rank zero and in dimension zero -/

/-- **Equation 0BRZ at rank zero**: for a finite locally free module `ℰ` of rank zero,
`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + 0 · χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_eq_curveChernDegreeOfModule_add_rank_zero
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (chern : ChernClassCycleRule (fieldChowSituation k) 0) :
    eulerCharacteristic k p E =
      curveChernDegreeOfModule k p hdim E 0 chern +
        ((0 : ℕ) : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegreeOfModule_add k p hdim E 0 chern
    (curveDegree_eq_curveChernDegreeOfModule_rank_zero k p hdim E chern)

/-- **Riemann-Roch, equation 0BRZ, for an invertible module on a scheme of dimension at most
zero**:

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`. -/
public theorem
    eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k p L =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible k p hdim L
    (curveDegree_eq_curveChernDegree_of_isInvertible_of_topologicalKrullDim_le_zero
      k p hdim hdim0 L)

/-! ### Dimension at most zero at the first Chern class of `ℰ` -/

/-- **On a scheme of dimension at most zero `deg(c₁(ℰ) ∩ [X]_1)` vanishes, at every rank and at
every datum of Stacks 02U0.** -/
public theorem curveChernDegreeOfModule_eq_zero_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r) :
    curveChernDegreeOfModule k p hdim E r chern = 0 :=
  curveChernDegree_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0 _

/-- **On a scheme of dimension at most zero the two readings of `deg(c₁(ℒ) ∩ [X]_1)` for an
invertible module `ℒ` agree**: the one read off the Chern classes of Stacks 02U0 at rank one,
`AlgebraicGeometry.curveChernDegreeOfModule`, and the one read off the first Chern class of
Stacks 02SO, `AlgebraicGeometry.curveChernDegree` at
`Stacks.Chow.firstChernComponentCycleRule`. -/
public theorem
    curveChernDegreeOfModule_eq_curveChernDegree_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    (chern : ChernClassCycleRule (fieldChowSituation k) 1) :
    curveChernDegreeOfModule k p hdim L 1 chern =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) := by
  rw [curveChernDegreeOfModule_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0 L 1 chern,
    curveChernDegree_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0]

/-- **Equation 0BRY at the Stacks 02U0 datum, for an invertible module on a scheme of dimension
at most zero**, both sides being zero. -/
public theorem
    curveDegree_eq_curveChernDegreeOfModule_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    (chern : ChernClassCycleRule (fieldChowSituation k) 1) :
    curveDegree k p hdim L 1 = curveChernDegreeOfModule k p hdim L 1 chern := by
  rw [curveDegree_eq_zero_of_isInvertible_of_topologicalKrullDim_le_zero k p hdim hdim0 L,
    curveChernDegreeOfModule_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0 L 1 chern]

/-- **Riemann-Roch, equation 0BRZ at the Stacks 02U0 datum, for an invertible module on a scheme
of dimension at most zero**:

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`,

where `c₁` is the one the datum of Stacks 02U0 supplies at rank one. -/
public theorem
eulerCharacteristic_eq_curveChernDegreeOfModule_add_of_isInvertible_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (chern : ChernClassCycleRule (fieldChowSituation k) 1) :
    eulerCharacteristic k p L =
      curveChernDegreeOfModule k p hdim L 1 chern +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  simpa using eulerCharacteristic_eq_curveChernDegreeOfModule_add k p hdim L 1 chern
    (curveDegree_eq_curveChernDegreeOfModule_of_isInvertible_of_topologicalKrullDim_le_zero
      k p hdim hdim0 L chern)

/-- **Equation 0BRY at the Stacks 02U0 datum, at arbitrary rank on a scheme of dimension at most
zero**, for a module `ℰ` with an isomorphism `ℰ ≅ 𝒪_X^{⊞ r}`. -/
public theorem
    curveDegree_eq_curveChernDegreeOfModule_of_iso_biprodPow_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    (e : E ≅ Scheme.Modules.biprodPow (X := X) (SheafOfModules.unit X.ringCatSheaf) r) :
    curveDegree k p hdim E r = curveChernDegreeOfModule k p hdim E r chern := by
  rw [curveDegree_eq_zero_of_iso_biprodPow k p hdim E r e,
    curveChernDegreeOfModule_eq_zero_of_topologicalKrullDim_le_zero k p hdim hdim0 E r chern]

/-- **Riemann-Roch, equation 0BRZ at the Stacks 02U0 datum, at arbitrary rank on a scheme of
dimension at most zero**, for a module `ℰ` with an isomorphism `ℰ ≅ 𝒪_X^{⊞ r}`:

`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + r · χ(X, 𝒪_X)`. -/
public theorem
eulerCharacteristic_eq_curveChernDegreeOfModule_add_of_iso_biprodPow_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ 1) (hdim0 : topologicalKrullDim X ≤ 0) (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (chern : ChernClassCycleRule (fieldChowSituation k) r)
    (e : E ≅ Scheme.Modules.biprodPow (X := X) (SheafOfModules.unit X.ringCatSheaf) r) :
    eulerCharacteristic k p E =
      curveChernDegreeOfModule k p hdim E r chern +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegreeOfModule_add k p hdim E r chern
    (curveDegree_eq_curveChernDegreeOfModule_of_iso_biprodPow_of_topologicalKrullDim_le_zero
      k p hdim hdim0 E r chern e)

end AlgebraicGeometry

end
