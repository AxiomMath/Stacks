module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminantModification
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochDeterminant
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksCore.Tactic.StacksAttribute

/-!
# Riemann-Roch on a proper scheme of dimension at most one, through the determinant

Let `k` be a field, `X` a proper scheme over `k` of dimension at most one and `ℰ` a finite locally
free `𝒪_X`-module of constant rank `r`. Then

`deg(ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1)`

and

`χ(X, ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`,

where `c₁(⋀ʳ ℰ)` is the first Chern class of the determinant,
`AlgebraicGeometry.curveChernDegreeDet`. Along the way, `deg(ℰ) = deg(⋀ʳ ℰ)`, the first equality of
[Stacks, Tag 0DJ5], holds on such an `X` at every constant rank.

## Main results

* `AlgebraicGeometry.curveDegree_exteriorPower_zero`: `⋀⁰ ℰ` has degree zero.
* `AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_forall_isCurve`: the first
  equality of [Stacks, Tag 0DJ5] on `X`, from the same on every proper curve.
* `AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_isProper`: the first equality of
  [Stacks, Tag 0DJ5] on `X`, at every constant rank.
* `AlgebraicGeometry.curveDegree_eq_curveChernDegreeDet`: `deg(ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1)` at
  every constant rank.
* `AlgebraicGeometry.eulerCharacteristic_eq_curveChernDegreeDet_add`:
  `χ(X, ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)` at every constant rank.

## References

* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- **The zeroth exterior power has degree zero**: `deg(⋀⁰ ℰ) = 0`, the degree taken at rank
one. -/
theorem curveDegree_exteriorPower_zero (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower E ((0 : ℕ) : ℤ)) 1] :
    curveDegree k p hdim (Scheme.Modules.exteriorPower E ((0 : ℕ) : ℤ)) 1 = 0 := by
  have := SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  have e : Scheme.Modules.exteriorPower E ((0 : ℕ) : ℤ) ≅ SheafOfModules.unit X.ringCatSheaf :=
    (SheafOfModules.algebras _ E).exteriorPieceIso_zero
  rw [curveDegree_eq_of_iso k p hdim 1 e]
  unfold curveDegree
  simp

/-- **The first equality of [Stacks, Tag 0DJ5] on a proper scheme of dimension at most one, from
the same on proper curves.** If every finite locally free module of positive constant rank on
every proper curve over `k` has the degree of its top exterior power, then so does every such
module on `X`. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_forall_isCurve
    (hcurve : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) [IsCurve k q] [IsProper q]
      (hY : topologicalKrullDim Y ≤ 1) (n : ℕ) (F : Y.Modules)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)],
      curveDegree k q hY F (n + 1) =
        @curveDegree k _ Y q _ hY (Scheme.Modules.exteriorPower F ((n + 1 : ℕ) : ℤ)) 1
          (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F (n + 1)))
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    curveDegree k p hdim E (n + 1) =
      @curveDegree k _ X p _ hdim (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)) := by
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)
  refine curveDegree_eq_curveDegree_exteriorPower_of_componentDegree k p hdim E (n + 1)
    fun ξ => ?_
  have := isProper_reducedComponentι_comp k p ξ
  have := isCurve_reducedComponentι_comp k p ξ
  have := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E (n + 1)
  have := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ
    (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) (n + 1)
  unfold componentDegree
  rw [hcurve _ (reducedComponentι X ξ ≫ p) _ n]
  exact curveDegree_eq_of_iso k _ _ 1
    (Scheme.Modules.exteriorPowerPullbackIso (reducedComponentι X ξ) E _).symm

/-- **The first equality of [Stacks, Tag 0DJ5] on a proper scheme of dimension at most one**:
`deg(ℰ) = deg(⋀ⁿ ℰ)` for `ℰ` finite locally free of constant rank `n`, every `n`. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_isProper (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    curveDegree k p hdim E n =
      @curveDegree k _ X p _ hdim (Scheme.Modules.exteriorPower E (n : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n) := by
  rcases n with _ | n
  · have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 0
    rw [curveDegree_rank_zero, curveDegree_exteriorPower_zero]
  · exact curveDegree_eq_curveDegree_exteriorPower_of_forall_isCurve k p
      (fun _ q _ _ hY m F _ => curveDegree_eq_curveDegree_exteriorPower_of_isCurve k q hY m F)
      hdim n E

/-- **The degree of `ℰ` is the degree of the first Chern class of its determinant**: on a proper
scheme `X` of dimension at most one over a field `k`, a finite locally free `𝒪_X`-module `ℰ` of
constant rank `r` satisfies

`deg(ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1)`,

where `deg(ℰ) = χ(X, ℰ) - r · χ(X, 𝒪_X)` is `AlgebraicGeometry.curveDegree` ([Stacks, Tag 0AYR])
and `c₁(⋀ʳ ℰ)` is the first Chern class of the determinant,
`AlgebraicGeometry.curveChernDegreeDet`. `X` is not assumed integral, reduced, or of dimension
exactly one, and every rank is covered, rank zero included. -/
theorem curveDegree_eq_curveChernDegreeDet (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    curveDegree k p hdim E r = curveChernDegreeDet k p hdim E r :=
  curveDegree_eq_curveChernDegreeDet_of_curveDegree_exteriorPower k p hdim E r
    (curveDegree_eq_curveDegree_exteriorPower_of_isProper k p hdim r E)

/-- **The Riemann-Roch formula with `c₁` read off the determinant**: on a proper scheme `X` of
dimension at most one over a field `k`, a finite locally free `𝒪_X`-module `ℰ` of constant rank `r`
satisfies

`χ(X, ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`,

with `c₁(⋀ʳ ℰ)` the first Chern class of the invertible module `⋀ʳ ℰ` ([Stacks, Tag 02SO]),
`AlgebraicGeometry.curveChernDegreeDet`, as in `curveDegree_eq_curveChernDegreeDet`. `X` is not
assumed integral, reduced, or of dimension exactly one, and every rank is covered, rank zero
included. The Euler characteristics ([Stacks, Tag 0BEJ]) are taken at the coherence of `ℰ` and of
`𝒪_X` that properness over `k` provides. -/
@[sga "6 XIII 4.6" "more general"]
theorem eulerCharacteristic_eq_curveChernDegreeDet_add (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k p E r
    letI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
    eulerCharacteristic k p E =
      curveChernDegreeDet k p hdim E r +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  have h := curveDegree_eq_curveChernDegreeDet k p hdim E r
  rw [Stacks.AlgebraicGeometry.CurveEulerBridge.curveDegree_eq_eulerCharacteristic_sub] at h
  linarith

end AlgebraicGeometry

end
