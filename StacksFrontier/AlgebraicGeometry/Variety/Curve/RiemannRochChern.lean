module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochGenuine
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Riemann-Roch on a proper scheme of dimension at most one, with the Chern class of Stacks 02U0

Let `k` be a field, `X` a proper scheme over `k` of dimension at most one and `ℰ` a finite locally
free `𝒪_X`-module of constant rank `r`. Equation [Stacks, Tag 0BRZ] is

  `χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`,

with `c₁(ℰ) ∩ -` the intersection with the first Chern class of [Stacks, Tag 02U5] — on an
integral closed subscheme `i : W ⟶ X` of dimension one, `i_*(c₁(i^*ℰ) ∩ [W])` with the class of
[Stacks, Tag 02U0] read off the projective space bundle formula [Stacks, Tag 02TX] — applied to
the fundamental one-cycle `[X]_1` of [Stacks, Tag 02QU], and `deg` the degree of zero cycles of
[Stacks, Tag 0AZ1].

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add`: the displayed
  formula for `ℰ` of every constant rank.

## References

* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- **Riemann-Roch**: on a proper scheme `X` of dimension at most one over a field `k`, a finite
locally free `𝒪_X`-module `ℰ` of constant rank `r` satisfies

`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`.

Here `c₁(ℰ) ∩ -` is intersection with the first Chern class of [Stacks, Tag 02U5],
`Stacks.Chow.GenuineChern.firstChernCapOnCycles`: on an integral closed subscheme `i : W ⟶ X` it is
`i_*(c₁(i^*ℰ) ∩ [W])` with the class of [Stacks, Tag 02U0] read off the projective space bundle
formula, extended coefficientwise; in rank zero it is zero. It is applied to the fundamental
one-cycle `[X]_1` ([Stacks, Tag 02QU]), and `deg` is the degree of zero cycles of
[Stacks, Tag 0AZ1]. `X` is not assumed integral, reduced, or of dimension exactly one, and every
rank is covered, rank zero included. The Euler characteristics ([Stacks, Tag 0BEJ]) are taken at
the coherence of `ℰ` and of `𝒪_X` that properness over `k` provides. -/
@[stacks 0BRZ, sga "6 XIII 4.6" "more general"]
theorem eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k p E r
    letI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
    eulerCharacteristic k p E =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
          (IsLocalRing.closedPoint k)
          (chowGroupCast (fieldChowSituation k) p (show (1 : ℤ) - 1 = 0 by simp)
            (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) p E r 1
              (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1))) +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  have h := chowDegree_firstChernCapOnCycles_fundamental_eq_curveDegree k p hdim E r
  rw [Stacks.AlgebraicGeometry.CurveEulerBridge.curveDegree_eq_eulerCharacteristic_sub] at h
  linarith

end AlgebraicGeometry

end
