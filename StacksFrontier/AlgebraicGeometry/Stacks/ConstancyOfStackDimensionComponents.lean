module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ConstancyOfStackDimension

/-!
# Comparing the local dimension of a chart along a connected set

The proof of Stacks 0DRX reduces the constancy of `x ↦ dim_x(𝒳)` to the local constancy of
`u ↦ dim_u(U)` along a smooth surjective scheme chart `U ⟶ 𝒳`, and proves the latter by
comparing the irreducible components of `U` through a point. The comparison step is the one with
mathematical content, and it is proved here.

Let `V` and `W` be nonempty open subsets of the chart on which the local dimension of `U` takes
the constant values `a` and `b`, and suppose both lie in one preconnected subset of `U`. Then
`a = b`. The images of `V` and `W` in `|𝒳|` are nonempty open, a smooth 1-morphism being open on
points, so they meet because `|𝒳|` is irreducible; at a common image point the dimension formula
of Stacks 0DRJ reads `dim_x(𝒳)` as `a` minus the relative dimension at a point of `V` and as `b`
minus the relative dimension at a point of `W`; and those two relative dimensions agree because
the relative dimension is locally constant and both points lie in the preconnected set.

In the source this is applied with `V = T_i \ ⋃_{i' ≠ i} T_{i'}` and `W = T_j \ ⋃_{i' ≠ j}
T_{i'}` the separating opens of two irreducible components through a common point `u`, and with
`C = T_i ∪ T_j`, which is preconnected because the two components are irreducible and share `u`.
The conclusion is then that the two components have the same dimension, which is what makes
`dim_u(U)` locally constant.

## Main results

* `AlgebraicGeometry.Stack.dimensionSubNat_left_injective`: `δ ↦ δ - d` is injective.
* `AlgebraicGeometry.Stack.topologicalKrullDimAt_chart_eq_of_isPreconnected`: the comparison.

## Implementation notes

No `@[stacks 0DRX]` and no `@[stacks 0DS4]` attribute is attached. The hypothesis `hr` is the
local constancy of the relative dimension of the chart, which is Stacks 0DRQ (2) for a stack
target and is not available here, so anything proved from it would be a conditional
registration. This file carries it explicitly, exactly as
`AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducible_chart` does, so that landing
Stacks 0DRQ discharges it in one step.

Both `hr` and the irreducibility of `|𝒳|` are genuinely used, and neither can be dropped. It is
*not* true that all irreducible components of a smooth surjective chart have the same dimension:
for `𝒳` a point, `U = Spec k ⊔ 𝐀¹_k ⟶ 𝒳` is smooth and surjective, and `dim_u(U)` is `0` on one
piece and `1` on the other. What the comparison needs, and what the two components through a
common point supply, is the preconnected set `C`; the conclusion of Stacks 0DRX is local
constancy, not constancy, of `dim_u(U)`.

Surjectivity of the chart is not a hypothesis: the argument needs only that the chart is open on
points, which is smoothness.

## References

* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRT](https://stacks.math.columbia.edu/tag/0DRT)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Subtracting a fixed natural number from a dimension in `[-∞, ∞]` is injective: the three
cases `⊥`, a natural number and `⊤` of the source land in the three disjoint cases `⊥`, an
integer and `⊤` of the target, and on natural numbers `m ↦ m - d` is injective. -/
theorem dimensionSubNat_left_injective (d : ℕ) :
    Function.Injective fun δ : WithBot ℕ∞ => dimensionSubNat δ d := by
  have hbot : dimensionSubNat (⊥ : WithBot ℕ∞) d = (⊥ : EInt) := rfl
  have htop : dimensionSubNat ((⊤ : ℕ∞) : WithBot ℕ∞) d = (⊤ : EInt) := rfl
  have hcoe : ∀ m : ℕ, dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d =
      (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := fun _ => rfl
  intro δ δ' hδ
  have h : dimensionSubNat δ d = dimensionSubNat δ' d := hδ
  induction δ using WithBot.recBotCoe <;> induction δ' using WithBot.recBotCoe <;>
    (try cases ‹ℕ∞› using ENat.recTopCoe) <;> (try cases ‹ℕ∞› using ENat.recTopCoe) <;>
    simp only [hbot, htop, hcoe] at h <;>
    first
    | rfl
    | exact absurd h (WithBotTop.coe_ne_bot _).symm
    | exact absurd h (WithBotTop.coe_ne_bot _)
    | exact absurd h (WithBotTop.coe_ne_top _).symm
    | exact absurd h (WithBotTop.coe_ne_top _)
    | exact absurd h WithBotTop.top_ne_bot
    | exact absurd h WithBotTop.top_ne_bot.symm
    | (have := WithBotTop.coe_injective h; simp; omega)

/-- **The comparison step of Stacks 0DRX.** Let `𝒳` be a locally Noetherian algebraic stack with
`|𝒳|` irreducible and let `f : U ⟶ 𝒳` be a smooth chart by a scheme of the site along which the
dimension formula of Stacks 0DRJ holds with relative dimension `r`. If `V` and `W` are nonempty
open subsets of `U` lying in one preconnected subset of `U`, and the local dimension of `U` is
constantly `a` on `V` and constantly `b` on `W`, then `a = b`.

The hypothesis `hr` is Stacks 0DRQ (2) for a stack target. -/
theorem topologicalKrullDimAt_chart_eq_of_isPreconnected
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val))
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (r : (BigFppfOver.toScheme B S hS).obj U → ℕ) (hr : IsLocallyConstant r)
    (hformula : ∀ u : (BigFppfOver.toScheme B S hS).obj U,
      dimensionAtPoint B S hS 𝒳 h𝒳 (AlgebraicStacks.chartPointMap B S hS U 𝒳 f u) =
        dimensionSubNat
          (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u) (r u))
    (C V W : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hC : _root_.IsPreconnected C) (hVC : V ⊆ C) (hWC : W ⊆ C)
    (hVopen : IsOpen V) (hWopen : IsOpen W) (hVne : V.Nonempty) (hWne : W.Nonempty)
    (a b : WithBot ℕ∞)
    (hV : ∀ v ∈ V, topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) v = a)
    (hW : ∀ w ∈ W, topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) w = b) :
    a = b := by
  let _ := pointTopology B S hS 𝒳.val
  have _ := h𝒳Irreducible
  set π := AlgebraicStacks.chartPointMap B S hS U 𝒳 f with hπ
  -- A smooth 1-morphism is open on points, so the two images are nonempty opens of `|𝒳|`.
  have hopen := AlgebraicStacks.isOpenMap_chartPointMap B S hS U 𝒳 f hsm
  -- Irreducibility of `|𝒳|` makes them meet.
  obtain ⟨x, -, hxV, hxW⟩ :=
    (IrreducibleSpace.isIrreducible_univ
        (points B S hS 𝒳.val.val 𝒳.val.property)).isPreirreducible
      (π '' V) (π '' W) (hopen V hVopen) (hopen W hWopen)
      (by obtain ⟨v, hv⟩ := hVne; exact ⟨π v, Set.mem_univ _, v, hv, rfl⟩)
      (by obtain ⟨w, hw⟩ := hWne; exact ⟨π w, Set.mem_univ _, w, hw, rfl⟩)
  obtain ⟨v, hvV, hvx⟩ := hxV
  obtain ⟨w, hwW, hwx⟩ := hxW
  -- The relative dimension agrees at the two points, both lying in the preconnected set.
  have hrvw : r v = r w := hr.apply_eq_of_isPreconnected hC (hVC hvV) (hWC hwW)
  -- The dimension formula at each of them computes `dim_x(𝒳)`.
  have hfv := hformula v
  have hfw := hformula w
  rw [hvx, hV v hvV] at hfv
  rw [hwx, hW w hwW, ← hrvw] at hfw
  exact dimensionSubNat_left_injective (r v) (hfv.symm.trans hfw)

end AlgebraicGeometry.Stack

end
