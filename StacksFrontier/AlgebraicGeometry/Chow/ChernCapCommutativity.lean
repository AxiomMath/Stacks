module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap

/-!
# Commutativity of two first Chern class cap products

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `L` and `N` be invertible modules on `X`. Stacks 02TJ is the commutativity

  `c₁(L) ∩ c₁(N) ∩ α = c₁(N) ∩ c₁(L) ∩ α`  in  `A_k(X)`,  for `α ∈ A_{k+2}(X)`,

and the source proves it by writing `α = ∑_j m_j [Z_j]` over a locally finite family of integral
closed subschemes of delta-dimension `k + 2`, pushing both iterated cap products through the
proper morphism `⨿_j Z_j ⟶ X` by two applications of Stacks 02SU, and invoking the case of an
integral `X` with `α = [X]`, which is Stacks 02TH.

Both sides are composites of two coefficientwise extensions of a rule on integral components, so
the passage from the integral case to all cycles is
`Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply`: it exhibits each composite as a single
locally finite sum over the components of `α`, after which the identity is a pointwise statement
about the four component rules. This replaces the
disjoint-union reduction of the source by coefficientwise bookkeeping over the components of `α`,
exactly as `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` does for Stacks 02SU itself.
The reduction the source performs is available separately as
`Stacks.Chow.firstChernCapRule_extendCycleGroup_comm_of_properPushforward`, which pushes the two
iterated cap products through an arbitrary proper morphism by two applications of Stacks 02SU.

## Main definitions

* `Stacks.Chow.FirstChernCapCommutesOnComponents` — the commutativity of Stacks 02TJ on the
  fundamental cycle of a single integral component, which is the case the source reduces to.

## Main results

* `Stacks.Chow.firstChernCapCommutesOnComponents_of_components` — that hypothesis restated on
  integral closed subschemes rather than on points.
* `Stacks.Chow.firstChernCapRule_extendCycleGroup_comm` — **Stacks 02TJ** at the level of
  **cycles**: the two iterated cap product cycles agree.
* `Stacks.Chow.firstChernClassCapOnChow_comm` — **Stacks 02TJ**: the two iterated operations on
  Chow groups agree.
* `Stacks.Chow.firstChernCapRule_extendCycleGroup_comm_of_properPushforward` — the reduction step
  of the source: commutativity for a cycle pushed forward along a proper morphism follows from
  commutativity upstairs, by two applications of Stacks 02SU.

## Implementation notes

### Degrees

The source writes the input degree as `k + 2` and the output degree as `k`. Here the input degree
is `k + 1 + 1`, so that the two successive degree-lowering operations compose without a transport
along `(k + 2) - 1 = k + 1`; this is the convention of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity`, where the integral case is stated
with the hypothesis `dim_δ(X) = k + 2` and the conclusion in `A_k(X)`.

### The parameters threaded, and why

In this repository the cap product of Stacks 02SO is built from an explicit component rule rather
than from an invertible module — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass`. So the two invertible modules of the source
enter only through component rules, and each of them is needed in both degrees in which it is
capped with: `chernL` and `chernN` in degree `k`, `chernLUp` and `chernNUp` in degree `k + 1`.
Descending each operation to Chow groups needs in addition the statement of Stacks 02TI in the
relevant degree, which is a hypothesis in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent`.

### The hypothesis on integral components, and why it is indispensable

`Stacks.Chow.FirstChernCapCommutesOnComponents` says that the two iterated cap product cycles
agree on the fundamental cycle of each integral component of `X` of delta-dimension `k + 1 + 1`.
That is the case the source reduces to, and the theorem extends it to every cycle; the extension
is not formal, since a cycle is a *locally* finite sum of components and both composites are
double locally finite sums which have to be exchanged.

It cannot be dropped. All four operations are built from arbitrary component rules, and four
unrelated rules satisfy no identity: taking `chernL = 0` and `chernN` with a nonzero value
already makes the conclusion fail.

It is, however, genuinely stronger than the integral case of the source, and this is the one
place where the statements below are not a mere generalization of Stacks 02TJ. Stacks 02TH, which
is `Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`, asserts the equality of the
two *classes* in `A_k(W)` on an integral `W`, whereas the hypothesis here asks for the equality
of the two *cycles* on `X`. A class-level hypothesis would not extend to all cycles by the argument
below: the difference of the two iterated cap product cycles of `α` is a locally finite sum of the
differences attached to the components of `α`, and rational equivalence to zero is stable under
such sums only when the witnessing families are jointly locally finite, which
`Stacks.Chow.rationallyEquivalentToZeroWithin_finsum` requires as the extra datum of a carrier for
each witness.

### No `@[stacks 02TJ]`

The tag's statement is the unconditional identity for two invertible modules. Every declaration
below carries four component rules standing in for Stacks 02SO, the integral-component hypothesis
standing in for Stacks 02TH, and — for the statements on Chow groups — four instances of Stacks
02TI. So none of them is literally the tagged statement, and no `@[stacks]` attribute is placed
in this file.

## References

* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (chernL chernN : FirstChernComponentCycleRule C p k)
  (chernLUp chernNUp : FirstChernComponentCycleRule C p (k + 1))

/-! ### Stacks 02TJ on integral components -/

/-- **Stacks 02TJ on integral components.** The assertion that for every integral component of
`X` of delta-dimension `k + 1 + 1` — equivalently, for every point of relative dimension
`k + 1 + 1` — the identity `c₁(L) ∩ c₁(N) ∩ [W] = c₁(N) ∩ c₁(L) ∩ [W]` holds at the level of
cycles.

This is the case the source reduces to, from which the general case follows by the component
formula; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativity`. -/
def FirstChernCapCommutesOnComponents : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 + 1 →
    (firstChernCapRule C p k chernL).extendCycleGroup
        (firstChernComponentCycleAt C p (k + 1) chernNUp x) =
      (firstChernCapRule C p k chernN).extendCycleGroup
        (firstChernComponentCycleAt C p (k + 1) chernLUp x)

/-- The commutativity of Stacks 02TJ on integral components, restated on integral closed
subschemes of `X` instead of on points: the two are the same datum, by
`Stacks.Chow.integralComponentAt_genericPointOf`. -/
theorem firstChernCapCommutesOnComponents_of_components
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
      (firstChernCapRule C p k chernL).extendCycleGroup
          (firstChernComponentCycle C p (k + 1) chernNUp W hW hDim) =
        (firstChernCapRule C p k chernN).extendCycleGroup
          (firstChernComponentCycle C p (k + 1) chernLUp W hW hDim)) :
    FirstChernCapCommutesOnComponents C p k chernL chernN chernLUp chernNUp := by
  intro x hdim
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C p x, hdim]
  have hx : genericPointOf (integralComponentAt x) hW = x := genericPointOf_integralComponentAt x
  have h' := h (integralComponentAt x) hW hDim
  rw [← firstChernComponentCycleAt_genericPointOf C p (k + 1) chernNUp _ hW hDim,
    ← firstChernComponentCycleAt_genericPointOf C p (k + 1) chernLUp _ hW hDim, hx] at h'
  exact h'

/-! ### Stacks 02TJ -/

/-- **Stacks 02TJ, at the level of cycles.** Granted the identity on integral components, the
cycles representing `c₁(L) ∩ c₁(N) ∩ α` and `c₁(N) ∩ c₁(L) ∩ α` are equal for every
`(k+1+1)`-cycle `α`.

This is sharper than the statement of the source, which is an equality of classes in `A_k(X)`.
Both sides are composites of two coefficientwise extensions, so
`Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply` puts both into the shape
`∑_x α(x) · (something attached to x)`, after which the hypothesis applies term by term. Only the
points carrying a nonzero coefficient of `α` are compared, and those have relative dimension
`k + 1 + 1` because `α` is a `(k+1+1)`-cycle. -/
theorem firstChernCapRule_extendCycleGroup_comm
    (hcomp : FirstChernCapCommutesOnComponents C p k chernL chernN chernLUp chernNUp)
    (α : CycleGroup C p (k + 1 + 1)) :
    (firstChernCapRule C p k chernL).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernNUp).extendCycleGroup α) =
      (firstChernCapRule C p k chernN).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernLUp).extendCycleGroup α) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have key : ∀ (chernOut : FirstChernComponentCycleRule C p k)
      (chernIn : FirstChernComponentCycleRule C p (k + 1)),
      ((firstChernCapRule C p k chernOut).extendCycleGroup
          ((firstChernCapRule C p (k + 1) chernIn).extendCycleGroup α)).1 y =
        ∑ᶠ x : X, α.1 x *
          ((firstChernCapRule C p k chernOut).extendCycleGroup
            (firstChernComponentCycleAt C p (k + 1) chernIn x)).1 y := by
    intro chernOut chernIn
    rw [show ((firstChernCapRule C p k chernOut).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernIn).extendCycleGroup α)).1 y =
      (firstChernCapRule C p k chernOut).toComponentRule.extendCoeff
        ((firstChernCapRule C p (k + 1) chernIn).toComponentRule.extendCycle
          (𝟙 X : X ⟶ X).continuous α.1) y from rfl,
      ComponentRule.extendCoeff_extendCycle_apply _ _ _ α.1 y]
    exact finsum_congr fun _ ↦ rfl
  rw [key chernL chernNUp, key chernN chernLUp]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [hcomp x ((mem_cyclesOfDimension_iff_forall_point C p (k + 1 + 1) α.1).1 α.2 x hx)]

/-- **Stacks 02TJ.** Intersecting successively with two first Chern classes is independent of the
order: `c₁(L) ∩ c₁(N) ∩ α = c₁(N) ∩ c₁(L) ∩ α` in `A_k(X)` for every `α ∈ A_{k+1+1}(X)`.

The four component rules, the four descent hypotheses of Stacks 02TI and the integral-component
identity are explicit parameters; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativity`. The identity holds already at the
level of cycles, which is `Stacks.Chow.firstChernCapRule_extendCycleGroup_comm`. -/
theorem firstChernClassCapOnChow_comm
    (hchernL : FirstChernClassCapFactorsThroughRationalEquivalence C p k chernL)
    (hchernN : FirstChernClassCapFactorsThroughRationalEquivalence C p k chernN)
    (hchernLUp : FirstChernClassCapFactorsThroughRationalEquivalence C p (k + 1) chernLUp)
    (hchernNUp : FirstChernClassCapFactorsThroughRationalEquivalence C p (k + 1) chernNUp)
    (hcomp : FirstChernCapCommutesOnComponents C p k chernL chernN chernLUp chernNUp)
    (α : chowGroup C p (k + 1 + 1)) :
    firstChernClassCapOnChow C p k chernL hchernL
        (firstChernClassCapOnChow C p (k + 1) chernNUp hchernNUp α) =
      firstChernClassCapOnChow C p k chernN hchernN
        (firstChernClassCapOnChow C p (k + 1) chernLUp hchernLUp α) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    change QuotientAddGroup.mk ((firstChernCapRule C p k chernL).extendCycleGroup
      ((firstChernCapRule C p (k + 1) chernNUp).extendCycleGroup β)) = _
    rw [firstChernCapRule_extendCycleGroup_comm C p k chernL chernN chernLUp chernNUp hcomp β]
    rfl

/-! ### The reduction along a proper morphism -/

section ProperPushforward

variable {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (q : Y ⟶ X) [IsProper q]
  (hq : q ≫ p = sY)
  (chernLY chernNY : FirstChernComponentCycleRule C sY k)
  (chernLYUp chernNYUp : FirstChernComponentCycleRule C sY (k + 1))

/-- **The reduction step of Stacks 02TJ.** If the two iterated cap product cycles agree on a
`(k+1+1)`-cycle `α'` on `Y`, then they agree on its proper pushforward to `X`.

This is the step the source performs with `Y = ⨿_j Z_j` the disjoint union of the integral closed
subschemes presenting `α`: each iterated cap product is pushed through `q` by two applications of
Stacks 02SU, in degrees `k + 1` and `k`, so both sides of the conclusion are the pushforwards of
the two sides upstairs. The compatibility of the component rules along `q` in each degree is the
hypothesis `Stacks.Chow.FirstChernCapCompatibleWithPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward`. -/
theorem firstChernCapRule_extendCycleGroup_comm_of_properPushforward
    (hcompL : FirstChernCapCompatibleWithPushforward C sY p q hq k chernLY chernL)
    (hcompN : FirstChernCapCompatibleWithPushforward C sY p q hq k chernNY chernN)
    (hcompLUp : FirstChernCapCompatibleWithPushforward C sY p q hq (k + 1) chernLYUp chernLUp)
    (hcompNUp : FirstChernCapCompatibleWithPushforward C sY p q hq (k + 1) chernNYUp chernNUp)
    (α : CycleGroup C sY (k + 1 + 1))
    (hα : (firstChernCapRule C sY k chernLY).extendCycleGroup
        ((firstChernCapRule C sY (k + 1) chernNYUp).extendCycleGroup α) =
      (firstChernCapRule C sY k chernNY).extendCycleGroup
        ((firstChernCapRule C sY (k + 1) chernLYUp).extendCycleGroup α)) :
    (firstChernCapRule C p k chernL).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernNUp).extendCycleGroup
          (properPushforward C sY p q hq (k + 1 + 1) α)) =
      (firstChernCapRule C p k chernN).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernLUp).extendCycleGroup
          (properPushforward C sY p q hq (k + 1 + 1) α)) := by
  have step : ∀ (chernOut : FirstChernComponentCycleRule C p k)
      (chernIn : FirstChernComponentCycleRule C p (k + 1))
      (chernOutY : FirstChernComponentCycleRule C sY k)
      (chernInY : FirstChernComponentCycleRule C sY (k + 1)),
      FirstChernCapCompatibleWithPushforward C sY p q hq k chernOutY chernOut →
      FirstChernCapCompatibleWithPushforward C sY p q hq (k + 1) chernInY chernIn →
      (firstChernCapRule C p k chernOut).extendCycleGroup
          ((firstChernCapRule C p (k + 1) chernIn).extendCycleGroup
            (properPushforward C sY p q hq (k + 1 + 1) α)) =
        properPushforward C sY p q hq k
          ((firstChernCapRule C sY k chernOutY).extendCycleGroup
            ((firstChernCapRule C sY (k + 1) chernInY).extendCycleGroup α)) := by
    intro chernOut chernIn chernOutY chernInY hOut hIn
    rw [← properPushforward_firstChernCapRule_extendCycleGroup C sY p q hq (k + 1) chernInY
      chernIn hIn α,
      ← properPushforward_firstChernCapRule_extendCycleGroup C sY p q hq k chernOutY chernOut
        hOut ((firstChernCapRule C sY (k + 1) chernInY).extendCycleGroup α)]
  rw [step chernL chernNUp chernLY chernNYUp hcompL hcompNUp,
    step chernN chernLUp chernNY chernLYUp hcompN hcompLUp, hα]

end ProperPushforward

end Stacks.Chow

end
