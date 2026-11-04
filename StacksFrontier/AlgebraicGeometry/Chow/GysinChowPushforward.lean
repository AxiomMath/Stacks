module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier

/-!
# The Gysin homomorphism on a component contained in the zero scheme

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible module on `X` and let `s ∈ Γ(X, L)` be a global section with
zero scheme `D = Z(s)`. Stacks 02T8 prescribes the Gysin map `Z_{k+1}(X) ⟶ A_k(D)` on integral
components by two rules, and `StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction` proves the
rule for a component `W` *not* contained in `D`. This file proves the remaining one — for `W`
contained in `D` the value is the first Chern class of `L|_W` pushed forward into `D` — and
defines the intersection with an effective Cartier zero scheme as a class on `X` itself.

## Main definitions

* `Stacks.Chow.effectiveCartierIntersection` — intersection with an effective Cartier zero
  scheme, as a homomorphism `Z_{k+1}(X) ⟶ A_k(X)`.

## Main results

* `Stacks.Chow.gysinHomomorphism_of_le` — the value of the Gysin map on an integral closed
  subscheme contained in the zero scheme.

## Implementation notes

### Both pushforwards are along closed immersions, so Stacks 02S2 is discharged

Both statements are expressed through proper pushforward on *Chow* groups,
`Stacks.Chow.properChowPushforward` (Stacks 0GU8), which carries the vanishing of Stacks 02S2 as
an explicit hypothesis `Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` because
Stacks 02S2 is not formalized in this repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow`.

That hypothesis is **not** carried here. Both morphisms involved are closed immersions — the
inclusion `W ⊆ D` of ideal sheaves and the inclusion `D ⊆ X` — and for a closed immersion Stacks
02S2 is proved outright in this repository, as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`
(`StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport`). So the hypothesis is supplied rather
than assumed, and the statements below are exactly those of Stacks 02T8 apart from the `chern`
parameter described next.

### The first Chern class is still an explicit parameter

As throughout `StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction`, the contained-component
class is the explicit argument `chern` of type `Stacks.Chow.FirstChernComponentClassRule`,
because Stacks 02SO is not available here: it rests on Stacks 02SJ, Stacks 02OZ and Stacks 0B8L,
none of which is formalized. Substituting `Stacks.Chow.firstChernComponentClass C p k L` for
`chern`, once Stacks 02SO lands, recovers the statements of Stacks 02T8 verbatim.

### No `@[stacks 02T8]`

With this file the covering set of Stacks 02T8 is complete up to that one parameter, but every
declaration of it still carries `chern`, so none is literally the tagged statement. Accordingly
no attribute is placed here either, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction`.

## References

* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)

/-- **Stacks 02T8.** The Gysin image of an integral closed subscheme contained in the zero
scheme is the proper pushforward into the zero scheme of the first Chern class of the restricted
invertible module.

The instance of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is discharged by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`, the
inclusion of `W` into the zero scheme being a closed immersion. -/
theorem gysinHomomorphism_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphism C p k L s chern
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      properChowPushforward C (W.subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h) (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Scheme.IdealSheafData.inclusion h) C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (by simp) k)
        (chern W hW hDim) := by
  have h₁ := (gysinRule C p k L s chern).extendCycleGroup_cycleAssociatedToClosedSubscheme
    W hW hDim
  change QuotientAddGroup.mk
    ((gysinRule C p k L s chern).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) = _
  rw [h₁, show (gysinRule C p k L s chern).cycle W hW hDim =
    gysinComponentCycle C p k L s chern W hW hDim from rfl,
    gysinComponentCycle_of_le C p k L s chern W hW hDim h]
  conv_rhs => rw [← Quotient.out_eq (chern W hW hDim)]
  rfl

/-- **Stacks 02T8.** Intersection with an effective Cartier zero scheme, read as a class on the
ambient scheme: the Gysin map of the zero scheme followed by proper pushforward of Chow classes
along its closed immersion into `X`.

As in `Stacks.Chow.gysinHomomorphism_of_le`, the instance of Stacks 02S2 that
`Stacks.Chow.properChowPushforward` requires is discharged, the zero scheme being a closed
subscheme of `X`. -/
def effectiveCartierIntersection
    (_hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s)) :
    CycleGroup C p (k + 1) →+ chowGroup C p k :=
  (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (Stacks.Divisors.zeroScheme X L s).subschemeι C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl k)).comp
    (gysinHomomorphism C p k L s chern)

/-- The intersection with an effective Cartier zero scheme is the pushforward of the Gysin class
of the cycle. -/
theorem effectiveCartierIntersection_apply
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s))
    (α : CycleGroup C p (k + 1)) :
    effectiveCartierIntersection C p k L s chern hD α =
      properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L s).subschemeι C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl k)
        (gysinHomomorphism C p k L s chern α) :=
  rfl

end Stacks.Chow

end
