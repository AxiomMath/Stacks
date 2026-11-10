module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent

/-!
# The self-intersection formula for the zero scheme of a section

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible module on `X` and let `s ∈ Γ(X, L)` be a global section with
zero scheme `i : D = Z(s) ⟶ X`. Stacks 0F95 computes the composite of the Gysin map of `D` with
the pushforward along `i`:

  `i^* i_* α = c₁(L|_D) ∩ α`  for a cycle `α` on `D`.

Every integral component of a cycle on `D` is contained in the zero scheme, so the Gysin map
evaluates on `i_* α` by the contained-component rule of Stacks 02T8 — the first Chern class of the
restriction of `L` — and that rule is the component rule of the cap product of Stacks 02SO on `D`.
This is the source's whole proof, and the content below is the passage from single components to an
arbitrary cycle: the two sides are locally finite sums over the components of `α`, reindexed over
the fibres of `i` on one side, and they are matched term by term.

## Degrees

The source writes the composite as `CH_k(D) ⟶ CH_{k-1}(D)`. Here the input degree is `k + 1` and
the output degree is `k`, so that the degree-lowering operations compose without casts, as in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`.

## Main definitions

* `Stacks.Chow.GysinSelfIntersectionOnComponents` — the agreement of the first Chern class
  component rule of `L` on `X` with that of `L|_D` on `D`, on the integral components of `D`.

## Main results

* `Stacks.Chow.gysinRule_extendCycleGroup_properPushforward_subschemeι` — Stacks 0F95 at the level
  of **cycles**: the Gysin cycle of `i_* α` is the first Chern class cycle of `α`.
* `Stacks.Chow.gysinHomomorphism_properPushforward_subschemeι` — the same identity read as an
  equality of classes in `A_k(D)`.
* `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_subschemeι` — **Stacks 0F95** for
  the Gysin map and the cap product of an invertible module, with `i_*` on cycles, with no
  hypothesis.
* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_properChowPushforward_subschemeι` — **Stacks
  0F95** as the composite `A_{k+1}(D) ⟶ A_k(D)` of the two descended operations, at any descent
  data.

## Implementation notes

### Stacks 02S2 is discharged, not assumed

`Stacks.Chow.properChowPushforward` (Stacks 0GU8) carries the vanishing of Stacks 02S2 as an
explicit hypothesis. The only morphism pushed along here is the closed immersion `i : D ⟶ X`, for
which Stacks 02S2 is proved outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`, so the
hypothesis is supplied rather than assumed.

### The component agreement, for arbitrary rules

For two arbitrary component rules the identity needs their agreement on the components of `D`.
In the source the two rules are the *same* rule: on an integral closed subscheme `W ⊆ D` the
contained-component rule of Stacks 02T8 reads `c₁(L|_W) ∩ [W]` and the component rule of the cap
product on `D` reads `c₁((L|_D)|_W) ∩ [W]`, and `L|_W = (L|_D)|_W`. In this repository both rules
are explicit parameters — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction` — so for arbitrary rules their agreement
enters the statement: two unrelated rules satisfy no identity, and taking the rule on `D` to be
zero and the rule on `X` to be nonzero on some component of `D` already makes the conclusion fail.

When both rules come from `L` the coefficientwise agreement is not available, for the reason
described in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible`:
`Stacks.Chow.gysinComponentCycle` pushes forward `Quotient.out` of the class the rule on `X`
supplies, an arbitrary representative, whereas the rule on `D` is cycle-valued, and nothing
relates the two cycles coefficientwise. It is not needed: the two rules agree up to rational
equivalence on every component of `D`, which is what the self-intersection formula of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula` uses, and the two theorems
for an invertible module below are deduced from it with no hypothesis.

### What is proved, given that agreement

The agreement constrains the rules on the fundamental cycle of a single integral component of `D`;
the theorems below extend it to every `(k+1)`-cycle on `D`. That extension is the work. A cycle is
a *locally* finite sum of components, so the Gysin side is a sum over the components of `i_* α`
reindexed as a sum over the fibres of `i`, which is
`Stacks.Chow.ComponentRule.extendCoeff_map_apply`, and that is where properness of `i` is used.

## References

* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)
  (chernD : FirstChernComponentCycleRule C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)

/-! ### The agreement of the two component rules on the components of the zero scheme -/

/-- **The component input of Stacks 0F95.** The assertion that for every integral component of the
zero scheme `D = Z(s)` of delta-dimension `k + 1` — equivalently, for every point of `D` of
relative dimension `k + 1` — the Gysin component cycle that `chern` attaches on `X` to its image,
weighted by `Stacks.Chow.pushforwardWeight`, is the first Chern class component cycle that
`chernD` attaches to it on `D`.

In the source both are `c₁(L|_W) ∩ [W]` for the same integral closed subscheme `W`, the two
restrictions of `L` to `W` being equal, so this is the step of the proof of Stacks 0F95 that reads
"immediate from the definition of `i^*`". Here the two rules are independent parameters standing in
for Stacks 02SO, so the agreement is a hypothesis; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersection`. The assertion is an equality of
cycle *coefficients*, as the component formulas of Stacks 02T8 and 02SO are. -/
def GysinSelfIntersectionOnComponents : Prop :=
  ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
    relativeDimension C.dimensionFunction
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) x = k + 1 →
      ∀ y : (Stacks.Divisors.zeroScheme X L s).subscheme,
        pushforwardWeight C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
            (Stacks.Divisors.zeroScheme X L s).subschemeι x *
          (gysinComponentCycleAt C p k L s chern
            ((Stacks.Divisors.zeroScheme X L s).subschemeι.base x)).1 y =
        (firstChernComponentCycleAt C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD x).1 y

/-- The agreement of the two component rules, restated on integral closed subschemes of the zero
scheme instead of on points: the two are the same datum, by
`Stacks.Chow.integralComponentAt_genericPointOf`. -/
theorem gysinSelfIntersectionOnComponents_of_components
    (h : ∀ (V : (Stacks.Divisors.zeroScheme X L s).subscheme.IdealSheafData)
      (hV : IsIntegral V.subscheme)
      (hDim : schemeDeltaDimension C
        (V.subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) =
          ((k + 1 : ℤ) : EInt))
      (y : (Stacks.Divisors.zeroScheme X L s).subscheme),
      pushforwardWeight C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι (genericPointOf V hV) *
        (gysinComponentCycleAt C p k L s chern
          ((Stacks.Divisors.zeroScheme X L s).subschemeι.base (genericPointOf V hV))).1 y =
      (firstChernComponentCycle C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD
        V hV hDim).1 y) :
    GysinSelfIntersectionOnComponents C p k L s chern chernD := by
  intro x hdim y
  have hV : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) x, hdim]
  have hx : genericPointOf (integralComponentAt x) hV = x :=
    genericPointOf_integralComponentAt x
  have h' := h (integralComponentAt x) hV hDim y
  rw [← firstChernComponentCycleAt_genericPointOf C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD _ hV hDim, hx] at h'
  exact h'

/-! ### Stacks 0F95 -/

/-- **Stacks 0F95, at the level of cycles.** Granted the agreement of the two component rules on
the integral components of the zero scheme, the Gysin cycle of the pushforward along `i` of a
`(k+1)`-cycle `α` on `D` is the first Chern class cycle of `α` on `D`.

This is sharper than the statement of the source, which is an equality of classes in `A_k(D)`.
Both sides are locally finite sums over the integral components of `α`:
`Stacks.Chow.ComponentRule.extendCoeff_map_apply` turns the left side into
`∑_x α(x) · w(x) · c(i x)`, the right side is `∑_x α(x) · c'(x)` by the definition of a
coefficientwise extension, and the hypothesis applies term by term. Only the points carrying a
nonzero coefficient of `α` are compared, and those have relative dimension `k + 1` because `α` is
a `(k+1)`-cycle. -/
theorem gysinRule_extendCycleGroup_properPushforward_subschemeι
    (hcomp : GysinSelfIntersectionOnComponents C p k L s chern chernD)
    (α : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    (gysinRule C p k L s chern).extendCycleGroup
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α) =
      (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        chernD).extendCycleGroup α := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  set i := (Stacks.Divisors.zeroScheme X L s).subschemeι with hi
  -- the left hand side: extending the Gysin rule of `X` over a pushforward along `i`
  have hcpt : IsCompact (i.base ⁻¹' {i.base y}) :=
    i.isProperMap.isCompact_preimage isCompact_singleton
  have hLHS : ((gysinRule C p k L s chern).extendCycleGroup
      (properPushforward C (i ≫ p) p i rfl (k + 1) α)).1 y =
      ∑ᶠ x : (Stacks.Divisors.zeroScheme X L s).subscheme, α.1 x *
        pushforwardWeight C (i ≫ p) p i x *
        (gysinComponentCycleAt C p k L s chern (i.base x)).1 y := by
    rw [show ((gysinRule C p k L s chern).extendCycleGroup
        (properPushforward C (i ≫ p) p i rfl (k + 1) α)).1 y =
      (gysinRule C p k L s chern).toComponentRule.extendCoeff
        (Function.locallyFinsupp.map i.base (pushforwardWeight C (i ≫ p) p i)
          i.isSpectralMap α.1) y from rfl,
      ComponentRule.extendCoeff_map_apply _ i.isSpectralMap i.isProperMap.isClosedMap _ _ y hcpt]
    exact finsum_congr fun _ ↦ rfl
  -- the right hand side: the coefficientwise extension of the cap product rule on `D`
  have hRHS : ((firstChernCapRule C (i ≫ p) k chernD).extendCycleGroup α).1 y =
      ∑ᶠ x : (Stacks.Divisors.zeroScheme X L s).subscheme, α.1 x *
        (firstChernComponentCycleAt C (i ≫ p) k chernD x).1 y := rfl
  rw [hLHS, hRHS]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul, zero_mul, zero_mul]
  · rw [mul_assoc, hcomp x
      ((mem_cyclesOfDimension_iff_forall_point C (i ≫ p) (k + 1) α.1).1 α.2 x hx) y]

/-- **Stacks 0F95.** Granted the agreement of the two component rules on the integral components
of the zero scheme, the Gysin map applied to the pushforward along `i` of a `(k+1)`-cycle `α` on
`D` is the class `c₁ ∩ α` in `A_k(D)`.

The pushforward is taken on cycles, as the proof of the source is: it reads the identity off the
definition of `i_*` on cycles and the definition of `i^*`. The identity holds already at the level
of cycles, which is
`Stacks.Chow.gysinRule_extendCycleGroup_properPushforward_subschemeι`. -/
theorem gysinHomomorphism_properPushforward_subschemeι
    (hcomp : GysinSelfIntersectionOnComponents C p k L s chern chernD)
    (α : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinHomomorphism C p k L s chern
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α) =
      firstChernClassCap C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD α := by
  change QuotientAddGroup.mk ((gysinRule C p k L s chern).extendCycleGroup
    (properPushforward C _ p (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α)) = _
  rw [gysinRule_extendCycleGroup_properPushforward_subschemeι C p k L s chern chernD hcomp α]
  rfl

/-- **Stacks 0F95, on Chow groups.** Granted the agreement of the two component rules on the
integral components of the zero scheme, the composite of proper pushforward along `i` with the
descended Gysin map is the descended cap product, `A_{k+1}(D) ⟶ A_k(D)`.

The two descent hypotheses are those of Stacks 02TO for the Gysin map and of Stacks 02TI for the
cap product, carried as hypotheses throughout this repository. The instance of Stacks 02S2 that
`Stacks.Chow.properChowPushforward` requires is discharged, `i` being a closed immersion. -/
theorem gysinHomomorphismOnChow_properChowPushforward_subschemeι
    (hgysin : GysinFactorsThroughRationalEquivalence C p k L s chern)
    (hchernD : FirstChernClassCapFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)
    (hcomp : GysinSelfIntersectionOnComponents C p k L s chern chernD)
    (α : chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinHomomorphismOnChow C p k L s chern hgysin
        (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Stacks.Divisors.zeroScheme X L s).subschemeι C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl (k + 1)) α) =
      firstChernClassCapOnChow C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD
        hchernD α := by
  induction α using QuotientAddGroup.induction_on with
  | H β => exact gysinHomomorphism_properPushforward_subschemeι C p k L s chern chernD hcomp β

/-! ### Stacks 0F95 for an invertible module -/

/-- **Stacks 0F95.** For the Gysin map of the zero scheme of a global section of an invertible
module `L`, the composite with the pushforward along `i` is intersection with the first Chern
class of the restriction `L|_D`: `i^* i_* α = c₁(L|_D) ∩ α` in `A_k(D)`.

Both operations are functions of `L` and `s` alone: the Gysin map is
`Stacks.Chow.gysinHomomorphismOfInvertible` and the right hand side is the cap product
`Stacks.Chow.firstChernClassCapOfInvertible` of the restricted module, which is invertible by
Stacks 0B8L. No hypothesis is carried: the two first Chern class component rules agree up to
rational equivalence on the integral components of `D`. The statement is exactly
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι`, of which this is an
alias. -/
@[stacks 0F95 "the identity i^* i_* α = c₁(L|_D) ∩ α in A_k(D), with i_* taken on cycles as in \
the source's proof, with no hypothesis"]
alias gysinHomomorphismOfInvertible_properPushforward_subschemeι :=
  gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι

/-- **Stacks 0F95, on Chow groups.** The composite
`i^* i_* : A_{k+1}(D) ⟶ A_k(D)` of the two descended operations of an invertible module `L` and a
section `s` is intersection with the first Chern class of `L|_D`.

The descended Gysin map is that of Stacks 02TO and the descended cap product that of Stacks 02TI,
at descent data `h` and `hchernD`. Both are propositions proved in this repository, as
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence` and
`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule`, so
the identity holds outright; with those proofs supplied it is
`Stacks.Chow.gysinChowOfInvertible_properChowPushforward_zeroSchemeι`. The instance of Stacks 02S2
needed for `i_*` on Chow groups is discharged, `i` being a closed immersion. -/
@[stacks 0F95 "the composite A_{k+1}(D) ⟶ A_k(D) of the descended operations, at any descent data \
h and hchernD; each is discharged by a theorem of this repository (Stacks 02TO and 02TI), so \
nothing is assumed"]
theorem gysinHomomorphismOnChowOfInvertible_properChowPushforward_subschemeι
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (hchernD : FirstChernClassCapFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L)))
    (α : chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinHomomorphismOnChowOfInvertible C p k L s h
        (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Stacks.Divisors.zeroScheme X L s).subschemeι C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl (k + 1)) α) =
      firstChernClassCapOnChow C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
          ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
        hchernD α := by
  induction α using QuotientAddGroup.induction_on with
  | H β => exact gysinHomomorphismOfInvertible_properPushforward_subschemeι C p k L s β

end Stacks.Chow

end
