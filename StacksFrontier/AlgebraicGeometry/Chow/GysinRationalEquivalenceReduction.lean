module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible

/-!
# Reducing the vanishing of Stacks 02TO to a single integral component

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global section with zero
scheme `i : D = Z(s) ⟶ X`. Stacks 02TO asserts that the Gysin map

  `i^* : Z_{k+1}(X) ⟶ A_k(D)`

kills every `(k+1)`-cycle rationally equivalent to zero. That assertion is the `Prop`
`Stacks.Chow.GysinOfInvertibleFactorsThroughRationalEquivalence` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible`; it is proved, with no
hypothesis, as `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence` in
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge`, by way of the reduction
in this file.

This file removes the part of that proof which is bookkeeping rather than geometry. A cycle
rationally equivalent to zero is, by Stacks 02RW, a *locally finite* sum
`α = ∑_j i_{j,*} div_{W_j}(f_j)` over integral closed subschemes `W_j ⊆ X` of delta-dimension
`k + 2`. The theorem below shows that the vanishing for `α` follows from the vanishing for each
summand separately, so the one datum left to prove is the single-component statement

  `i^*(i_{V,*} div_V(f)) ∼ 0`  on `D`, with witnesses inside `i^{-1}(V)`,

for *one* integral closed subscheme `V ⊆ X` of delta-dimension `k + 2` and *one* nonzero rational
function `f` on `V`. That is `Stacks.Chow.GysinKillsPrincipalDivisorOnComponent`; for the first
Chern class rule of `L` it is proved as
`Stacks.Chow.gysinOfInvertibleKillsPrincipalDivisorOnComponent` in
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge`.

## Main definitions

* `Stacks.Chow.GysinKillsPrincipalDivisorOnComponent` — the single-component datum, for the Gysin
  map of an arbitrary first Chern class component rule.
* `Stacks.Chow.GysinOfInvertibleKillsPrincipalDivisorOnComponent` — the same datum for the Gysin
  map of an invertible module and a section, with no component rule in sight.
* `Stacks.Chow.gysinHomomorphismOnChowOfInvertibleOfComponents` — the map
  `i^* : A_{k+1}(X) ⟶ A_k(D)` of Stacks 02TO, built from that datum.

## Main results

* `Stacks.Chow.gysinFactorsThroughRationalEquivalence_of_components` — the single-component datum
  implies `Stacks.Chow.GysinFactorsThroughRationalEquivalence`.
* `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_of_components` — the vanishing
  of Stacks 02TO follows from the single-component datum.
* `Stacks.Chow.gysinKillsPrincipalDivisor_of_factorsThroughRationalEquivalence` — conversely, the
  vanishing gives the single-component statement with the carrier forgotten. So the carrier is the
  only thing the datum asserts beyond an instance of the conclusion.

## Implementation notes

### What this removes from the dependency list of Stacks 02TO

The source proves the reduction by forming `X' = ⨿ W_j`, pulling the triple back to `X'`, and
using

* Stacks 02TA, that the Gysin map commutes with proper pushforward along `X' ⟶ X`, and
* Stacks 02S2, that proper pushforward along `D' ⟶ D` factors through rational equivalence.

Neither is needed here. The Gysin map of Stacks 02T8 is built in this repository as the
coefficientwise extension `Stacks.Chow.IntegralComponentRule.extendChow` of a rule on integral
components, and `Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum` already evaluates such
an extension on a locally finite sum of cycles. So the family is handled one member at a time and
the disjoint union never appears.

That matters for what is left to do. The morphism `D' ⟶ D` the source pushes along is proper but
not a closed immersion — `D'` is a disjoint union, and the `W_j` may overlap — so the source needs
Stacks 02S2 in its general form, hence Stacks 02RU, neither of which is in this repository. This
reduction never forms `D'`, and the only pushforwards the remaining single-component datum involves
are along the closed immersions `V ⟶ X` and `V ∩ D ⟶ D`, for which Stacks 02S2 *is* proved here:
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`.

### Why the datum carries a carrier

`Stacks.Chow.IsRationallyEquivalentToZeroWithin` rather than
`Stacks.Chow.IsRationallyEquivalentToZero` is what the datum asserts, and the strengthening is
forced, not cosmetic. Reassembling locally finitely many rational equivalences into one needs the
*witnessing* families to be jointly locally finite, and the bare predicate of Stacks 02RW does not
give that — the witnesses of the summands may be far larger than the summands. See the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity`. The carrier
`i^{-1}(V)` is the natural one: the Gysin component cycle of `V` is supported there
(`Stacks.Chow.support_gysinComponentCycle_subset`), and the family `{i^{-1}(W_j)}` is locally
finite because `{W_j}` is and `i` is continuous.

### Where Stacks 02TO itself is

The declarations below derive the vanishing and the descended map
`i^* : A_{k+1}(X) ⟶ A_k(D)` from the single-component datum
`Stacks.Chow.GysinOfInvertibleKillsPrincipalDivisorOnComponent`, which is the case the source's
proof reduces to — `X` integral and `α = div(f)`. That datum is proved in
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge`, where Stacks 02TO is
registered with no hypothesis: `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence`
is the vanishing and `Stacks.Chow.gysinChowOfInvertible` is the descended map. The declarations
here are the steps of that proof and carry no Stacks attribute.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)

/-! ### The Gysin map as a coefficientwise extension -/

/-- The Gysin homomorphism of Stacks 02T8 is the coefficientwise extension to the Chow group of
the rule of Stacks 02T8 (1) on integral components. -/
theorem gysinHomomorphism_eq_extendChow :
    gysinHomomorphism C p k L s chern = (gysinRule C p k L s chern).extendChow :=
  rfl

/-! ### The single-component datum -/

/-- **The one geometric input the vanishing of Stacks 02TO still needs.** For every integral
closed subscheme `V ⊆ X` of delta-dimension `k + 2` and every nonzero rational function `f` on
`V`, the Gysin cycle of the pushforward of `div_V(f)` is rationally equivalent to zero on the zero
scheme `D = Z(s)`, witnessed by a family of integral closed subschemes contained in the preimage
of `V`.

This is the case "`X` integral and `α = div(f)`" that the proof of Stacks 02TO reduces to, read on
`X` rather than on `V`. `Stacks.Chow.gysinFactorsThroughRationalEquivalence_of_components` shows
that it is enough. -/
def GysinKillsPrincipalDivisorOnComponent : Prop :=
  ∀ (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt))
    (f : (rationalFunctions V.subscheme)ˣ),
    IsRationallyEquivalentToZeroWithin C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s chern).extendCycleGroup
        ⟨principalDivisorPushforward C p V hV f,
          principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) V hV hDim f⟩)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (V.support : Set X))

/-! ### The reduction -/

/-- **The locally finite half of the proof of Stacks 02TO.** If the Gysin map kills the
pushforward of the principal divisor of a rational function on each single integral closed
subscheme of delta-dimension `k + 2`, with witnesses over that subscheme, then it kills every
`(k+1)`-cycle rationally equivalent to zero.

Neither Stacks 02TA nor the general form of Stacks 02S2 is used: the Gysin map is a
coefficientwise extension, so `Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum` splits
it over the locally finite presentation of Stacks 02RW, and
`Stacks.Chow.rationallyEquivalentToZero_finsum` reassembles the pieces. -/
theorem gysinFactorsThroughRationalEquivalence_of_components
    (h : GysinKillsPrincipalDivisorOnComponent C p k L s chern) :
    GysinFactorsThroughRationalEquivalence C p k L s chern := by
  intro α hα
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  set R := gysinRule C p k L s chern with hR
  set i := (Stacks.Divisors.zeroScheme X L s).subschemeι with hi
  -- the summands of the presentation of Stacks 02RW, as `(k+1)`-cycles on `X`
  set D : J → CycleGroup C p (k + 1) := fun j ↦
    ⟨principalDivisorPushforward C p (W j) (hW j) (g j),
      principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) (W j) (hW j) (hDim j) (g j)⟩
    with hD
  have hsupp : ∀ j, Function.support (D j).1 ⊆ ((W j).support : Set X) := fun j ↦
    support_principalDivisorPushforward_subset C p (W j) (hW j) (g j)
  -- the Gysin map splits over the presentation
  have hsplit : ∀ y : (Stacks.Divisors.zeroScheme X L s).subscheme,
      (R.extendCycleGroup α).1 y = ∑ᶠ j : J, (R.extendCycleGroup (D j)).1 y :=
    fun y ↦ R.extendCycleGroup_finsum D (fun j ↦ ((W j).support : Set X)) hLocal hsupp α
      (fun x ↦ hg x) y
  -- each piece is rationally equivalent to zero over its own component, and the carriers are
  -- locally finite because `i` is continuous
  have hpiece : ∀ j, IsRationallyEquivalentToZeroWithin C (i ≫ p) k (R.extendCycleGroup (D j))
      (i.base ⁻¹' ((W j).support : Set X)) := fun j ↦ h (W j) (hW j) (hDim j) (g j)
  have hcarrier : LocallyFinite fun j ↦ i.base ⁻¹' ((W j).support : Set X) :=
    hLocal.preimage_continuous i.continuous
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  exact rationallyEquivalentToZero_finsum C (i ≫ p) k (fun j ↦ R.extendCycleGroup (D j))
    (fun j ↦ i.base ⁻¹' ((W j).support : Set X)) hcarrier hpiece hsplit

/-! ### The same thing with no component rule -/

/-- **The single-component input to the vanishing of Stacks 02TO**, for the Gysin map of an
invertible module `L` and a section `s`: the single-component datum
`Stacks.Chow.GysinKillsPrincipalDivisorOnComponent` at the first Chern class component rule of
`L`. It is proved as `Stacks.Chow.gysinOfInvertibleKillsPrincipalDivisorOnComponent`. -/
abbrev GysinOfInvertibleKillsPrincipalDivisorOnComponent : Prop :=
  GysinKillsPrincipalDivisorOnComponent C p k L s (firstChernComponentClass C p k L)

/-- **The reduction of Stacks 02TO to its single-component case.** If the Gysin map of the zero
scheme of `s` kills the pushforward of the principal divisor of a rational function on each single
integral closed subscheme of delta-dimension `k + 2`, with witnesses over that subscheme, then it
kills every `(k+1)`-cycle rationally equivalent to zero — which is the vanishing of Stacks 02TO, and
therefore, by `Stacks.Chow.gysinHomomorphismOnChowOfInvertibleOfComponents`, the descended map
`i^* : A_{k+1}(X) ⟶ A_k(D)`. The datum is proved, and Stacks 02TO stated with no hypothesis, as
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence`. -/
theorem gysinOfInvertibleFactorsThroughRationalEquivalence_of_components
    (h : GysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s) :
    GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s :=
  gysinFactorsThroughRationalEquivalence_of_components C p k L s
    (firstChernComponentClass C p k L) h

/-- The Gysin homomorphism of the zero scheme of a global section of an invertible module,
descended to Chow groups,

  `i^* : A_{k+1}(X) ⟶ A_k(D)`,

built from the single-component datum; with that datum proved it is
`Stacks.Chow.gysinChowOfInvertible`, the form of Stacks 02TO with no hypothesis. This is
`Stacks.Chow.gysinHomomorphismOnChowOfInvertible` with its vanishing hypothesis supplied by
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_of_components`, so it is a
function of `L`, `s` and that datum alone, and
`Stacks.Chow.eq_gysinHomomorphismOnChowOfInvertible` says it is the only homomorphism of Chow
groups agreeing with the Gysin map on cycle representatives. -/
def gysinHomomorphismOnChowOfInvertibleOfComponents
    (h : GysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s) :
    chowGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  gysinHomomorphismOnChowOfInvertible C p k L s
    (gysinOfInvertibleFactorsThroughRationalEquivalence_of_components C p k L s h)

/-- The descended Gysin map agrees with the Gysin homomorphism of Stacks 02T8 on cycle
representatives, which is the formula that determines it. -/
@[simp]
theorem gysinHomomorphismOnChowOfInvertibleOfComponents_mk
    (h : GysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s)
    (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOnChowOfInvertibleOfComponents C p k L s h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      gysinHomomorphismOfInvertible C p k L s α :=
  rfl

/-! ### The datum is an instance of the conclusion, up to the carrier -/

/-- Conversely, the vanishing of Stacks 02TO gives the single-component statement with its carrier
forgotten: the pushforward of a principal divisor on one integral closed subscheme is itself a
cycle rationally equivalent to zero, by the one-member family.

So the carrier of `Stacks.Chow.GysinKillsPrincipalDivisorOnComponent` is the only thing that datum
asks for beyond an instance of the conclusion, and by
`Stacks.Chow.IsRationallyEquivalentToZeroWithin.isRationallyEquivalentToZero` the carrier is
discarded freely in the other direction. -/
theorem gysinKillsPrincipalDivisor_of_factorsThroughRationalEquivalence
    (h : GysinFactorsThroughRationalEquivalence C p k L s chern) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt))
    (f : (rationalFunctions V.subscheme)ˣ) :
    IsRationallyEquivalentToZero C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s chern).extendCycleGroup
        ⟨principalDivisorPushforward C p V hV f,
          principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) V hV hDim f⟩) := by
  refine (QuotientAddGroup.eq_zero_iff _).1 (h _ ⟨PUnit.{u + 1}, fun _ ↦ V, fun _ ↦ hV,
    fun _ ↦ hDim, locallyFinite_of_finite _, fun _ ↦ f, fun x ↦ ?_⟩)
  exact (finsum_unique (fun _ : PUnit.{u + 1} ↦
    principalDivisorPushforward C p V hV f x)).symm

end Stacks.Chow

end
