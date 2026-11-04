module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.GysinChowPushforward

/-!
# The first Chern class cap product and the Gysin map of an invertible module

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)`. The cap product of
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass` and the Gysin map of
`StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction` each carry the first Chern class component
rule of `L` as an explicit argument, and
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule` supplies that argument from `L`
alone, giving `Stacks.Chow.firstChernClassCapOfInvertible` and
`Stacks.Chow.gysinHomomorphismOfInvertible`.

That file specialises the two constructions and one of their five characterising statements. This
file specialises the remaining four, so that every statement about the cap product and the Gysin
map is available as a function of `L` and `s` with no component rule in sight:

* the integral-component formula for the cap product, through proper pushforward of *Chow
  classes* rather than of cycles;
* the locally finite component formula for the cap product;
* the contained-component formula for the Gysin map;
* the locally finite component formula for the Gysin map;

together with the intersection homomorphism of an effective Cartier zero scheme.

## Main definitions

* `Stacks.Chow.effectiveCartierIntersectionOfInvertible` — intersection with the zero scheme of
  `s`, when that zero scheme is an effective Cartier divisor, as a homomorphism
  `Z_{k+1}(X) ⟶ A_k(X)`.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_integral` — the value of the cap product on the
  fundamental cycle of an integral closed subscheme.
* `Stacks.Chow.firstChernClassCapOfInvertible_finsum` — the locally finite component formula for
  the cap product.
* `Stacks.Chow.gysinHomomorphismOfInvertible_of_le` — the value of the Gysin map on an integral
  closed subscheme contained in the zero scheme.
* `Stacks.Chow.gysinHomomorphismOfInvertible_finsum` — the locally finite component formula for
  the Gysin map.

## Implementation notes

### Each proof is an instantiation

Every declaration here is the corresponding component-rule-parametric declaration applied to
`Stacks.Chow.firstChernComponentCycleRule C p k L` or
`Stacks.Chow.firstChernComponentClass C p k L`. The one exception is the integral-component
formula for the cap product, whose parametric form
`Stacks.Chow.firstChernClassCap_integral_cycle` is stated at the level of cycles — it equates the
cap product with the class of the pushforward *cycle*. The class-level form equates it instead
with the proper Chow pushforward of the component *class*, and the two agree because
`Stacks.Chow.properChowPushforward_mk` holds by `rfl`.

### Stacks 02S2 is discharged, not assumed

`Stacks.Chow.properChowPushforward` carries the vanishing statement of Stacks 02S2 as an explicit
hypothesis. As in `StacksFrontier.AlgebraicGeometry.Chow.GysinChowPushforward`, that hypothesis is
supplied here rather than assumed: every morphism pushed along is a closed immersion, for which
Stacks 02S2 is proved outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`.

### No Stacks attribute

No declaration here carries a Stacks attribute. Whether these statements and those of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule` are the statements of Stacks 02SO
and Stacks 02T8 depends on the identification of the generic-stalk model of a meromorphic section
with the sheaf `𝒦_X(L)` and on the independence of the chosen section, which are discussed in the
module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule` and
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence`.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
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

/-! ### The cap product of an invertible module -/

/-- On the fundamental cycle of a single integral closed subscheme `W ⊆ X` of delta-dimension
`k + 1`, the cap product of an invertible module is the proper Chow pushforward along `W ⟶ X` of
the first Chern class of `L|_W`.

This is `Stacks.Chow.firstChernClassCapOfInvertible_integral_cycle` read through
`Stacks.Chow.properChowPushforward_mk`. The instance of Stacks 02S2 that
`Stacks.Chow.properChowPushforward` requires is discharged, `W.subschemeι` being a closed
immersion. -/
@[stacks 02SO "integral component formula"]
theorem firstChernClassCapOfInvertible_integral (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernClassCapOfInvertible C p k L
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      properChowPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion W.subschemeι C
          (W.subschemeι ≫ p) p rfl k)
        (firstChernComponentClass C p k L W hW hDim) :=
  firstChernClassCapOfInvertible_integral_cycle C p k L W hW hDim

/-- The locally finite component formula for the cap product of an invertible module: on a
presentation `α = ∑ n_j [W_j]` of a `(k+1)`-cycle, `c₁(L) ∩ α` is the class of
`∑ n_j c₁(L) ∩ [W_j]`. -/
@[stacks 02SO "locally finite component formula"]
theorem firstChernClassCapOfInvertible_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C p k,
      firstChernClassCapOfInvertible C p k L α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ j : J, n j *
        (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
          (W j) (hW j) (hDim j)).1 x :=
  firstChernClassCap_finsum C p k (firstChernComponentCycleRule C p k L) W hW hDim hLocal n α hα

/-! ### The Gysin homomorphism of an invertible module -/

section Gysin

variable (s : Γ(L, ⊤))

/-- The Gysin image of an integral closed subscheme contained in the zero scheme of `s` is the
proper Chow pushforward into that zero scheme of the first Chern class of `L|_W`.

The instance of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is discharged, the
inclusion of `W` into the zero scheme being a closed immersion. -/
@[stacks 02T8 "integral component contained in the zero scheme"]
theorem gysinHomomorphismOfInvertible_of_le (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphismOfInvertible C p k L s
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      properChowPushforward C (W.subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h) (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Scheme.IdealSheafData.inclusion h) C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (by simp) k)
        (firstChernComponentClass C p k L W hW hDim) :=
  gysinHomomorphism_of_le C p k L s (firstChernComponentClass C p k L) W hW hDim h

/-- The locally finite component formula for the Gysin map of an invertible module. -/
@[stacks 02T8 "locally finite component formula"]
theorem gysinHomomorphismOfInvertible_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      gysinHomomorphismOfInvertible C p k L s α = QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
            (W j) (hW j) (hDim j)).1 x :=
  gysinHomomorphism_finsum C p k L s (firstChernComponentClass C p k L) W hW hDim hLocal n α hα

/-- Intersection with the zero scheme of `s`, when that zero scheme is an effective Cartier
divisor, read as a class on the ambient scheme: the Gysin map of the zero scheme followed by
proper Chow pushforward along its closed immersion into `X`. -/
@[stacks 02T8 "intersection with an effective Cartier divisor"]
def effectiveCartierIntersectionOfInvertible
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s)) :
    CycleGroup C p (k + 1) →+ chowGroup C p k :=
  effectiveCartierIntersection C p k L s (firstChernComponentClass C p k L) hD

/-- The intersection with an effective Cartier zero scheme is the proper Chow pushforward of the
Gysin class of the cycle. -/
theorem effectiveCartierIntersectionOfInvertible_apply
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s))
    (α : CycleGroup C p (k + 1)) :
    effectiveCartierIntersectionOfInvertible C p k L s hD α =
      properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L s).subschemeι C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl k)
        (gysinHomomorphismOfInvertible C p k L s α) :=
  rfl

end Gysin

end Stacks.Chow

end
