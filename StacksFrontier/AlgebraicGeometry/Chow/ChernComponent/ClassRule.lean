module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ComponentRule
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent

/-!
# The first Chern class component rule of an invertible module

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `L` be an invertible `𝒪_X`-module. A *component rule* for `L` assigns to every
integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` a value for the first Chern class of
`L|_W` capped with the fundamental cycle of `W`: a `k`-cycle for
`Stacks.Chow.FirstChernComponentCycleRule C p k`, and a class in `A_k(W)` for
`Stacks.Chow.FirstChernComponentClassRule C p k`. We construct both rules from `L`, and with them
the first Chern class cap product and the Gysin homomorphism of `L`.

## Main definitions

* `Stacks.Chow.firstChernComponentCycleRule`: the cycle-valued component rule of an invertible
  module.
* `Stacks.Chow.firstChernComponentClass`: the Chow-class-valued component rule of an invertible
  module.
* `Stacks.Chow.firstChernClassCapOfInvertible`: the cap product `α ↦ c₁(L) ∩ α` of an invertible
  module.
* `Stacks.Chow.gysinHomomorphismOfInvertible`: the Gysin homomorphism of the zero scheme of a
  global section of an invertible module.

## Main results

* `Stacks.Chow.isInvertible_presheaf_modulePullback`: the pullback of an invertible module along a
  morphism of schemes is invertible.
* `Stacks.Chow.firstChernComponentClass_eq_mk`: the class rule is the class of the cycle rule.
* `Stacks.Chow.firstChernClassCapOfInvertible_integral_cycle`: the cap product on the fundamental
  cycle of an integral closed subscheme.
* `Stacks.Chow.gysinHomomorphismOfInvertible_of_not_le`: the Gysin image of an integral closed
  subscheme not contained in the zero scheme is the class of its intersection with the zero scheme.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-! ### Invertibility of pullbacks -/

/-- The pullback of an invertible module along a morphism of schemes `f : X' ⟶ X` is invertible
(Stacks, Tag 0B8L), with the structure sheaf of `X'` spelled as `Scheme.presheaf` and its sheaf
condition as `Scheme.ringCatSheaf.2`. -/
theorem isInvertible_presheaf_modulePullback {X' : Scheme.{u}} (f : X' ⟶ X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L
      ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  isInvertible_presheaf _

/-! ### The two component rules -/

/-- The cycle-valued first Chern class component rule of an invertible module: on each integral
closed subscheme `W ⊆ X` of delta-dimension `k + 1` it is the divisor cycle of a chosen nonzero
element of the generic stalk of `L|_W`. -/
def firstChernComponentCycleRule : FirstChernComponentCycleRule C p k :=
  chernComponentCycleRuleOfInvertible C p k L fun W _ =>
    isInvertible_presheaf_modulePullback L W.subschemeι

/-- The Chow-class-valued first Chern class component rule of an invertible module: on each
integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` it is the class in `A_k(W)` of the
divisor cycle of a chosen nonzero element of the generic stalk of `L|_W`. -/
def firstChernComponentClass : FirstChernComponentClassRule C p k := fun W hW hDim =>
  QuotientAddGroup.mk (firstChernComponentCycleRule C p k L W hW hDim)

/-- The class rule is the class of the cycle rule. -/
@[simp]
theorem firstChernComponentClass_eq_mk (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentClass C p k L W hW hDim =
      QuotientAddGroup.mk (firstChernComponentCycleRule C p k L W hW hDim) :=
  rfl

/-! ### The cap product and the Gysin homomorphism of an invertible module -/

/-- The first Chern class cap product `Z_{k+1}(X) ⟶ A_k(X)`, `α ↦ c₁(L) ∩ α`, of an invertible
module: `Stacks.Chow.firstChernClassCap` at the component rule of `L`. -/
@[stacks 02SO]
abbrev firstChernClassCapOfInvertible : CycleGroup C p (k + 1) →+ chowGroup C p k :=
  firstChernClassCap C p k (firstChernComponentCycleRule C p k L)

/-- The cap product of an invertible module satisfies the locally finite component formula that
determines it. -/
theorem isFirstChernClassCap_firstChernClassCapOfInvertible :
    IsFirstChernClassCap C p k (firstChernComponentCycleRule C p k L)
      (firstChernClassCapOfInvertible C p k L) :=
  (firstChernClassCapConstruction C p k (firstChernComponentCycleRule C p k L)).2

/-- On the fundamental cycle of a single integral closed subscheme `W ⊆ X` of delta-dimension
`k + 1`, the cap product of an invertible module is the class of the pushforward to `X` of the
divisor cycle of `L|_W`. -/
theorem firstChernClassCapOfInvertible_integral_cycle (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernClassCapOfInvertible C p k L
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L) W hW hDim) :=
  firstChernClassCap_integral_cycle C p k (firstChernComponentCycleRule C p k L) W hW hDim

section Gysin

variable (s : Γ(L, ⊤))

/-- The Gysin homomorphism of the zero scheme of a global section `s` of an invertible module:
`Stacks.Chow.gysinHomomorphism` at the first Chern class component rule of `L`. -/
@[stacks 02T8 "Gysin homomorphism"]
abbrev gysinHomomorphismOfInvertible : CycleGroup C p (k + 1) →+
    chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  gysinHomomorphism C p k L s (firstChernComponentClass C p k L)

/-- The Gysin homomorphism of an invertible module satisfies the locally finite component formula
that determines it. -/
theorem isGysinHomomorphism_gysinHomomorphismOfInvertible :
    IsGysinHomomorphism C p k L s (firstChernComponentClass C p k L)
      (gysinHomomorphismOfInvertible C p k L s) :=
  (gysinHomomorphismConstruction C p k L s (firstChernComponentClass C p k L)).2

/-- The Gysin image of an integral closed subscheme not contained in the zero scheme is the class
of its scheme-theoretic intersection with that zero scheme. -/
@[stacks 02T8 "integral component not contained in the zero scheme"]
theorem gysinHomomorphismOfInvertible_of_not_le (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphismOfInvertible C p k L s
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k) :=
  gysinHomomorphism_of_not_le C p k L s (firstChernComponentClass C p k L) W hW hDim h

end Gysin

end Stacks.Chow

end
