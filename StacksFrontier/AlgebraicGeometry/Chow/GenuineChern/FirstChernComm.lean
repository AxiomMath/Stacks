module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow

/-!
# Commutativity of two first Chern class cap products

Let `X` be locally of finite type over the base of chapter 42 and let `ℒ`, `𝒩` be invertible
`𝒪_X`-modules. Then

  `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α`  in  `A_k(X)`,  for `α ∈ A_{k+2}(X)`.

This is [Stacks, Tag 02TJ]. The passage from the integral closed subschemes of `X` to every class
is `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm`; this file supplies its two inputs:
Stacks 02TI in its reduced form is `Stacks.Chow.firstChernCapKillsPrincipalDivisor`, and the
integral case is [Stacks, Tag 02TH]
(`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`) applied on each integral closed
subscheme `W`, after identifying the value of the component rule at `W` with the class of the
divisor of any nonzero meromorphic section ([Stacks, Tag 02SJ]).

## Main results

* `Stacks.Chow.GenuineChern.firstChernCapCommutesOnIntegralComponents` — Stacks 02TH on the
  integral closed subschemes of delta-dimension `k + 2`, for the component rules.
* `Stacks.Chow.GenuineChern.invCap_capOnChow_comm` — Stacks 02TJ, for the cap operators
  `Stacks.Chow.invCap`.
* `Stacks.Chow.GenuineChern.firstChernClassCapChow_comm` — Stacks 02TJ, for
  `Stacks.Chow.firstChernClassCapChow`.

## References

* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **Stacks 02TH on the integral components.** On every integral closed subscheme `W ⊆ X` of
delta-dimension `k + 2`, capping the component cycle of `𝒩` at `W` with `c₁(ℒ|_W)` and the
component cycle of `ℒ` at `W` with `c₁(𝒩|_W)` gives the same class in `A_k(W)`. -/
theorem firstChernCapCommutesOnIntegralComponents :
    FirstChernCapCommutesOnIntegralComponents C p k L N := by
  intro W hW hDim
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      W.subschemeι.toLRSHom.toShHom L
      ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj N) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      W.subschemeι.toLRSHom.toShHom N
      ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  have := isInvertible_presheaf_modulePullback L W.subschemeι
  have := isInvertible_presheaf_modulePullback N W.subschemeι
  have hn : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 2 : ℤ) : EInt) := by
    rw [hDim, show (k + 1 + 1 : ℤ) = k + 2 by ring]
  obtain ⟨s, hs⟩ :=
    Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible
      ((Scheme.Modules.pullback W.subschemeι).obj L)
  obtain ⟨t, ht⟩ :=
    Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible
      ((Scheme.Modules.pullback W.subschemeι).obj N)
  have hL : (QuotientAddGroup.mk' (rationalEquivalences C (W.subschemeι ≫ p) (k + 1))
      (firstChernComponentCycleRule C p (k + 1) L W hW hDim)) =
      QuotientAddGroup.mk' _ (divisorCycleOfInvertibleSection C (W.subschemeι ≫ p) hn _ s) :=
    firstChernComponentClass_eq_mk_of_ne_zero C p (k + 1) L W hDim hs
  have hN : (QuotientAddGroup.mk' (rationalEquivalences C (W.subschemeι ≫ p) (k + 1))
      (firstChernComponentCycleRule C p (k + 1) N W hW hDim)) =
      QuotientAddGroup.mk' _ (divisorCycleOfInvertibleSection C (W.subschemeι ≫ p) hn _ t) :=
    firstChernComponentClass_eq_mk_of_ne_zero C p (k + 1) N W hDim ht
  rw [← firstChernClassCapChow_mk, ← firstChernClassCapChow_mk, hL, hN,
    firstChernClassCapChow_mk, firstChernClassCapChow_mk]
  exact firstChernClassCapOfInvertible_divisorCycle_comm C (W.subschemeι ≫ p) hn _ _ ht hs

/-- **Stacks 02TJ.** For invertible modules `ℒ` and `𝒩` on `X` locally of finite type over the
base and `α ∈ A_{k+2}(X)`,

  `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α`  in  `A_k(X)`. -/
theorem invCap_capOnChow_comm (α : chowGroup C p (k + 1 + 1)) :
    (invCap C p L).capOnChow C p k ((invCap C p N).capOnChow C p (k + 1) α) =
      (invCap C p N).capOnChow C p k ((invCap C p L).capOnChow C p (k + 1) α) :=
  firstChernClassCapOnChowOfInvertible_comm C p k L N
    (fun j ↦ firstChernCapKillsPrincipalDivisor C j)
    (firstChernCapCommutesOnIntegralComponents C p k L N) α

/-- **Stacks 02TJ**, for the descended operations `Stacks.Chow.firstChernClassCapChow`. -/
theorem firstChernClassCapChow_comm (α : chowGroup C p (k + 1 + 1)) :
    firstChernClassCapChow C k p L (firstChernClassCapChow C (k + 1) p N α) =
      firstChernClassCapChow C k p N (firstChernClassCapChow C (k + 1) p L α) :=
  invCap_capOnChow_comm C p k L N α

end Stacks.Chow.GenuineChern

end
