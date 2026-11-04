module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# The Gysin system of the first Chern class rule

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. A
`Stacks.Chow.GysinSystem` for it is a choice, for every scheme locally of finite type over `S`,
every invertible module on it and every degree, of the contained-component first Chern class rule
of Stacks 02SO, together with the vanishing of Stacks 02TO for the Gysin map built from that rule.

This file constructs, with no hypothesis, the Gysin system whose rule is
`Stacks.Chow.firstChernComponentClass`, the class of the divisor cycle of a nonzero meromorphic
section of the restricted invertible module.

## Main definitions

* `Stacks.Chow.GysinOfInvertibleDescends` — the vanishing of Stacks 02TO for every scheme locally
  of finite type over the base, every invertible module on it, every global section and every
  degree, bundled as a single `Prop`.
* `Stacks.Chow.gysinSystemOfInvertible` — the Gysin system of the first Chern class rule.

## Main results

* `Stacks.Chow.gysinOfInvertibleDescends` — the vanishing of Stacks 02TO for every test datum.
* `Stacks.Chow.GysinSystem.eq_of_chern_eq` — a Gysin system is determined by its first Chern class
  rule.
* `Stacks.Chow.gysinSystemOfInvertible_onChow`,
  `Stacks.Chow.gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible` — its Gysin map on Chow
  groups is the descended Gysin map of Stacks 02TO for the invertible module and the section.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The vanishing of Stacks 02TO, bundled over all test data -/

/-- Stacks 02TO for every test datum: for every scheme locally of finite type over the base,
every invertible module on it, every global section of that module and every degree, the Gysin map
of the zero scheme of the section kills the cycles rationally equivalent to zero. -/
def GysinOfInvertibleDescends (C : ChowSituation.{u}) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ),
    GysinOfInvertibleFactorsThroughRationalEquivalence C q k L s

/-- For every scheme locally of finite type over the base, every invertible module on it, every
global section of that module and every degree, the Gysin map of the zero scheme of the section
kills the cycles rationally equivalent to zero. -/
@[stacks 02TO "the vanishing for every test datum at once, with no hypothesis: the bundled form \
of `gysinOfInvertibleFactorsThroughRationalEquivalence`"]
theorem gysinOfInvertibleDescends (C : ChowSituation.{u}) : GysinOfInvertibleDescends C :=
  @fun _ q _ L _ s k ↦ gysinOfInvertibleFactorsThroughRationalEquivalence C q k L s

/-! ### A Gysin system is determined by its first Chern class rule -/

/-- Two Gysin systems with the same contained-component first Chern class rule are equal. -/
theorem GysinSystem.eq_of_chern_eq {C : ChowSituation.{u}} {G G' : GysinSystem C}
    (h : ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      (k : ℤ), G.chern q L k = G'.chern q L k) : G = G' := by
  obtain ⟨chern, factors⟩ := G
  obtain ⟨chern', factors'⟩ := G'
  congr
  funext T q _ L _ k
  exact h q L k

/-! ### The Gysin system of the first Chern class rule -/

/-- The Gysin system whose contained-component first Chern class rule is the class of the
divisor cycle of a nonzero meromorphic section of the restricted invertible module. -/
def gysinSystemOfInvertible (C : ChowSituation.{u}) : GysinSystem C where
  chern := @fun _ q _ L _ k ↦ firstChernComponentClass C q k L
  factors := @fun _ q _ L _ s k ↦ gysinOfInvertibleFactorsThroughRationalEquivalence C q k L s

/-- The first Chern class rule of the Gysin system of an invertible module. -/
@[simp]
theorem gysinSystemOfInvertible_chern (C : ChowSituation.{u})
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (k : ℤ) :
    (gysinSystemOfInvertible C).chern q L k = firstChernComponentClass C q k L :=
  rfl

/-- The Gysin map on Chow groups of the Gysin system of an invertible module is the descended Gysin
map `i^* : A_{k+1}(T) ⟶ A_k(Z(s))` of that module and section. -/
theorem gysinSystemOfInvertible_onChow (C : ChowSituation.{u})
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    (gysinSystemOfInvertible C).onChow q L s k =
      gysinHomomorphismOnChowOfInvertible C q k L s (gysinOfInvertibleDescends C q L s k) :=
  rfl

/-- The Gysin map on Chow groups of the Gysin system of an invertible module is the descended
map `i^* : A_{k+1}(T) ⟶ A_k(Z(s))` of Stacks 02TO, `Stacks.Chow.gysinChowOfInvertible`. -/
theorem gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible (C : ChowSituation.{u})
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    (gysinSystemOfInvertible C).onChow q L s k = gysinChowOfInvertible C q k L s :=
  rfl

end Stacks.Chow

end
