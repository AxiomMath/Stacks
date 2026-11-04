module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass

/-!
# The component rule of the first Chern class cap product

The cap product `Z_{k+1}(X) ⟶ A_k(X)`, `α ↦ c₁(L) ∩ α`, of `Stacks.Chow.firstChernClassCap` is
built from a `Stacks.Chow.FirstChernComponentCycleRule`: a `k`-cycle on every integral closed
subscheme `W ⊆ X` of delta-dimension `k + 1`. We construct such a rule from `L`, as the divisor
cycle of a chosen nonzero element of the generic stalk of `L|_W`, under the hypothesis that every
restriction `L|_W` is locally free of rank one in the stalkwise form
`Stacks.Divisors.IsTrivializedNear`, or that every restriction is invertible. The rule depends on
the chosen elements.

## Main definitions

* `Stacks.Chow.chernComponentCycle` — the divisor cycle of a meromorphic section as a `k`-cycle
  on an integral scheme of delta-dimension `k + 1`.
* `Stacks.Chow.chernComponentCycleRule` — the first Chern class component rule built from `L`.
* `Stacks.Chow.chernComponentCycleRuleOfInvertible` — the same, with the local triviality of each
  restriction replaced by its invertibility.

## Main results

* `Stacks.Chow.chernComponentCycle_genericPoint` and `Stacks.Chow.chernComponentCycle_eq_zero` —
  the coefficients of the component cycle.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The component cycle, graded for the component rule -/

section ComponentCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {k : ℤ}
  (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) {L : X.Modules}

/-- The component cycle of the first Chern class: the Weil divisor
`div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` of a meromorphic section `s ∈ L_η`, as a cycle of
delta-dimension `k` on an integral scheme of delta-dimension `k + 1`. -/
def chernComponentCycle (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) : CycleGroup C p k :=
  ⟨weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s), by
    have h := weilDivisorAlgebraicCycle_mem_cyclesOfDimension_sub_one C p hk
      (weilDivisorOfMeromorphicSection hL s)
    rwa [add_sub_cancel_right] at h⟩

/-- The coefficient of the component cycle at the generic point of a prime divisor `Z` is the
order of vanishing of `s` along `Z`. -/
@[simp]
theorem chernComponentCycle_genericPoint (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) (Z : PrimeDivisor X) :
    ((chernComponentCycle C p hk hL s : CycleGroup C p k) : AlgebraicCycle X ℤ)
        Z.genericPoint = orderOfVanishing L s Z := by
  simp [chernComponentCycle]

/-- The component cycle vanishes at every point which is not the generic point of a prime
divisor. -/
theorem chernComponentCycle_eq_zero (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) (x : X)
    (hx : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x) :
    ((chernComponentCycle C p hk hL s : CycleGroup C p k) : AlgebraicCycle X ℤ) x = 0 :=
  weilDivisorCoeff_eq_zero _ x hx

end ComponentCycle

/-! ### The component rule -/

section Rule

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (k : ℤ) (L : X.Modules)

/-- The first Chern class component rule of a module `L` every restriction `L|_W` of which is
locally free of rank one in the stalkwise sense `Stacks.Divisors.IsTrivializedNear`: on each
integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` it is the divisor cycle of a chosen
nonzero meromorphic section of `L|_W`. -/
def chernComponentCycleRule
    (hL : ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
      ∀ x : W.subscheme, IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x) :
    FirstChernComponentCycleRule C p k := fun W hW hDim =>
  letI : IsIntegral W.subscheme := hW
  letI : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  chernComponentCycle C (W.subschemeι ≫ p) hDim (hL W hW)
    (exists_ne_zero_genericStalk (hL W hW (genericPoint W.subscheme))).choose

/-- The first Chern class component rule `Stacks.Chow.chernComponentCycleRule` for a module all of
whose restrictions to integral closed subschemes are invertible. -/
def chernComponentCycleRuleOfInvertible
    (hL : ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
      AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
        W.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback W.subschemeι).obj L)) :
    FirstChernComponentCycleRule C p k :=
  chernComponentCycleRule C p k L fun W hW =>
    have := hL W hW
    isTrivializedNear_of_isInvertible _

end Rule

end Stacks.Chow

end
