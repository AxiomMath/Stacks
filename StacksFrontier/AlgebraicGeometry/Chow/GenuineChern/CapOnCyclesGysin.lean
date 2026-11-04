module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleGysin
public import StacksCore.Tactic.StacksAttribute

/-!
# Intersecting with Chern classes commutes with the Gysin map of an effective Cartier divisor

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ` be finite locally free of rank `r` on `X` and let
`(ℒ, s, i : D ⟶ X)` be as in Definition 02T8: `ℒ` invertible, `s ∈ Γ(X, ℒ)` and `i` the closed
immersion of the zero scheme `D = Z(s)`. Then for every `0 ≤ j ≤ r` and every `α ∈ A_{k+1}(X)`

  `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`  in  `A_{k-j}(D)`,

where `i^*` is the Gysin map of [Stacks, Tag 02TO] and `c_j(-) ∩ -` is intersection with the
`j`-th Chern class of [Stacks, Tag 02U5], applied to a class through any cycle representing it
([Stacks, Tag 02U7]). This is [Stacks, Tag 0B7G].

The statement is `Stacks.Chow.GenuineChern.chernCap_gysin` for the cap products characterized by
the projective-bundle relation of [Stacks, Tag 02U6], transported along the identification
`Stacks.Chow.GenuineChern.chernCap_mk_eq_chernCapOnCycles` of those cap products with the
operation of Stacks 02U5.

## Main results

* `Stacks.Chow.GenuineChern.chernCapOnCycles_gysin` — **Stacks 0B7G**, for the operation of
  Stacks 02U5 on representatives of `α` and of `i^*α`.

## References

* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0B7G.** Let `ℰ` be finite locally free of rank `r` on `X` and let
`(ℒ, s, i : D ⟶ X)` be as in Definition 02T8. Let `α ∈ A_{k+1}(X)`, let `a` be a cycle
representing `α` and `b` a cycle representing `i^*α ∈ A_k(D)`. Then for every `0 ≤ j ≤ r`

  `c_j(ℰ|_D) ∩ b = i^*(c_j(ℰ) ∩ a)`  in  `A_{k-j}(D)`,

for the Gysin map of Stacks 02TO and intersection with Chern classes of Stacks 02U5; that is,
`c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`. -/
@[stacks 0B7G]
theorem chernCapOnCycles_gysin (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C sX (k + 1)) (a : CycleGroup C sX (k + 1))
    (ha : QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1)) a = α)
    (b : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) k)
    (hb : QuotientAddGroup.mk'
        (rationalEquivalences C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) k) b =
      gysinChowOfInvertible C sX k L s α) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
      (Stacks.Divisors.zeroScheme X L s).subschemeι E r
    chernCapOnCycles C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj E) r k j b =
      gysinChowOfInvertible C sX (k - (j : ℤ)) L s
        (chowGroupCast C sX (show k + 1 - (j : ℤ) = k - (j : ℤ) + 1 by omega)
          (chernCapOnCycles C sX E r (k + 1) j a)) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (Stacks.Divisors.zeroScheme X L s).subschemeι E r
  rw [← chernCap_mk_eq_chernCapOnCycles, hb, ← chernCap_mk_eq_chernCapOnCycles, ha]
  exact chernCap_gysin C sX L s E r k j α

end Stacks.Chow.GenuineChern

end
