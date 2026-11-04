module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesOfRank
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput

/-!
# The first Chern class of an invertible module on an integral scheme

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S`, integral of
delta-dimension `n`, and `ℒ` an invertible `𝒪_X`-module, which is finite locally free of rank one
([Stacks, Tag 0B8M]). [Stacks, Tag 02U2] says that the first Chern class `c_1(ℒ) ∩ [X]` of
[Stacks, Tag 02U0], read on the projective bundle `𝐏(ℒ)`, is the Weil divisor class
`c₁(ℒ) ∩ [X]` of [Stacks, Tag 02SJ], the class of the divisor of any nonzero meromorphic section.

The Chern classes of 02U0 are those of `Stacks.Chow.chernClassFundamentalOfRank`, defined on the
genuine projective bundle `Stacks.Chow.bundle ℒ` with its twist `𝒪(1)`. The source's proof
observes that `𝐏(ℒ) = X` with `𝒪(1) = ℒ`; here the bundle is not literally `X`, and the same
observation enters as `𝒪(1) ≅ π^*ℒ` (`Stacks.Chow.GenuineChern.bundleTwistIsoOfRankOne`) together
with the uniqueness half of the projective bundle formula, which is
`Stacks.Chow.GenuineChern.chernCap_one_eq_invCap`: `c_1(ℒ) ∩ α = c₁(ℒ) ∩ α` for every class `α`.
At `α = [X]` the right-hand side is the cap product of Stacks 02SO on the fundamental cycle, which
is the Weil divisor class by
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental`.

## Main results

* `Stacks.Chow.chernClassFundamentalOfRank_one_eq_firstChernClassCapFundamental` —
  **Stacks 02U2**.

## References

* [Stacks Project, Tag 02U2](https://stacks.math.columbia.edu/tag/02U2)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] (n : ℤ) (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 02U2.** Let `X` be locally of finite type over the base of a Chow situation, integral
of delta-dimension `n`, and let `ℒ` be an invertible `𝒪_X`-module, so of rank one. The first Chern
class `c_1(ℒ) ∩ [X] ∈ A_{n-1}(X)` of Stacks 02U0, defined by the relation
`c₁(𝒪_{𝐏(ℒ)}(1)) ∩ π^*c_0 = π^*c_1` with `c_0 = [X]` on the projective bundle of `ℒ`, is the
Weil divisor class `c₁(ℒ) ∩ [X]` of Stacks 02SJ. -/
@[stacks 02U2]
theorem chernClassFundamentalOfRank_one_eq_firstChernClassCapFundamental :
    letI := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
    chowGroupCast C p (show n - ((1 : Fin (1 + 1)) : ℤ) = n - 1 by simp)
        (chernClassFundamentalOfRank L 1 C p n 1) =
      firstChernClassCapFundamental C p n hn L := by
  let := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
  have h := GenuineChern.chernCap_one_eq_invCap C p L n
    (QuotientAddGroup.mk' (rationalEquivalences C p n)
      (cycleAssociatedToClosedSubscheme C p (𝟙 X) n))
  have hX : ∀ (m : ℤ) (hm : n = m), chowGroupCast C p hm
      (QuotientAddGroup.mk' (rationalEquivalences C p n)
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) n)) =
      QuotientAddGroup.mk' (rationalEquivalences C p m)
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) m) := by
    rintro m rfl
    rfl
  rw [hX, invCap_capOnChow_mk,
    firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental C p n hn L]
    at h
  rw [← h]
  rfl

end Stacks.Chow

end
