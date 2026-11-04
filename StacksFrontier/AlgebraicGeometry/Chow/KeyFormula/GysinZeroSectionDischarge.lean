module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# The Gysin single-component vanishing for the zero section

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be an integral,
locally Noetherian scheme locally of finite type over `S` of delta-dimension `k + 2`, let `M` be
an invertible `𝒪_Y`-module and let `h` be a nonzero rational function on `Y`. The
single-component input to Stacks 02TO,
`Stacks.Chow.GysinOfInvertibleKillsPrincipalDivisorOnComponent`, asks for the Gysin cycle of
`div(h)` to be rationally equivalent to zero on the zero scheme `Z(s)` of a global section `s` of
`M`. This file settles the degenerate case `s = 0`.

## Main results

* `Stacks.Divisors.zeroScheme_zero_eq_bot` — the zero scheme of the zero section is the trivial
  ideal sheaf.
* `Stacks.Chow.gysinRule_extendCycleGroup_eq_zero_of_section_eq_zero` — the single-component
  vanishing of Stacks 02TO for the zero section, with no hypothesis.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **The zero scheme of the zero section is the whole scheme**: its ideal sheaf is `⊥`. -/
theorem zeroScheme_zero_eq_bot {Y : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    zeroScheme Y M (0 : Γ(M, ⊤)) = ⊥ := by
  refine Scheme.IdealSheafData.ext (funext fun U ↦ le_antisymm ?_ bot_le)
  refine (Scheme.IdealSheafData.ideal_ofIdeals_le _ U).trans ?_
  rw [Ideal.span_le]
  rintro a ⟨φ, rfl⟩
  simp

end Stacks.Divisors

namespace Stacks.Chow

/-- **The single-component input to Stacks 02TO for the zero section, with no hypothesis.** On an
integral, locally Noetherian scheme `Y` of delta-dimension `k + 2` locally of finite type over
the base, the Gysin cycle of the principal divisor of a nonzero rational function, taken for the
zero section of an invertible module `M`, is rationally equivalent to zero on the zero scheme
`Z(0)`. -/
theorem gysinRule_extendCycleGroup_eq_zero_of_section_eq_zero
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    [IsIntegral Y] [IsLocallyNoetherian Y] {k : ℤ}
    (hn : schemeDeltaDimension C q = ((k + 1 + 1 : ℤ) : EInt))
    (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (h : Y.functionField) (hh : h ≠ 0)
    (β : CycleGroup C q (k + 1)) (hβ : (β : AlgebraicCycle Y ℤ) = principalCycle Y h) :
    IsRationallyEquivalentToZero C
        ((Stacks.Divisors.zeroScheme Y M (0 : Γ(M, ⊤))).subschemeι ≫ q) k
      ((gysinRule C q k M 0 (firstChernComponentClass C q k M)).extendCycleGroup β) := by
  set i := (Stacks.Divisors.zeroScheme Y M (0 : Γ(M, ⊤))).subschemeι with hi
  have hiso : IsIso i :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (Stacks.Divisors.zeroScheme_zero_eq_bot M)
  have hmk : gysinHomomorphismOfInvertible C q k M (0 : Γ(M, ⊤)) β =
      QuotientAddGroup.mk' (rationalEquivalences C (i ≫ q) k)
        ((gysinRule C q k M 0 (firstChernComponentClass C q k M)).extendCycleGroup β) := rfl
  have h9 := properChowPushforward_gysinHomomorphismOfInvertible C q k M (0 : Γ(M, ⊤)) β
  rw [firstChernCapKillsPrincipalDivisor C k Y q hn M h hh β hβ, hmk,
    properChowPushforward_mk] at h9
  have h2 := (QuotientAddGroup.eq_zero_iff _).1 h9
  have hinv : inv i ≫ (i ≫ q) = q := by simp
  have h3 := properPushforwardFactorsThroughRationalEquivalence_of_isIso C q (i ≫ q) (inv i)
    hinv k _ h2
  rwa [properPushforward_properPushforward C (i ≫ q) q (i ≫ q) i (inv i) rfl hinv k,
    properPushforward_congr C (i ≫ q) (i ≫ q) (i ≫ inv i) (𝟙 _) (by simp) (by simp)
      (Category.id_comp _) k, properPushforward_id] at h3

end Stacks.Chow

end
