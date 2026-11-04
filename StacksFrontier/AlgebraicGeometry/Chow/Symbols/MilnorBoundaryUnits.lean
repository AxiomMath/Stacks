module

public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MilnorBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit

/-!
# The tame symbol of two units, and the Milnor K₂ boundary it kills

Let `A` be a one-dimensional Noetherian local domain with fraction field `K`. The tame symbol of
Stacks 02Q1 is trivial on a pair of elements of `Kˣ` which both come from units of `A`: by Stacks
02Q2 the symbol of a unit of `A` against a nonzerodivisor `b` is the residue of that unit raised
to the order of vanishing of `b`, and the order of vanishing of a unit is zero.

Consequently the degree-two Milnor K-boundary
`AlgebraicGeometry.milnorKTwoTameSymbol` of Stacks 0GU9 kills the pure symbol `{f, g}` whenever
`f` and `g` both come from units of `A`.

This is the local input to the local finiteness of the first differential of the complex of
Stacks 0GU9: at all but finitely many points of an integral scheme a prescribed pair of nonzero
rational functions is a pair of units of the local ring, and there the boundary of the
corresponding pure symbol vanishes.

## Scope

Both results are direct consequences of their stated hypotheses on `A`, `K` and the two
units; no further input is assumed.

## Main results

* `AlgebraicGeometry.ord_unit_eq_zero` — the order of vanishing of a unit is zero.
* `AlgebraicGeometry.tameSymbol_eq_one_of_eq_algebraMap_units` — the tame symbol of two elements
  of `Kˣ` coming from units of `A` is trivial.
* `AlgebraicGeometry.milnorKTwoTameSymbol_pureSymbol_eq_zero_of_eq_algebraMap_units` — the
  degree-two Milnor K-boundary kills the pure symbol of two such elements.

## References

* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 02Q2](https://stacks.math.columbia.edu/tag/02Q2)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

/-- The order of vanishing of a unit is zero: the ideal it generates is the whole ring, so the
quotient by that ideal is trivial and has length zero. -/
theorem ord_unit_eq_zero {A : Type u} [CommRing A] (u : Aˣ) : Ring.ord A (u : A) = 0 := by
  have h : Ideal.span {(u : A)} = ⊤ := Ideal.span_singleton_eq_top.mpr u.isUnit
  simp_all [Ring.ord, Submodule.Quotient.subsingleton_iff]

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] in
/-- An element of `Kˣ` which is the image of a unit `u` of `A` is, as a unit, the image of `u`
under the canonical map of unit groups. -/
theorem units_eq_map_units_of_eq_algebraMap {f : Kˣ} {u : Aˣ}
    (hf : (f : K) = algebraMap A K (u : A)) :
    f = (IsLocalization.map_units K
      (⟨(u : A), isRegular_iff_mem_nonZeroDivisors.mp u.isUnit.isRegular⟩ :
        nonZeroDivisors A)).unit :=
  Units.ext hf

/-- **The tame symbol of two units is trivial.** If `f` and `g` in `Kˣ` are the images of units
`u` and `v` of `A`, then the tame symbol of Stacks 02Q1 sends them to `1`: by Stacks 02Q2 the
symbol is the residue of `u` raised to the order of vanishing of `v`, and that order is zero
because `v` is a unit. -/
theorem tameSymbol_eq_one_of_eq_algebraMap_units (hdim : ringKrullDim A = 1) {f g : Kˣ}
    {u v : Aˣ} (hf : (f : K) = algebraMap A K (u : A))
    (hg : (g : K) = algebraMap A K (v : A)) :
    tameSymbol (K := K) hdim f g = 1 := by
  rw [units_eq_map_units_of_eq_algebraMap hf, units_eq_map_units_of_eq_algebraMap hg]
  refine Units.ext ?_
  rw [(tameSymbol (K := K) hdim).eq_moduleSymbol (u : A) (v : A) u.isUnit.isRegular
    v.isUnit.isRegular]
  rw [moduleSymbol_unit_left_ring u (v : A) v.isUnit.isRegular.isSMulRegular hdim,
    ord_unit_eq_zero v]
  simp

/-- **The degree-two Milnor K-boundary kills a pure symbol of two units.** If `f` and `g` in
`Kˣ` are the images of units of `A`, then the pure symbol `{f, g}` of the degree-two Milnor
K-group of `K` is sent to zero by the boundary of Stacks 0GU9. -/
theorem milnorKTwoTameSymbol_pureSymbol_eq_zero_of_eq_algebraMap_units
    (hdim : ringKrullDim A = 1) {f g : Kˣ} {u v : Aˣ}
    (hf : (f : K) = algebraMap A K (u : A)) (hg : (g : K) = algebraMap A K (v : A)) :
    milnorKTwoTameSymbol (K := K) hdim (milnorKTwoPureSymbol K f g) = 0 := by
  rw [milnorKTwoTameSymbol_pureSymbol hdim f g,
    tameSymbol_eq_one_of_eq_algebraMap_units hdim hf hg]
  simp

end AlgebraicGeometry

end

end
