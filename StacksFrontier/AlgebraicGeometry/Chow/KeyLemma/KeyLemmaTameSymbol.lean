module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.FormulaComparison

/-!
# The Key Lemma for the tame symbol of Stacks 0EAQ

Stacks 0EAX, the Key Lemma: let `A` be a two-dimensional Noetherian local domain with fraction
field `K`, let `f, g ∈ K^*`, and let `𝔮₁, …, 𝔮_t` be the height-one primes `𝔮` of `A` such that
`f` or `g` is not an element of `A_𝔮^*`. Then

`∑_{i = 1, …, t} ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(f, g)) = 0`,

or, equivalently, `∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(f, g)) = 0`, since
`∂_{A_𝔮}(f, g) = 1` whenever `f, g ∈ A_𝔮^*`. Here `∂_{A_𝔮}` is the tame symbol of Section 0EAH,
the map `Q(A_𝔮)^* × Q(A_𝔮)^* → κ(𝔮)^*` that the recipe of Stacks 0EAQ defines on nonzerodivisors
and Stacks 0EAS extends; in the library it is `Stacks.Chow.formulaTameSymbol`.

The source proves the Key Lemma from Stacks 0EAW by bilinearity. The library has Stacks 0EAW and
the bilinear reduction for the symbol `d_{A_𝔮}` of Stacks 02PZ, in the form of the analogue of
the key lemma, Stacks 02QJ (`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`). The two
symbols are the same map: `Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol` proves that
the extension of `d_{A_𝔮}` to `Q(A_𝔮)^*` is the symbol of Stacks 0EAQ, on every one-dimensional
Noetherian local ring. This file rewrites along that equality.

## Main results

* `Stacks.Chow.formulaTameSymbol_eq_one_of_units` — `∂_{A_𝔮}(f, g) = 1` when `f, g ∈ A_𝔮^*`.
* `Stacks.Chow.finite_setOf_not_localUnit` — only finitely many height-one primes `𝔮` have `f`
  or `g` outside `A_𝔮^*`.
* `Stacks.Chow.finsum_heightOneOrd_formulaTameSymbol_eq_zero` — **Stacks 0EAX**, the second
  displayed form.
* `Stacks.Chow.sum_heightOneOrd_formulaTameSymbol_eq_zero` — **Stacks 0EAX**, the first displayed
  form, the sum over the primes where `f` or `g` is not a local unit.

## References

* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 02QJ](https://stacks.math.columbia.edu/tag/02QJ)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section Formula

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- **The tame symbol of Stacks 0EAQ is trivial on local units.** If `f, g ∈ K^*` are images of
units of `A_𝔮`, then `∂_{A_𝔮}(f, g) = 1`: on nonzerodivisors of `A_𝔮` the symbol is the formula
of Stacks 0EAQ, which is `1` on two units. -/
theorem formulaTameSymbol_eq_one_of_units (p : HeightOnePrime A)
    {f g : (FractionRing A)ˣ} (u v : (Localization.AtPrime p.1.asIdeal)ˣ)
    (hu : algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) u = f)
    (hv : algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) v = g) :
    formulaTameSymbol (ringKrullDim_localization_heightOnePrime p) (FractionRing A) f g = 1 := by
  have hf : f = regularFractionUnit (Q := FractionRing A)
      (⟨u, u.isUnit.mem_nonZeroDivisors⟩ : nonZeroDivisors (Localization.AtPrime p.1.asIdeal)) :=
    Units.ext (by rw [regularFractionUnit_val]; exact hu.symm)
  have hg : g = regularFractionUnit (Q := FractionRing A)
      (⟨v, v.isUnit.mem_nonZeroDivisors⟩ : nonZeroDivisors (Localization.AtPrime p.1.asIdeal)) :=
    Units.ext (by rw [regularFractionUnit_val]; exact hv.symm)
  rw [hf, hg, formulaTameSymbol_regularFractionUnit]
  exact tameSymbolValue_eq_one_of_isUnit u.isUnit v.isUnit

omit [IsNoetherianRing A] in
/-- A quotient `a / b` of elements of `A` outside a prime `𝔮` is the image of a unit of `A_𝔮`. -/
theorem exists_unit_eq_of_notMem (p : HeightOnePrime A) {f : (FractionRing A)ˣ}
    (a b : nonZeroDivisors A)
    (hf : f = regularFractionUnit (Q := FractionRing A) a *
      (regularFractionUnit (Q := FractionRing A) b)⁻¹)
    (ha : (a : A) ∉ p.1.asIdeal) (hb : (b : A) ∉ p.1.asIdeal) :
    ∃ u : (Localization.AtPrime p.1.asIdeal)ˣ,
      algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) u = f := by
  obtain ⟨ua, hua⟩ := isUnit_toLocalizationNonZeroDivisor p.1.asIdeal a ha
  obtain ⟨ub, hub⟩ := isUnit_toLocalizationNonZeroDivisor p.1.asIdeal b hb
  refine ⟨ua * ub⁻¹, ?_⟩
  have hφ : ∀ x : A, algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A)
      (algebraMap A (Localization.AtPrime p.1.asIdeal) x) = algebraMap A (FractionRing A) x :=
    fun x => (IsScalarTower.algebraMap_apply A (Localization.AtPrime p.1.asIdeal)
      (FractionRing A) x).symm
  have hua' : algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) ua =
      algebraMap A (FractionRing A) a := by
    rw [hua]; exact hφ a
  have hub' : algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) ub =
      algebraMap A (FractionRing A) b := by
    rw [hub]; exact hφ b
  have hinv : algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) ↑ub⁻¹ =
      (algebraMap A (FractionRing A) b)⁻¹ := by
    rw [← hub']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  rw [Units.val_mul, map_mul, hua', hinv, hf, Units.val_mul, Units.val_inv_eq_inv_val,
    regularFractionUnit_val, regularFractionUnit_val]

/-- **Only finitely many height-one primes see a non-unit.** For `f, g ∈ K^*` the set of
height-one primes `𝔮` of `A` such that `f` or `g` is not an element of `A_𝔮^*` is finite: writing
`f = a / b` and `g = c / d`, it lies among the finitely many height-one primes containing one of
`a, b, c, d`. -/
theorem finite_setOf_not_localUnit (f g : (FractionRing A)ˣ) :
    {p : HeightOnePrime A |
      ¬ ((∃ u : (Localization.AtPrime p.1.asIdeal)ˣ,
          algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) u = f) ∧
        ∃ v : (Localization.AtPrime p.1.asIdeal)ˣ,
          algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) v = g)}.Finite := by
  obtain ⟨a, b, hf⟩ := exists_presentation_fractionRing f
  obtain ⟨c, d, hg⟩ := exists_presentation_fractionRing g
  refine ((((finite_heightOnePrime_mem a.2).union (finite_heightOnePrime_mem b.2)).union
    (finite_heightOnePrime_mem c.2)).union (finite_heightOnePrime_mem d.2)).subset
    fun p hp => ?_
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hmem
  exact hp ⟨exists_unit_eq_of_notMem p a b hf hmem.1.1.1 hmem.1.1.2,
    exists_unit_eq_of_notMem p c d hg hmem.1.2 hmem.2⟩

/-- **Stacks Project, Tag 0EAX: the Key Lemma, second displayed form.** Let `A` be a
two-dimensional Noetherian local domain with fraction field `K` and let `f, g ∈ K^*`. Then

`∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(f, g)) = 0`,

the sum over all height-one primes of `A`, where `∂_{A_𝔮}` is the tame symbol of Section 0EAH
given by the recipe of Stacks 0EAQ (`Stacks.Chow.formulaTameSymbol`) on the one-dimensional
Noetherian local ring `A_𝔮`, whose total ring of fractions is `K`.

By `Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol` this symbol is the extension of the
symbol `d_{A_𝔮}` of Stacks 02PZ, for which the identity is the analogue of the key lemma, Stacks
02QJ (`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`). -/
@[stacks 0EAX "the second displayed form, the sum over all height-one primes, for the tame \
symbol of Stacks 0EAQ"]
theorem finsum_heightOneOrd_formulaTameSymbol_eq_zero [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (f g : (FractionRing A)ˣ) :
    ∑ᶠ p : HeightOnePrime A, heightOneOrd hdim p
      (formulaTameSymbol (ringKrullDim_localization_heightOnePrime p) (FractionRing A) f g) =
      0 := by
  refine (finsum_congr fun p => ?_).trans (finsum_fracTameSymbolOrderAt_canonical_eq_zero hdim f g)
  rw [← tameSymbolOfKrullDimOne_eq_formulaTameSymbol]
  rfl

/-- **Stacks Project, Tag 0EAX: the Key Lemma, first displayed form.** Let `A` be a
two-dimensional Noetherian local domain with fraction field `K`, let `f, g ∈ K^*`, and let
`𝔮₁, …, 𝔮_t` be the height-one primes `𝔮` of `A` such that `f` or `g` is not an element of
`A_𝔮^*` — a finite set, by `Stacks.Chow.finite_setOf_not_localUnit`. Then

`∑_{i = 1, …, t} ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(f, g)) = 0`,

with `∂_{A_𝔮}` the tame symbol of Stacks 0EAQ (`Stacks.Chow.formulaTameSymbol`). The terms left
out of the second displayed form vanish because `∂_{A_𝔮}(f, g) = 1` when `f, g ∈ A_𝔮^*`
(`Stacks.Chow.formulaTameSymbol_eq_one_of_units`). -/
@[stacks 0EAX "the first displayed form, the sum over the height-one primes at which f or g is \
not a local unit, for the tame symbol of Stacks 0EAQ"]
theorem sum_heightOneOrd_formulaTameSymbol_eq_zero [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (f g : (FractionRing A)ˣ) :
    ∑ p ∈ (finite_setOf_not_localUnit f g).toFinset, heightOneOrd hdim p
      (formulaTameSymbol (ringKrullDim_localization_heightOnePrime p) (FractionRing A) f g) =
      0 := by
  rw [← finsum_eq_sum_of_support_subset _ ?_]
  · exact finsum_heightOneOrd_formulaTameSymbol_eq_zero hdim f g
  · intro p hp
    rw [Set.Finite.coe_toFinset]
    by_contra hns
    simp only [Set.mem_ofPred_eq, not_not] at hns
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hns
    exact hp (by dsimp only; rw [formulaTameSymbol_eq_one_of_units p u v hu hv, heightOneOrd_one])

end Formula

end Stacks.Chow

end
