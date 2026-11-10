module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityFraction
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Reciprocity
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.DeterminantComparison

/-!
# The reciprocity sum vanishes over a normal domain

Let `A` be a two-dimensional Noetherian normal local domain. Each of its height-one
localizations is a discrete valuation ring, so each carries the tame symbol
`Stacks.Chow.normalHeightOneSymbol`, and the reciprocity sum

`∑_𝔮 ord_{A/𝔮}(∂_{A_𝔮}(a, b))`

is defined with no symbol data supplied by hand. This file proves that it vanishes, for two
nonzerodivisors of `A` and then for two units of the fraction field.

The sum is already known to vanish for the symbol built from the determinants of two-periodic
complexes, `AlgebraicGeometry.sum_ord_localTameSymbol_eq_zero`. At a discrete valuation ring that
symbol is the tame symbol, by
`Stacks.Chow.dvrTameSymbol_eq_tameSymbol`, so the two summands agree at every height-one prime
and the two sums are the same sum. The passage from nonzerodivisors to the fraction field is
`Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_iff_forall_nonZeroDivisors`.

Normality is used only to make the localizations discrete valuation rings, which is what supplies
the symbol; the source asks for no such hypothesis.

## Main results

* `Stacks.Chow.normalHeightOneSymbol_eq_localTameSymbol` — over a Noetherian normal domain the
  tame symbol at a height-one prime is the determinant symbol there.
* `Stacks.Chow.nonempty_heightOnePrime_of_ringKrullDim_eq_two` — the sum is indexed by a nonempty
  set.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_isIntegrallyClosed` — the reciprocity sum of
  two nonzerodivisors vanishes.
* `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_of_isIntegrallyClosed` — the reciprocity sum
  of two units of the fraction field vanishes.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 02QJ](https://stacks.math.columbia.edu/tag/02QJ)
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

omit [IsDomain A] [IsNoetherianRing A] in
/-- An automorphism of the fraction field over the base ring is the identity: a localization
admits only one algebra endomorphism. -/
theorem units_map_fractionRing_algEquiv_symm (f : (FractionRing A)ˣ) :
    Units.map (FractionRing.algEquiv A (FractionRing A)).symm.toRingHom.toMonoidHom f = f := by
  have h : (FractionRing.algEquiv A (FractionRing A)).symm.toAlgHom = AlgHom.id A _ :=
    @Subsingleton.elim _ (IsLocalization.algHom_subsingleton (nonZeroDivisors A)) _ _
  refine Units.ext ?_
  change (FractionRing.algEquiv A (FractionRing A)).symm.toAlgHom ((f : FractionRing A)) = _
  rw [h]
  rfl

variable [IsIntegrallyClosed A]

/-- **Over a Noetherian normal domain the tame symbol at a height-one prime is the determinant
symbol there.** The localization is a discrete valuation ring, where the symbol built from the
determinants of two-periodic complexes is the classical tame symbol
(`Stacks.Chow.dvrRegularTameSymbol_eq_tameSymbol`), and the structure map of `A` into its
fraction field factors through the localization. -/
theorem normalHeightOneSymbol_eq_localTameSymbol (p : HeightOnePrime A)
    (a b : nonZeroDivisors A) :
    normalHeightOneSymbol p (toLocalizationNonZeroDivisor p.1.asIdeal a)
        (toLocalizationNonZeroDivisor p.1.asIdeal b) =
      localTameSymbol (A := A) (K := FractionRing A) (heightOnePrimeEquivIdeal p)
        (regularFractionUnit a) (regularFractionUnit b) := by
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
    isDiscreteValuationRing_localization_of_height_eq_one p.1.asIdeal p.2
  have hone : ringKrullDim (Localization.AtPrime p.1.asIdeal) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one _
  have hnorm : normalHeightOneSymbol p =
      dvrRegularTameSymbol (A := Localization.AtPrime p.1.asIdeal)
        (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
          (Localization.AtPrime p.1.asIdeal))) := rfl
  have hloc : localTameSymbol (A := A) (K := FractionRing A)
        (heightOnePrimeEquivIdeal p) (regularFractionUnit a) (regularFractionUnit b) =
      AlgebraicGeometry.tameSymbol (A := Localization.AtPrime p.1.asIdeal)
        (K := FractionRing A) hone
        (Units.map (FractionRing.algEquiv A (FractionRing A)).symm.toRingHom.toMonoidHom
          (regularFractionUnit a))
        (Units.map (FractionRing.algEquiv A (FractionRing A)).symm.toRingHom.toMonoidHom
          (regularFractionUnit b)) := rfl
  rw [hnorm, hloc, units_map_fractionRing_algEquiv_symm,
    units_map_fractionRing_algEquiv_symm,
    dvrRegularTameSymbol_eq_tameSymbol (K := FractionRing A) hone _
      (toLocalizationNonZeroDivisor p.1.asIdeal a)
      (toLocalizationNonZeroDivisor p.1.asIdeal b),
    regularFractionUnit_toLocalizationNonZeroDivisor p a,
    regularFractionUnit_toLocalizationNonZeroDivisor p b]

variable [IsLocalRing A]

omit [IsIntegrallyClosed A] in
/-- **The sum of the reciprocity relation is indexed by a nonempty set.** A two-dimensional local
ring is not a field, so its maximal ideal contains a nonzero nonunit, and a minimal prime over
that element has height one. -/
theorem nonempty_heightOnePrime_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) :
    Nonempty (HeightOnePrime A) := by
  have hnf : ¬ IsField A := by
    intro h
    rw [ringKrullDim_eq_zero_of_isField h] at hdim
    exact absurd hdim (by decide)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := maximalIdeal A) fun h => hnf (isField_iff_maximalIdeal_eq.mpr h)
  exact nonempty_heightOnePrime hx0 fun hu => (notMem_maximalIdeal.mpr hu) hxm

/-- **The reciprocity sum of two nonzerodivisors vanishes over a two-dimensional Noetherian
normal local domain.** At every height-one prime the tame symbol of
`Stacks.Chow.normalHeightOneSymbol` is the determinant symbol, whose reciprocity sum vanishes by
`AlgebraicGeometry.sum_ord_localTameSymbol_eq_zero`.

This is the reciprocity relation Stacks 0EAW under the extra hypothesis that `A` is a normal
domain, which is what makes the localizations discrete valuation rings and so supplies the
symbol. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_isIntegrallyClosed (hdim : ringKrullDim A = 2)
    (a b : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (normalHeightOneSymbol p) a b = 0 := by
  obtain ⟨_, hsum⟩ := AlgebraicGeometry.sum_ord_localTameSymbol_eq_zero
    (A := A) (K := FractionRing A) hdim (regularFractionUnit a) (regularFractionUnit b)
  rw [← finsum_comp_equiv (heightOnePrimeEquivIdeal (A := A))] at hsum
  refine Eq.trans (finsum_congr fun p => ?_) hsum
  exact congrArg (heightOneOrd hdim p) (normalHeightOneSymbol_eq_localTameSymbol p a b)

/-- **The reciprocity sum of two units of the fraction field vanishes over a two-dimensional
Noetherian normal local domain.** The reduction of
`Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_iff_forall_nonZeroDivisors` turns the relation
on the fraction field into the relation on nonzerodivisors of `A`.

This is the key lemma Stacks 0EAX under the extra hypothesis that `A` is a normal domain. -/
theorem fracTameSymbolOrderAt_finsum_eq_zero_of_isIntegrallyClosed (hdim : ringKrullDim A = 2)
    (f g : (FractionRing A)ˣ) :
    ∑ᶠ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (normalHeightOneSymbol p) f g = 0 :=
  (fracTameSymbolOrderAt_finsum_eq_zero_iff_forall_nonZeroDivisors hdim
    normalHeightOneSymbol).mpr
      (fun x y => tameSymbolOrderAt_finsum_eq_zero_of_isIntegrallyClosed hdim x y) f g

end Stacks.Chow

end
