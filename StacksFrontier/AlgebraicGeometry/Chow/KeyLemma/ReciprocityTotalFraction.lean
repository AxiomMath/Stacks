module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityCanonical

/-!
# The Key Lemma on the total ring of fractions of a non-domain

Stacks 0EAX, the Key Lemma, says that for a two-dimensional Noetherian local ring `A` with total
ring of fractions `Q(A)` and `f, g ∈ Q(A)^*`

`∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(f, g)) = 0`,

where only finitely many terms are nonzero. The source states it for a domain, and
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero` proves it there. This file proves it
with no domain hypothesis, as the key formula Stacks 0EQU for algebraic spaces needs.

Without a domain hypothesis the total ring of fractions of `A_𝔮` is no longer the total ring of
fractions of `A`: an element `f ∈ Q(A)^*` reaches `Q(A_𝔮)^*` through the ring map
`Stacks.Chow.heightOneFractionMap : Q(A) → Q(A_𝔮)` induced by `A → A_𝔮`, which sends
nonzerodivisors to nonzerodivisors. The tame symbol on `Q(A_𝔮)` is
`Stacks.Chow.tameSymbolOfKrullDimOne`, which exists for every one-dimensional Noetherian local
ring (Stacks 0EAH).

The argument is the source's: writing `f = a / b` and `g = c / d` with `a, b, c, d`
nonzerodivisors of `A`, bilinearity of the symbol (Stacks 0EAI, 0EAJ) and additivity of the order
of vanishing expand each summand into four summands of Stacks 0EAW, and Stacks 0EAW
(`AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero`, proved without a domain hypothesis, in the
reindexed form `Stacks.Chow.finsum_tameSymbolOrderAt_canonical_eq_zero`) kills each of the four.

## Main definitions

* `Stacks.Chow.heightOneFractionMap` — the ring map `Q(A) → Q(A_𝔮)` at a height-one prime.
* `Stacks.Chow.totalFractionTameSymbolOrderAt` — the summand `ord_{A/𝔮}(∂_{A_𝔮}(f, g))`.

## Main results

* `Stacks.Chow.totalFractionTameSymbolOrderAt_regularFractionUnit` — on nonzerodivisors of `A`
  the summand is the summand of Stacks 0EAW for the canonical symbol.
* `Stacks.Chow.totalFractionTameSymbolOrderAt_eq_of_presentation` — the four-term expansion.
* `Stacks.Chow.finite_totalFractionTameSymbolOrderAt_support` — the finiteness assertion of
  Stacks 0EAX.
* `Stacks.Chow.finsum_heightOneOrd_tameSymbol_totalFraction_eq_zero` — **Stacks 0EAX for every
  two-dimensional Noetherian local ring**.

## References

* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section TotalFraction

variable {A : Type u} [CommRing A]

/-- **The map of total rings of fractions at a height-one prime.** The localization map
`A → A_𝔮` sends nonzerodivisors to nonzerodivisors, so it induces a ring map
`Q(A) → Q(A_𝔮)`. -/
noncomputable def heightOneFractionMap (p : HeightOnePrime A) :
    FractionRing A →+* FractionRing (Localization.AtPrime p.1.asIdeal) :=
  IsLocalization.map (FractionRing (Localization.AtPrime p.1.asIdeal))
    (algebraMap A (Localization.AtPrime p.1.asIdeal))
    (IsLocalization.nonZeroDivisors_le_comap (M := p.1.asIdeal.primeCompl)
      (S := Localization.AtPrime p.1.asIdeal))

/-- The map `Q(A) → Q(A_𝔮)` restricts to the localization map on `A`. -/
theorem heightOneFractionMap_algebraMap (p : HeightOnePrime A) (a : A) :
    heightOneFractionMap p (algebraMap A (FractionRing A) a) =
      algebraMap (Localization.AtPrime p.1.asIdeal)
        (FractionRing (Localization.AtPrime p.1.asIdeal))
        (algebraMap A (Localization.AtPrime p.1.asIdeal) a) :=
  IsLocalization.map_eq _ _

/-- A nonzerodivisor of `A`, viewed as a unit of `Q(A)` and pushed to `Q(A_𝔮)`, is the unit of
`Q(A_𝔮)` given by its image in `A_𝔮`. -/
theorem units_map_heightOneFractionMap_regularFractionUnit (p : HeightOnePrime A)
    (a : nonZeroDivisors A) :
    Units.map (heightOneFractionMap p).toMonoidHom
        (regularFractionUnit (Q := FractionRing A) a) =
      regularFractionUnit (Q := FractionRing (Localization.AtPrime p.1.asIdeal))
        (toLocalizationNonZeroDivisor p.1.asIdeal a) := by
  refine Units.ext ?_
  rw [Units.coe_map, regularFractionUnit_val, regularFractionUnit_val]
  exact heightOneFractionMap_algebraMap p (a : A)

variable [IsNoetherianRing A]

/-- **The summand of Stacks 0EAX on the total ring of fractions.** For a two-dimensional
Noetherian ring `A`, a height-one prime `𝔮` and `f, g ∈ Q(A)^*`, this is the order of vanishing
along `A / 𝔮` of the tame symbol `∂_{A_𝔮}(f, g)` of Stacks 0EAH, computed on the images of `f`
and `g` in `Q(A_𝔮)^*`. -/
noncomputable def totalFractionTameSymbolOrderAt (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (f g : (FractionRing A)ˣ) : ℤ :=
  heightOneOrd hdim p
    (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime p)
      (FractionRing (Localization.AtPrime p.1.asIdeal))
      (Units.map (heightOneFractionMap p).toMonoidHom f)
      (Units.map (heightOneFractionMap p).toMonoidHom g))

/-- The summand of Stacks 0EAX, written out. -/
theorem totalFractionTameSymbolOrderAt_eq_heightOneOrd (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (f g : (FractionRing A)ˣ) :
    totalFractionTameSymbolOrderAt hdim p f g =
      heightOneOrd hdim p
        (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime p)
          (FractionRing (Localization.AtPrime p.1.asIdeal))
          (Units.map (heightOneFractionMap p).toMonoidHom f)
          (Units.map (heightOneFractionMap p).toMonoidHom g)) := rfl

/-- **On nonzerodivisors of `A` the summand of Stacks 0EAX is the summand of Stacks 0EAW** for
the canonical symbol, because the tame symbol of Stacks 0EAH restricts on nonzerodivisors of
`A_𝔮` to the symbol of Stacks 02PZ. -/
theorem totalFractionTameSymbolOrderAt_regularFractionUnit (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (a c : nonZeroDivisors A) :
    totalFractionTameSymbolOrderAt hdim p (regularFractionUnit a) (regularFractionUnit c) =
      tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) a c := by
  rw [totalFractionTameSymbolOrderAt_eq_heightOneOrd,
    units_map_heightOneFractionMap_regularFractionUnit,
    units_map_heightOneFractionMap_regularFractionUnit,
    tameSymbolOfKrullDimOne_regularFractionUnit]
  rfl

/-- **The summand of Stacks 0EAX on a pair of fractions.** If `f = a / b` and `g = c / d` with
`a, b, c, d` nonzerodivisors of `A`, the summand is the alternating sum of the four summands of
Stacks 0EAW on the numerators and denominators, by bilinearity of the tame symbol and additivity
of the order of vanishing. -/
theorem totalFractionTameSymbolOrderAt_eq_of_presentation (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) {f g : (FractionRing A)ˣ} (a b c d : nonZeroDivisors A)
    (hf : f = regularFractionUnit (Q := FractionRing A) a *
      (regularFractionUnit (Q := FractionRing A) b)⁻¹)
    (hg : g = regularFractionUnit (Q := FractionRing A) c *
      (regularFractionUnit (Q := FractionRing A) d)⁻¹) :
    totalFractionTameSymbolOrderAt hdim p f g =
      tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) a c -
          tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) a d -
        tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) b c +
          tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) b d := by
  rw [← totalFractionTameSymbolOrderAt_regularFractionUnit hdim p a c,
    ← totalFractionTameSymbolOrderAt_regularFractionUnit hdim p a d,
    ← totalFractionTameSymbolOrderAt_regularFractionUnit hdim p b c,
    ← totalFractionTameSymbolOrderAt_regularFractionUnit hdim p b d]
  simp only [totalFractionTameSymbolOrderAt_eq_heightOneOrd, hf, hg, map_mul, map_inv,
    TameSymbol.map_mul_left, TameSymbol.map_mul_right, TameSymbol.inv_left,
    TameSymbol.inv_right, heightOneOrd_mul, heightOneOrd_inv]
  ring

/-- A combination `u - v - w + x` of integer functions with finite support has finite support. -/
private theorem finite_support_sub_sub_add {α : Type*} {u v w x : α → ℤ}
    (hu : (Function.support u).Finite) (hv : (Function.support v).Finite)
    (hw : (Function.support w).Finite) (hx : (Function.support x).Finite) :
    (Function.support (u - v - w + x)).Finite :=
  (((hu.union hv).union hw).union hx).subset fun p hp => by
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    simp [h] at hp

/-- **Stacks 0EAX, finiteness of the sum.** For two units of the total ring of fractions of a
two-dimensional Noetherian ring, only finitely many height-one primes contribute a nonzero
summand: the four-term expansion bounds the support by the supports of four summands of
Stacks 0EAW, each finite by `Stacks.Chow.finite_tameSymbolOrderAt_support`. -/
theorem finite_totalFractionTameSymbolOrderAt_support (hdim : ringKrullDim A = 2)
    (f g : (FractionRing A)ˣ) :
    {p : HeightOnePrime A | totalFractionTameSymbolOrderAt hdim p f g ≠ 0}.Finite := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) g
  refine (finite_support_sub_sub_add
    (finite_tameSymbolOrderAt_support hdim canonicalHeightOneSymbol a c)
    (finite_tameSymbolOrderAt_support hdim canonicalHeightOneSymbol a d)
    (finite_tameSymbolOrderAt_support hdim canonicalHeightOneSymbol b c)
    (finite_tameSymbolOrderAt_support hdim canonicalHeightOneSymbol b d)).subset fun p hp => ?_
  simpa [totalFractionTameSymbolOrderAt_eq_of_presentation hdim p a b c d hf hg] using hp

/-- **Stacks 0EAX, finiteness of the sum**, with the summand written out. -/
theorem finite_heightOneOrd_tameSymbol_totalFraction_support (hdim : ringKrullDim A = 2)
    (f g : (FractionRing A)ˣ) :
    {p : HeightOnePrime A | heightOneOrd hdim p
      (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime p)
        (FractionRing (Localization.AtPrime p.1.asIdeal))
        (Units.map (heightOneFractionMap p).toMonoidHom f)
        (Units.map (heightOneFractionMap p).toMonoidHom g)) ≠ 0}.Finite :=
  finite_totalFractionTameSymbolOrderAt_support hdim f g

/-- **Stacks Project, Tag 0EAX: the Key Lemma, for every two-dimensional Noetherian local
ring.** Let `A` be a two-dimensional Noetherian local ring, not necessarily a domain, with total
ring of fractions `Q(A)`, and let `f, g ∈ Q(A)^*`. Then

`∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(f, g)) = 0`,

the sum being over the height-one primes of `A`, with `∂_{A_𝔮}` the tame symbol of Stacks 0EAH on
the one-dimensional Noetherian local ring `A_𝔮`, applied to the images of `f` and `g` under
`Stacks.Chow.heightOneFractionMap`. Only finitely many terms are nonzero, by
`Stacks.Chow.finite_heightOneOrd_tameSymbol_totalFraction_support`.

The proof is the source's: writing `f = a / b`, `g = c / d` expands the sum into four reciprocity
sums of Stacks 0EAW, each of which vanishes. -/
@[stacks 02QJ "generalization: for every two-dimensional Noetherian local ring, on the total ring \
of fractions"]
theorem finsum_heightOneOrd_tameSymbol_totalFraction_eq_zero [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (f g : (FractionRing A)ˣ) :
    ∑ᶠ p : HeightOnePrime A, heightOneOrd hdim p
      (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime p)
        (FractionRing (Localization.AtPrime p.1.asIdeal))
        (Units.map (heightOneFractionMap p).toMonoidHom f)
        (Units.map (heightOneFractionMap p).toMonoidHom g)) = 0 := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) g
  let t : nonZeroDivisors A → nonZeroDivisors A → HeightOnePrime A → ℤ := fun x y p =>
    tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) x y
  have ht : ∀ x y : nonZeroDivisors A, (Function.support (t x y)).Finite := fun x y =>
    finite_tameSymbolOrderAt_support hdim canonicalHeightOneSymbol x y
  have hz : ∀ x y : nonZeroDivisors A, ∑ᶠ p, t x y p = 0 := fun x y =>
    finsum_tameSymbolOrderAt_canonical_eq_zero hdim x y
  have hsub : (Function.support fun p => t a c p - t a d p).Finite :=
    ((ht a c).union (ht a d)).subset (Function.support_sub _ _)
  have hsub' : (Function.support fun p => t a c p - t a d p - t b c p).Finite :=
    (hsub.union (ht b c)).subset (Function.support_sub _ _)
  calc
    _ = ∑ᶠ p : HeightOnePrime A, (t a c p - t a d p - t b c p + t b d p) :=
      finsum_congr fun p =>
        totalFractionTameSymbolOrderAt_eq_of_presentation hdim p a b c d hf hg
    _ = 0 := by
      rw [finsum_add_distrib hsub' (ht b d), finsum_sub_distrib hsub (ht b c),
        finsum_sub_distrib (ht a c) (ht a d), hz, hz, hz, hz]
      ring

end TotalFraction

end Stacks.Chow

end
