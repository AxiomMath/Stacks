module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder

/-!
# The reciprocity sum of tame-symbol orders

Let `A` be a two-dimensional Noetherian ring and `a, b` nonzerodivisors of `A`. For each
height-one prime `𝔮` the localization `A_𝔮` carries a tame symbol `∂_{A_𝔮}` in the sense of
Stacks 0EAH, and the summand

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) ∈ ℤ`

of the reciprocity relation Stacks 0EAW is `Stacks.Chow.tameSymbolOrderAt`. Only finitely many
height-one primes contribute, by `Stacks.Chow.finite_tameSymbolOrderAt_support`, so the
reciprocity sum

`∑ᶠ 𝔮, ord_{A/𝔮}(∂_{A_𝔮}(a, b))`

is a finite sum of integers. This file establishes the properties of that sum which do not
depend on the finite modification of Stacks 0EAG: it is bi-additive and skew, it is a finite sum
over any finite set carrying the contributing primes, and it vanishes whenever one of the two
arguments is a unit of `A`, or more generally whenever the two arguments admit at every
height-one prime a simultaneous power factorization whose unit parts come from `A`.

The last of these is the *globally prepared* case of Stacks 0EAW. The source reaches a prepared
case only after a finite modification, and there the unit parts `u_𝔮`, `v_𝔮` are units of `A_𝔮`
rather than of `A`; it then computes the summand through the multiplicities `e_A(M_𝔮, a, b)` of
two-periodic complexes. When the unit parts come from `A` their orders of vanishing along
`A / 𝔮` are zero, so each summand vanishes on its own and no multiplicity computation is needed:
that is proved here from `Stacks.Chow.tameSymbolOrderAt_eq_of_factorization`, the value of the
summand on a factorization.

As in `Stacks.Chow.finite_tameSymbolOrderAt_support`, none of this needs `A` to be local.

## Main results

* `Stacks.Chow.heightOneOrd_eq_zero_of_isUnit` — a unit of `A` has order of vanishing zero along
  every height-one prime.
* `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_isUnit_left`,
  `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_isUnit_right` — the summand of Stacks 0EAW vanishes
  at every height-one prime when one argument is a unit of `A`. This strengthens
  `Stacks.Chow.tameSymbolOrderAt_eq_zero`, which asks both arguments to avoid the prime.
* `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_isUnit` — the summand vanishes at a
  prime where the two arguments admit a simultaneous power factorization with unit parts coming
  from `A`.
* `Stacks.Chow.tameSymbolOrderAt_finsum_mul_left`,
  `Stacks.Chow.tameSymbolOrderAt_finsum_mul_right`,
  `Stacks.Chow.tameSymbolOrderAt_finsum_add_swap` — the reciprocity sum is bi-additive and skew.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_sum` — the reciprocity sum as a finite sum.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_isUnit_left`,
  `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_isUnit_right`,
  `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_global_factorization` — cases of the
  reciprocity relation Stacks 0EAW.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_multiplicity` — the reduction of Stacks 0EAW
  to the multiplicity identity of the source.

## Implementation notes

The order of vanishing `Stacks.Chow.heightOneOrd` is `ordInt` of the quotient `A / 𝔮`, taken on
the residue field of `A_𝔮`, which Mathlib makes a fraction field of `A / 𝔮`. To evaluate it on
the image of an element of `A` one has to pass from `residue A_𝔮 ∘ algebraMap A A_𝔮` to
`algebraMap (A / 𝔮) κ(𝔮) ∘ Ideal.Quotient.mk 𝔮`; that identification is
`Stacks.Chow.residue_algebraMap_eq`. Because the value of `ordInt` carries a proof that its
argument is nonzero, rewriting the argument needs the congruence
`Stacks.Chow.ordInt_val_congr` rather than `rw`.

That a unit has order of vanishing zero is `Stacks.Chow.ordInt_eq_zero_of_isUnit`, deduced from
`Ring.ordFrac_of_isUnit`. Deducing it instead from the length formula `ordInt_algebraMap` would
require `A / 𝔮` to be local, hence `A` to be local, which none of the statements here otherwise
need.

The reciprocity sum is Mathlib's `finsum`. Its additive manipulations need the support to be
finite, which is `Stacks.Chow.finite_tameSymbolOrderAt_support`; the symbols are therefore
carried as a family indexed by the height-one primes, as in that statement.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section OrderOfUnit

/-- The order of vanishing `ordInt` depends on its argument only through its value: the proof
that the argument is nonzero is irrelevant to it. This is what lets a rewrite pass under the
nonvanishing hypothesis that `ordInt` carries. -/
theorem ordInt_val_congr (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Nontrivial R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x y : K}
    (h : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInt R x hx = ordInt R y hy := by
  subst h
  rfl

/-- **A unit has order of vanishing zero.** Its order of vanishing in the sense of
`Ring.ordFrac` is `1`, so the integer it corresponds to is `0`. Unlike the length formula
`ordInt_algebraMap`, this does not need the ring to be local. -/
theorem ordInt_eq_zero_of_isUnit (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {r : R}
    (hr : IsUnit r) (h : algebraMap R K r ≠ 0) :
    ordInt R (algebraMap R K r) h = 0 := by
  have h2 : WithZero.unzero (x := Ring.ordFrac R (algebraMap R K r))
      ((h.isUnit.map (Ring.ordFrac R)).ne_zero) = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, Ring.ordFrac_of_isUnit hr]
    rfl
  change Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac R (algebraMap R K r))
    ((h.isUnit.map (Ring.ordFrac R)).ne_zero)) = 0
  rw [h2]
  rfl

variable {A : Type u} [CommRing A]

/-- The residue of the image of `x : A` in the localization at a prime `𝔮` is the image of the
class of `x` in `A / 𝔮` under the fraction-field structure map: both are the structure map of
`A` into the residue field of `A_𝔮`. -/
theorem residue_algebraMap_eq (p : HeightOnePrime A) (x : A) :
    residue (Localization.AtPrime p.1.asIdeal)
        (algebraMap A (Localization.AtPrime p.1.asIdeal) x) =
      algebraMap (A ⧸ p.1.asIdeal) (ResidueField (Localization.AtPrime p.1.asIdeal))
        (Ideal.Quotient.mk _ x) := by
  rw [Ideal.algebraMap_quotient_residueField_mk,
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p.1.asIdeal)]
  rfl

variable [IsNoetherianRing A]

/-- **A unit of `A` has order of vanishing zero along every height-one prime.** The class of a
unit in `A / 𝔮` is again a unit of `A / 𝔮`, and a unit has order of vanishing zero. -/
theorem heightOneOrd_eq_zero_of_isUnit (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (w : (ResidueField (Localization.AtPrime p.1.asIdeal))ˣ) {x : A} (hx : IsUnit x)
    (hw : (w : ResidueField (Localization.AtPrime p.1.asIdeal)) =
      residue (Localization.AtPrime p.1.asIdeal)
        (algebraMap A (Localization.AtPrime p.1.asIdeal) x)) :
    heightOneOrd hdim p w = 0 := by
  have : Ring.KrullDimLE 1 (A ⧸ p.1.asIdeal) :=
    krullDimLE_quotient_of_height_eq_one hdim p.1.asIdeal p.2
  have hval : (w : ResidueField (Localization.AtPrime p.1.asIdeal)) =
      algebraMap (A ⧸ p.1.asIdeal) (ResidueField (Localization.AtPrime p.1.asIdeal))
        (Ideal.Quotient.mk _ x) := by
    rw [hw, residue_algebraMap_eq]
  have hne : algebraMap (A ⧸ p.1.asIdeal) (ResidueField (Localization.AtPrime p.1.asIdeal))
      (Ideal.Quotient.mk _ x) ≠ 0 := hval ▸ w.ne_zero
  change ordInt (A ⧸ p.1.asIdeal)
    (w : ResidueField (Localization.AtPrime p.1.asIdeal)) w.ne_zero = 0
  rw [ordInt_val_congr (A ⧸ p.1.asIdeal) hval w.ne_zero hne]
  exact ordInt_eq_zero_of_isUnit (A ⧸ p.1.asIdeal)
    (hx.map (Ideal.Quotient.mk p.1.asIdeal)) hne

end OrderOfUnit

section Vanishing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The summand of Stacks 0EAW vanishes at every height-one prime when its first argument is a
unit of `A`.** By Stacks 0EAN the symbol is then the residue of that unit raised to the length of
`A_𝔮 / b A_𝔮`, and a unit of `A` has order of vanishing zero along `𝔮`.

This strengthens `Stacks.Chow.tameSymbolOrderAt_eq_zero`, which asks both arguments to avoid the
prime: here the second argument is arbitrary. -/
theorem tameSymbolOrderAt_eq_zero_of_isUnit_left (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (ha : IsUnit (a : A)) :
    tameSymbolOrderAt hdim p symb a b = 0 := by
  have hU : (toLocalizationNonZeroDivisor p.1.asIdeal a :
      Localization.AtPrime p.1.asIdeal) =
      ((Units.map (algebraMap A (Localization.AtPrime p.1.asIdeal)).toMonoidHom ha.unit :
        (Localization.AtPrime p.1.asIdeal)ˣ) : Localization.AtPrime p.1.asIdeal) := by
    simp [toLocalizationNonZeroDivisor]
  rw [show tameSymbolOrderAt hdim p symb a b =
      heightOneOrd hdim p (symb (toLocalizationNonZeroDivisor p.1.asIdeal a)
        (toLocalizationNonZeroDivisor p.1.asIdeal b)) from rfl,
    symb.unit_left _ _ _ hU, heightOneOrd_pow,
    heightOneOrd_eq_zero_of_isUnit hdim p _ ha (by simp), mul_zero]

/-- **The summand of Stacks 0EAW vanishes at every height-one prime when its second argument is
a unit of `A`**, by skewness of the summand. -/
theorem tameSymbolOrderAt_eq_zero_of_isUnit_right (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (hb : IsUnit (b : A)) :
    tameSymbolOrderAt hdim p symb a b = 0 := by
  have h := tameSymbolOrderAt_add_swap hdim p symb a b
  rwa [tameSymbolOrderAt_eq_zero_of_isUnit_left hdim p symb b a hb, add_zero] at h

/-- **The summand of Stacks 0EAW vanishes at a prime where the two arguments admit a
simultaneous power factorization whose unit parts come from `A`.** If in `A_𝔮` we have
`a = u π ^ e` and `b = v π ^ f` with `π` a nonzerodivisor of `A_𝔮` and `u`, `v` the images of
units of `A`, then

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = m (f ord_{A/𝔮}(ū) - e ord_{A/𝔮}(v̄)) = 0`,

because the orders of vanishing of the images of units of `A` are zero. The source instead
allows `u`, `v` to be units of `A_𝔮`, where those two orders need not vanish, and computes the
summand through the multiplicity of a two-periodic complex. -/
theorem tameSymbolOrderAt_eq_zero_of_factorization_isUnit (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (π : nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : Aˣ) (e f : ℕ)
    (ha : (toLocalizationNonZeroDivisor p.1.asIdeal a :
        Localization.AtPrime p.1.asIdeal) =
      algebraMap A (Localization.AtPrime p.1.asIdeal) (u : A) *
        (π : Localization.AtPrime p.1.asIdeal) ^ e)
    (hb : (toLocalizationNonZeroDivisor p.1.asIdeal b :
        Localization.AtPrime p.1.asIdeal) =
      algebraMap A (Localization.AtPrime p.1.asIdeal) (v : A) *
        (π : Localization.AtPrime p.1.asIdeal) ^ f) :
    tameSymbolOrderAt hdim p symb a b = 0 := by
  rw [tameSymbolOrderAt_eq_of_factorization hdim p symb a b π
      (Units.map (algebraMap A (Localization.AtPrime p.1.asIdeal)).toMonoidHom u)
      (Units.map (algebraMap A (Localization.AtPrime p.1.asIdeal)).toMonoidHom v) e f
      (by simpa using ha) (by simpa using hb),
    heightOneOrd_eq_zero_of_isUnit hdim p _ u.isUnit (by simp),
    heightOneOrd_eq_zero_of_isUnit hdim p _ v.isUnit (by simp)]
  ring

/-- **The summand of Stacks 0EAW vanishes at every height-one prime when the two arguments are
unit multiples of powers of one nonzerodivisor of `A`.** This is the globally prepared case of
the reciprocity relation, prime by prime. -/
theorem tameSymbolOrderAt_eq_zero_of_global_factorization (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b π : nonZeroDivisors A) (u v : Aˣ) (e f : ℕ)
    (ha : (a : A) = (u : A) * (π : A) ^ e) (hb : (b : A) = (v : A) * (π : A) ^ f) :
    tameSymbolOrderAt hdim p symb a b = 0 :=
  tameSymbolOrderAt_eq_zero_of_factorization_isUnit hdim p symb a b
    (toLocalizationNonZeroDivisor p.1.asIdeal π) u v e f
    (by
      change algebraMap A (Localization.AtPrime p.1.asIdeal) (a : A) = _
      rw [ha]
      simp [toLocalizationNonZeroDivisor])
    (by
      change algebraMap A (Localization.AtPrime p.1.asIdeal) (b : A) = _
      rw [hb]
      simp [toLocalizationNonZeroDivisor])

end Vanishing

section Sum

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The reciprocity sum of Stacks 0EAW is additive in its first argument**: by Stacks 0EAL
termwise, and by the finiteness of the contributing primes to split the sum. -/
theorem tameSymbolOrderAt_finsum_mul_left (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a a' b : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) (a * a') b =
      (∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b) +
        ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a' b := by
  rw [finsum_congr (fun p => tameSymbolOrderAt_mul_left hdim p (symb p) a a' b)]
  exact finsum_add_distrib (finite_tameSymbolOrderAt_support hdim symb a b)
    (finite_tameSymbolOrderAt_support hdim symb a' b)

/-- **The reciprocity sum of Stacks 0EAW is additive in its second argument**: by Stacks 0EAL
termwise, and by the finiteness of the contributing primes to split the sum. -/
theorem tameSymbolOrderAt_finsum_mul_right (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b b' : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a (b * b') =
      (∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b) +
        ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b' := by
  rw [finsum_congr (fun p => tameSymbolOrderAt_mul_right hdim p (symb p) a b b')]
  exact finsum_add_distrib (finite_tameSymbolOrderAt_support hdim symb a b)
    (finite_tameSymbolOrderAt_support hdim symb a b')

/-- **The reciprocity sum of Stacks 0EAW is skew**, by Stacks 0EAJ termwise. -/
theorem tameSymbolOrderAt_finsum_add_swap (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) :
    (∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b) +
      ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) b a = 0 := by
  rw [← finsum_add_distrib (finite_tameSymbolOrderAt_support hdim symb a b)
      (finite_tameSymbolOrderAt_support hdim symb b a),
    finsum_congr (fun p => tameSymbolOrderAt_add_swap hdim p (symb p) a b), finsum_zero]

/-- **The reciprocity sum of Stacks 0EAW is a finite sum** over any finite set of height-one
primes carrying the contributing ones. In the source that set is the primes of `V(ab)` other
than the maximal ideal. -/
theorem tameSymbolOrderAt_finsum_eq_sum (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (s : Finset (HeightOnePrime A))
    (hs : ∀ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b ≠ 0 → p ∈ s) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b =
      ∑ p ∈ s, tameSymbolOrderAt hdim p (symb p) a b :=
  finsum_eq_sum_of_support_subset _ fun _ hp => hs _ hp

/-- **Stacks 0EAW when the first argument is a unit of `A`**: every summand vanishes. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_isUnit_left (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (ha : IsUnit (a : A)) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 := by
  exact finsum_eq_zero_of_forall_eq_zero fun p =>
    tameSymbolOrderAt_eq_zero_of_isUnit_left hdim p (symb p) a b ha

/-- **Stacks 0EAW when the second argument is a unit of `A`**: every summand vanishes. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_isUnit_right (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (hb : IsUnit (b : A)) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 := by
  exact finsum_eq_zero_of_forall_eq_zero fun p =>
    tameSymbolOrderAt_eq_zero_of_isUnit_right hdim p (symb p) a b hb

/-- **Stacks 0EAW in the globally prepared case.** If the two nonzerodivisors are unit multiples
of powers of one nonzerodivisor of `A`, then every summand of the reciprocity sum vanishes, so
the sum is zero. The source reaches a prepared case only after the finite modification of
Stacks 0EAG, where the unit parts are units of the localizations and the summands need not
vanish individually. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_global_factorization (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b π : nonZeroDivisors A) (u v : Aˣ) (e f : ℕ)
    (ha : (a : A) = (u : A) * (π : A) ^ e) (hb : (b : A) = (v : A) * (π : A) ^ f) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 := by
  exact finsum_eq_zero_of_forall_eq_zero fun p =>
    tameSymbolOrderAt_eq_zero_of_global_factorization hdim p (symb p) a b π u v e f ha hb

/-- **The reduction of Stacks 0EAW to the multiplicity identity of the source.** The proof in the
source produces, at each contributing prime `𝔮`, a finite `A`-module `M_𝔮` with

`e_A(M_𝔮, a, b) = - ord_{A/𝔮}(∂_{A_𝔮}(a, b))`,

and shows `∑ e_A(M_𝔮, a, b) = 0` by comparing `⨁ M_𝔮` with `A / abA`, whose two-periodic complex
has vanishing cohomology by
`AlgebraicGeometry.periodicLength_quotient_mul_eq_zero`. Given those two facts the reciprocity
relation follows. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_multiplicity (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (mult : HeightOnePrime A → ℤ)
    (hmult : ∀ p : HeightOnePrime A, mult p = - tameSymbolOrderAt hdim p (symb p) a b)
    (hsum : ∑ᶠ p : HeightOnePrime A, mult p = 0) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 := by
  rw [finsum_congr hmult, finsum_neg_distrib] at hsum
  exact neg_eq_zero.mp hsum

end Sum

end Stacks.Chow

end
