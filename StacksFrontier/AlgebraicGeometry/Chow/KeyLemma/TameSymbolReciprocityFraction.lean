module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityNonzero
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction

/-!
# The reciprocity sum of tame-symbol orders on the fraction field

Let `A` be a two-dimensional Noetherian domain with fraction field `K`. At a height-one prime `𝔮`
the localization `A_𝔮` is a one-dimensional Noetherian local domain whose total ring of fractions
is `K`, so a tame symbol on pairs of nonzerodivisors of `A_𝔮` extends by
`Stacks.Chow.RegularTameSymbol.extend` to the tame symbol

`∂_{A_𝔮} : K^* × K^* → κ(𝔮)^*`

of Stacks 0EAH, and the summand of the key lemma Stacks 0EAX,

`ord_{A/𝔮}(∂_{A_𝔮}(f, g)) ∈ ℤ`  for `f, g ∈ K^*`,

is defined: it is `Stacks.Chow.fracTameSymbolOrderAt`. On the images of nonzerodivisors of `A` it
agrees with the summand `Stacks.Chow.tameSymbolOrderAt` of Stacks 0EAW, and on a pair of
fractions `f = a / b`, `g = c / d` it is the alternating sum of four of those, by the defining
formula of Stacks 0EAH.

Two consequences are proved. First, **only finitely many height-one primes contribute**, with no
hypothesis beyond those needed to state it: this is the finiteness assertion of Stacks 0EAX, and
it follows from the finiteness assertion `Stacks.Chow.finite_tameSymbolOrderAt_support` of
Stacks 0EAW applied to the four pairs of a presentation. Second, **the vanishing of the
reciprocity sum on `K^*` is equivalent to its vanishing on pairs of nonzerodivisors of `A`** —
that is, Stacks 0EAX is equivalent to Stacks 0EAW. This is the content of the proof of Stacks
0EAX in the source: bilinearity of the symbol and additivity of the order functions reduce the
relation for `f, g ∈ K^*` to the relation for elements of `A`. It is stated as an `iff`, so it is
a reformulation of Stacks 0EAX and not a weakening of it.

The vanishing sum itself is not proved here; for the tame symbol of Stacks 0EAQ it is
`Stacks.Chow.finsum_heightOneOrd_formulaTameSymbol_eq_zero` (Stacks 0EAX).

As in `Stacks.Chow.finite_tameSymbolOrderAt_support`, none of this needs `A` to be local; the
source states Stacks 0EAX for a local domain.

## Main definitions

* `Stacks.Chow.fracTameSymbolOrderAt` — the summand `ord_{A/𝔮}(∂_{A_𝔮}(f, g))` of Stacks 0EAX,
  for `f, g` units of the fraction field.

## Main results

* `Stacks.Chow.fracTameSymbolOrderAt_regularFractionUnit` — on the images of nonzerodivisors of
  `A` the summand of Stacks 0EAX is the summand of Stacks 0EAW.
* `Stacks.Chow.fracTameSymbolOrderAt_eq_of_presentation` — the summand on a pair of fractions, as
  the alternating sum of four summands of Stacks 0EAW.
* `Stacks.Chow.fracTameSymbolOrderAt_mul_left`, `Stacks.Chow.fracTameSymbolOrderAt_mul_right`,
  `Stacks.Chow.fracTameSymbolOrderAt_add_swap` — the summand is bi-additive and skew on `K^*`.
* `Stacks.Chow.finite_fracTameSymbolOrderAt_support` — **the finiteness assertion of
  Stacks 0EAX**: for `f, g ∈ K^*` only finitely many height-one primes contribute.
* `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_sum` — the reciprocity sum of Stacks 0EAX as a
  finite sum.
* `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_of_presentation`,
  `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors`,
  `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_iff_forall_nonZeroDivisors` — **the reduction
  of Stacks 0EAX to Stacks 0EAW**, as a four-term expansion, as an implication and as an
  equivalence.
* `Stacks.Chow.fracTameSymbolOrderAt_mvPolynomialX_eq_one`,
  `Stacks.Chow.not_forall_fracTameSymbolOrderAt_eq_zero_mvPolynomial` — the summand of
  Stacks 0EAX is not identically zero: it is `1` at one height-one prime of `k[X₀, X₁]`.

## Implementation notes

That `K` is a total ring of fractions of `A_𝔮` as well as of `A` is a Mathlib instance for
`K = FractionRing A`, which is therefore the spelling used; the two structure maps `A → K` and
`A_𝔮 → K` agree, which is `Stacks.Chow.regularFractionUnit_toLocalizationNonZeroDivisor`.

`Stacks.Chow.RegularTameSymbol.extend` needs `Ring.KrullDimLE 1 A_𝔮`, which
`Stacks.Chow.krullDimLE_localization_of_height_eq_one` supplies from the height hypothesis rather
than by inference; it is installed as a file-local instance so that the extension can be written
without carrying it. `Ring.KrullDimLE` is a `Prop`, so the instance is irrelevant to the value of
the definition and a caller may re-derive it.

Sums over the height-one primes are `finsum`, and the four-term expansion of the reciprocity sum
is obtained by first restricting all five sums to one finite set of primes carrying the four
supports, where the arithmetic is `Finset.sum_add_distrib`; manipulating the `finsum`s directly
would need a finiteness hypothesis for each intermediate combination of the four.

What blocks the vanishing sum is Stacks 0EAW, and through it the construction Stacks 0EAQ of the
symbol: the symbol is carried here as the data `Stacks.Chow.RegularTameSymbol`, whose uniqueness
the source explicitly declines to claim, and the proof of Stacks 0EAW passes through the product
formula of Stacks 0EAT, which for arbitrary data is a uniqueness assertion — see the module
documentation of `StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FiniteExtension`. So the
reduction proved here is the whole of Stacks 0EAX that does not depend on Stacks 0EAW.

## References

* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section Fraction

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- The localization at a height-one prime has Krull dimension at most one, which is what the
tame symbol of Stacks 0EAH requires of it. This is
`Stacks.Chow.krullDimLE_localization_of_height_eq_one` installed as an instance, so that the
extension of a symbol to the fraction field can be written without carrying it. -/
local instance krullDimLE_localization_heightOnePrime (p : HeightOnePrime A) :
    Ring.KrullDimLE 1 (Localization.AtPrime p.1.asIdeal) :=
  krullDimLE_localization_of_height_eq_one p.1.asIdeal p.2

omit [IsNoetherianRing A] in
/-- A nonzerodivisor of `A`, viewed as a nonzerodivisor of the localization `A_𝔮`, has the same
image in the fraction field: both are the structure map of `A` into it. -/
theorem regularFractionUnit_toLocalizationNonZeroDivisor (p : HeightOnePrime A)
    (a : nonZeroDivisors A) :
    regularFractionUnit (Q := FractionRing A)
        (toLocalizationNonZeroDivisor p.1.asIdeal a) =
      regularFractionUnit (Q := FractionRing A) a := by
  refine Units.ext ?_
  rw [regularFractionUnit_val, regularFractionUnit_val,
    show ((toLocalizationNonZeroDivisor p.1.asIdeal a :
        Localization.AtPrime p.1.asIdeal)) =
      algebraMap A (Localization.AtPrime p.1.asIdeal) (a : A) from rfl]
  exact (IsScalarTower.algebraMap_apply A (Localization.AtPrime p.1.asIdeal)
    (FractionRing A) (a : A)).symm

/-- **The summand of Stacks 0EAX.** For a two-dimensional Noetherian domain `A`, a height-one
prime `𝔮` and a tame symbol on pairs of nonzerodivisors of `A_𝔮`, this is the order of vanishing
along `A / 𝔮` of the value `∂_{A_𝔮}(f, g)` of the extended symbol of Stacks 0EAH on two units of
the fraction field of `A`. -/
noncomputable def fracTameSymbolOrderAt (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f g : (FractionRing A)ˣ) : ℤ :=
  heightOneOrd hdim p (symb.extend (FractionRing A) f g)

/-- The summand of Stacks 0EAX, written out. Stated so that the definition is not unfolded by a
rewrite, which would generate an equation lemma for it. -/
theorem fracTameSymbolOrderAt_eq_heightOneOrd (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f g : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb f g =
      heightOneOrd hdim p (symb.extend (FractionRing A) f g) := rfl

/-- **On the images of nonzerodivisors of `A` the summand of Stacks 0EAX is the summand of
Stacks 0EAW**, because the extension of Stacks 0EAH restricts to the given symbol. -/
theorem fracTameSymbolOrderAt_regularFractionUnit (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a c : nonZeroDivisors A) :
    fracTameSymbolOrderAt hdim p symb (regularFractionUnit a) (regularFractionUnit c) =
      tameSymbolOrderAt hdim p symb a c := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd,
    ← regularFractionUnit_toLocalizationNonZeroDivisor p a,
    ← regularFractionUnit_toLocalizationNonZeroDivisor p c,
    symb.extend_regularFractionUnit]
  rfl

/-- **The summand of Stacks 0EAX on a pair of fractions.** If `f = a / b` and `g = c / d` with
`a, b, c, d` nonzerodivisors of `A`, then

`ord_{A/𝔮}(∂_{A_𝔮}(f, g)) =
  ord_{A/𝔮}(∂_{A_𝔮}(a, c)) - ord_{A/𝔮}(∂_{A_𝔮}(a, d))
  - ord_{A/𝔮}(∂_{A_𝔮}(b, c)) + ord_{A/𝔮}(∂_{A_𝔮}(b, d))`,

which is the defining formula of Stacks 0EAH read through the additive order of vanishing. -/
theorem fracTameSymbolOrderAt_eq_of_presentation (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    {f g : (FractionRing A)ˣ} (a b c d : nonZeroDivisors A)
    (hf : f = regularFractionUnit (Q := FractionRing A) a *
      (regularFractionUnit (Q := FractionRing A) b)⁻¹)
    (hg : g = regularFractionUnit (Q := FractionRing A) c *
      (regularFractionUnit (Q := FractionRing A) d)⁻¹) :
    fracTameSymbolOrderAt hdim p symb f g =
      tameSymbolOrderAt hdim p symb a c - tameSymbolOrderAt hdim p symb a d -
        tameSymbolOrderAt hdim p symb b c + tameSymbolOrderAt hdim p symb b d := by
  have hlift : ∀ (u : (FractionRing A)ˣ) (x y : nonZeroDivisors A),
      u = regularFractionUnit (Q := FractionRing A) x *
        (regularFractionUnit (Q := FractionRing A) y)⁻¹ →
      u = regularFractionUnit (toLocalizationNonZeroDivisor p.1.asIdeal x) *
        (regularFractionUnit (Q := FractionRing A)
          (toLocalizationNonZeroDivisor p.1.asIdeal y))⁻¹ := fun u x y h => by
    rw [regularFractionUnit_toLocalizationNonZeroDivisor p x,
      regularFractionUnit_toLocalizationNonZeroDivisor p y]
    exact h
  have hbridge : ∀ x y : nonZeroDivisors A,
      heightOneOrd hdim p (symb (toLocalizationNonZeroDivisor p.1.asIdeal x)
        (toLocalizationNonZeroDivisor p.1.asIdeal y)) =
      tameSymbolOrderAt hdim p symb x y := fun _ _ => rfl
  rw [fracTameSymbolOrderAt_eq_heightOneOrd,
    symb.extend_eq (FractionRing A) (toLocalizationNonZeroDivisor p.1.asIdeal a)
      (toLocalizationNonZeroDivisor p.1.asIdeal b)
      (toLocalizationNonZeroDivisor p.1.asIdeal c)
      (toLocalizationNonZeroDivisor p.1.asIdeal d) (hlift f a b hf) (hlift g c d hg),
    heightOneOrd_mul, heightOneOrd_mul, heightOneOrd_mul, heightOneOrd_inv, heightOneOrd_inv,
    hbridge a c, hbridge a d, hbridge b c, hbridge b d]
  ring

omit [IsDomain A] [IsNoetherianRing A] in
/-- Every unit of the fraction field of a commutative ring is a quotient of two nonzerodivisors
of the ring, so the four-term formula applies to every pair of arguments. -/
theorem exists_presentation_fractionRing (f : (FractionRing A)ˣ) :
    ∃ a b : nonZeroDivisors A,
      f = regularFractionUnit a * (regularFractionUnit (Q := FractionRing A) b)⁻¹ :=
  exists_regularFractionUnit_div f

/-- **The summand of Stacks 0EAX is additive in its first argument**, by Stacks 0EAI. -/
theorem fracTameSymbolOrderAt_mul_left (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f f' g : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb (f * f') g =
      fracTameSymbolOrderAt hdim p symb f g + fracTameSymbolOrderAt hdim p symb f' g := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, fracTameSymbolOrderAt_eq_heightOneOrd,
    fracTameSymbolOrderAt_eq_heightOneOrd,
    (symb.extend (FractionRing A)).map_mul_left, heightOneOrd_mul]

/-- **The summand of Stacks 0EAX is additive in its second argument**, by Stacks 0EAI. -/
theorem fracTameSymbolOrderAt_mul_right (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f g g' : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb f (g * g') =
      fracTameSymbolOrderAt hdim p symb f g + fracTameSymbolOrderAt hdim p symb f g' := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, fracTameSymbolOrderAt_eq_heightOneOrd,
    fracTameSymbolOrderAt_eq_heightOneOrd,
    (symb.extend (FractionRing A)).map_mul_right, heightOneOrd_mul]

@[simp]
theorem fracTameSymbolOrderAt_one_left (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (g : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb 1 g = 0 := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, (symb.extend (FractionRing A)).one_left,
    heightOneOrd_one]

@[simp]
theorem fracTameSymbolOrderAt_one_right (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (f : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb f 1 = 0 := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, (symb.extend (FractionRing A)).one_right,
    heightOneOrd_one]

/-- **The summand of Stacks 0EAX is skew**, by Stacks 0EAJ. -/
theorem fracTameSymbolOrderAt_add_swap (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (f g : (FractionRing A)ˣ) :
    fracTameSymbolOrderAt hdim p symb f g + fracTameSymbolOrderAt hdim p symb g f = 0 := by
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, fracTameSymbolOrderAt_eq_heightOneOrd,
    ← heightOneOrd_mul, (symb.extend (FractionRing A)).skew, heightOneOrd_one]

/-- **Stacks 0EAX, finiteness of the sum.** For two units of the fraction field of a
two-dimensional Noetherian domain, only finitely many height-one primes contribute a nonzero
tame-symbol order. Writing the two arguments as quotients of nonzerodivisors of `A` expresses
each summand through four summands of Stacks 0EAW, each of which has finite support by
`Stacks.Chow.finite_tameSymbolOrderAt_support`. -/
theorem finite_fracTameSymbolOrderAt_support (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f g : (FractionRing A)ˣ) :
    {p : HeightOnePrime A | fracTameSymbolOrderAt hdim p (symb p) f g ≠ 0}.Finite := by
  obtain ⟨a, b, hf⟩ := exists_presentation_fractionRing f
  obtain ⟨c, d, hg⟩ := exists_presentation_fractionRing g
  refine (((finite_tameSymbolOrderAt_support hdim symb a c).union
    (finite_tameSymbolOrderAt_support hdim symb a d)).union
      ((finite_tameSymbolOrderAt_support hdim symb b c).union
        (finite_tameSymbolOrderAt_support hdim symb b d))).subset ?_
  intro p hp
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hmem
  refine hp ?_
  rw [fracTameSymbolOrderAt_eq_of_presentation hdim p (symb p) a b c d hf hg,
    hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2]
  ring

/-- **The reciprocity sum of Stacks 0EAX is a finite sum** over any finite set of height-one
primes carrying the contributing ones. -/
theorem fracTameSymbolOrderAt_finsum_eq_sum (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (f g : (FractionRing A)ˣ) (s : Finset (HeightOnePrime A))
    (hs : ∀ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (symb p) f g ≠ 0 → p ∈ s) :
    ∑ᶠ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (symb p) f g =
      ∑ p ∈ s, fracTameSymbolOrderAt hdim p (symb p) f g :=
  finsum_eq_sum_of_support_subset _ fun _ hp => hs _ hp

/-- **The reduction of Stacks 0EAX to Stacks 0EAW, as an expansion of the sum.** For `f = a / b`
and `g = c / d` the reciprocity sum of Stacks 0EAX is the alternating sum of the four reciprocity
sums of Stacks 0EAW on the numerators and denominators. -/
theorem fracTameSymbolOrderAt_finsum_eq_of_presentation (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    {f g : (FractionRing A)ˣ} (a b c d : nonZeroDivisors A)
    (hf : f = regularFractionUnit (Q := FractionRing A) a *
      (regularFractionUnit (Q := FractionRing A) b)⁻¹)
    (hg : g = regularFractionUnit (Q := FractionRing A) c *
      (regularFractionUnit (Q := FractionRing A) d)⁻¹) :
    ∑ᶠ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (symb p) f g =
      ((∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a c) -
          ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a d) -
        (∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) b c) +
          ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) b d := by
  have hfin := finite_tameSymbolOrderAt_support hdim symb
  have hsub {u v : HeightOnePrime A → ℤ} (hu : (Function.support u).Finite)
      (hv : (Function.support v).Finite) : (Function.support fun p => u p - v p).Finite :=
    (hu.union hv).subset (Function.support_sub _ _)
  rw [finsum_congr fun p =>
      fracTameSymbolOrderAt_eq_of_presentation hdim p (symb p) a b c d hf hg,
    finsum_add_distrib (hsub (hsub (hfin a c) (hfin a d)) (hfin b c)) (hfin b d),
    finsum_sub_distrib (hsub (hfin a c) (hfin a d)) (hfin b c),
    finsum_sub_distrib (hfin a c) (hfin a d)]

/-- **Stacks 0EAX from Stacks 0EAW.** If the reciprocity sum of Stacks 0EAW vanishes for every
pair of nonzerodivisors of `A`, then the reciprocity sum of Stacks 0EAX vanishes for every pair
of units of the fraction field: writing the arguments as quotients expands the sum into four of
the former. This is the proof of Stacks 0EAX in the source. -/
theorem fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors
    (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (h : ∀ x y : nonZeroDivisors A,
      ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) x y = 0)
    (f g : (FractionRing A)ˣ) :
    ∑ᶠ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (symb p) f g = 0 := by
  obtain ⟨a, b, hf⟩ := exists_presentation_fractionRing f
  obtain ⟨c, d, hg⟩ := exists_presentation_fractionRing g
  rw [fracTameSymbolOrderAt_finsum_eq_of_presentation hdim symb a b c d hf hg,
    h a c, h a d, h b c, h b d]
  ring

/-- **Stacks 0EAX is equivalent to Stacks 0EAW.** The reciprocity sum vanishes for every pair of
units of the fraction field exactly when it vanishes for every pair of nonzerodivisors of `A`.
One direction is the expansion of a pair of fractions into four pairs of elements of `A`, the
other is the agreement of the two summands on the images of nonzerodivisors. Being an
equivalence, this is a reformulation of Stacks 0EAX rather than a weakening of it. -/
theorem fracTameSymbolOrderAt_finsum_eq_zero_iff_forall_nonZeroDivisors
    (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) :
    (∀ f g : (FractionRing A)ˣ,
        ∑ᶠ p : HeightOnePrime A, fracTameSymbolOrderAt hdim p (symb p) f g = 0) ↔
      ∀ x y : nonZeroDivisors A,
        ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) x y = 0 := by
  refine ⟨fun h x y => ?_, fun h f g =>
    fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors hdim symb h f g⟩
  rw [← finsum_congr (fun p =>
    fracTameSymbolOrderAt_regularFractionUnit hdim p (symb p) x y)]
  exact h _ _

end Fraction

section Witness

variable (k : Type u) [Field k]

/-- **The summand of Stacks 0EAX is `1` at one height-one prime of `k[X₀, X₁]`**, for the pair of
variables `X_j`, `X_i` viewed in the fraction field. It agrees there with the summand of
Stacks 0EAW, which is `Stacks.Chow.tameSymbolOrderAt_mvPolynomialX_eq_one`. -/
theorem fracTameSymbolOrderAt_mvPolynomialX_eq_one {i j : Fin 2} (hij : i ≠ j) :
    fracTameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k)
        (mvPolynomialHeightOnePrimeX k i)
        (normalHeightOneSymbol (mvPolynomialHeightOnePrimeX k i))
        (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
          (mvPolynomialX k j))
        (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
          (mvPolynomialX k i)) = 1 := by
  rw [fracTameSymbolOrderAt_regularFractionUnit]
  exact tameSymbolOrderAt_mvPolynomialX_eq_one k hij

/-- **The summand of Stacks 0EAX is not identically zero**, so the reciprocity relation of
Stacks 0EAX is a statement about a function that genuinely takes nonzero values. -/
theorem not_forall_fracTameSymbolOrderAt_eq_zero_mvPolynomial :
    ¬ ∀ (p : HeightOnePrime (MvPolynomial (Fin 2) k))
        (f g : (FractionRing (MvPolynomial (Fin 2) k))ˣ),
      fracTameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p
        (normalHeightOneSymbol p) f g = 0 := by
  intro h
  have h1 := h (mvPolynomialHeightOnePrimeX k 0)
    (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k)) (mvPolynomialX k 1))
    (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k)) (mvPolynomialX k 0))
  rw [fracTameSymbolOrderAt_mvPolynomialX_eq_one k (by decide : (0 : Fin 2) ≠ 1)] at h1
  exact one_ne_zero h1

/-- The set whose finiteness Stacks 0EAX asserts is finite and not empty, at `k[X₀, X₁]` for the
pair of variables. -/
theorem finite_and_nonempty_fracTameSymbolOrderAt_support_mvPolynomial :
    {p : HeightOnePrime (MvPolynomial (Fin 2) k) |
        fracTameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p
          (normalHeightOneSymbol p)
          (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
            (mvPolynomialX k 1))
          (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
            (mvPolynomialX k 0)) ≠ 0}.Finite ∧
      {p : HeightOnePrime (MvPolynomial (Fin 2) k) |
        fracTameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p
          (normalHeightOneSymbol p)
          (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
            (mvPolynomialX k 1))
          (regularFractionUnit (Q := FractionRing (MvPolynomial (Fin 2) k))
            (mvPolynomialX k 0)) ≠ 0}.Nonempty :=
  ⟨finite_fracTameSymbolOrderAt_support (MvPolynomial.ringKrullDim_fin_two k)
      normalHeightOneSymbol _ _,
    ⟨mvPolynomialHeightOnePrimeX k 0, by
      rw [Set.mem_ofPred_eq,
        fracTameSymbolOrderAt_mvPolynomialX_eq_one k (by decide : (0 : Fin 2) ≠ 1)]
      exact one_ne_zero⟩⟩

end Witness

end Stacks.Chow

end
