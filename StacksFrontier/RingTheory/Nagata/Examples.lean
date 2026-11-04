module

public import StacksFrontier.RingTheory.Nagata.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fields, `ℤ` and Dedekind domains in characteristic zero are Nagata

Proof of `isNagataRing_field_and_int_and_isDedekindDomain`. A ring is Nagata when it is Noetherian
and every quotient `R ⧸ 𝔭` by a prime ideal is N-2, so all three classes are verified by inspecting
those quotients.

When `𝔭` is maximal the quotient is a field, and a field `A` is N-2 for a trivial reason: its
fraction field is `A` itself, so a finite extension `L` of it is a finite-dimensional `A`-vector
space, every element of `L` is integral over `A`, and the integral closure is all of `L`. This
already settles a ring all of whose primes are maximal — in particular a field, whose only prime
is `0` — and it settles every nonzero prime of a Dedekind domain, those being maximal.

What remains is the prime `𝔭 = 0` of a Dedekind domain `R`, where the quotient is `R` itself. Here
`R` is integrally closed, so its integral closure in `Frac(R)` is `R`, which is finite over `R`;
that is N-1, and in characteristic zero N-1 implies N-2 (Tag 032M, `N1_iff_N2`), because every
finite extension of a field of characteristic zero is separable. The ring `ℤ` is the case
`R = ℤ`.

## Main results

* `solution`: the statement of Tag 0335 for fields, `ℤ` and Dedekind domains in characteristic
  zero.

## References

* [Stacks Project, Tag 0335](https://stacks.math.columbia.edu/tag/0335)
* [Stacks Project, Tag 032M](https://stacks.math.columbia.edu/tag/032M)
-/

@[expose] public section

universe u

namespace Stacks.Nagata.FieldAndDedekindDomain


/-- The integral closure of an integrally closed ring `R` in its ring of fractions `K` is `R`
itself, hence a finite `R`-module: an integrally closed domain is N-1.

`IsDomain R` is not needed: as for `IsIntegrallyClosed`, the statement reads the same for a general
commutative ring with `K` its total ring of fractions. -/
private theorem module_finite_integralClosure_of_isIntegrallyClosed (R K : Type*) [CommRing R]
    [IsIntegrallyClosed R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  have hinj : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  rw [IsIntegrallyClosed.integralClosure_eq_bot]
  exact Module.Finite.equiv (Algebra.botEquivOfInjective hinj).symm.toLinearEquiv

/-- A field is N-2: a finite extension `L` of its fraction field is a finite-dimensional vector
space over it, and every element of `L` is integral over it, so the integral closure is `L`. -/
private theorem isJapaneseRing_of_isField (A : Type u) [CommRing A] [IsDomain A] (hA : IsField A) :
    IsJapaneseRing A := by
  refine { finite := fun L _ _ _ _ _ => ?_ }
  have : Module.Finite A (FractionRing A) :=
    Module.Finite.equiv (IsLocalization.atUnits A (nonZeroDivisors A) fun x hx =>
      isUnit_iff_exists_inv.2 (hA.mul_inv_cancel (nonZeroDivisors.ne_zero hx))).toLinearEquiv
  have : Module.Finite A L := Module.Finite.trans (FractionRing A) L
  have hint : Algebra.IsIntegral A L := Algebra.IsIntegral.of_finite A L
  rw [integralClosure_eq_top_iff.2 hint]
  exact Module.Finite.equiv (Subalgebra.topEquiv (R := A) (A := L)).symm.toLinearEquiv

/-- The quotient by a maximal ideal is N-2, being a field. -/
private theorem isJapaneseRing_quotient_of_isMaximal {R : Type u} [CommRing R] (p : Ideal R)
    [hp : p.IsMaximal] : IsJapaneseRing (R ⧸ p) :=
  isJapaneseRing_of_isField _ ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp hp)

/-- A Noetherian integrally closed domain of characteristic zero is N-2: it is N-1 because it is
integrally closed, and in characteristic zero N-1 implies N-2 (Tag 032M). -/
private theorem isJapaneseRing_of_isIntegrallyClosed (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] : IsJapaneseRing R := by
  have h : IsN2_032m R (FractionRing R) := (N1_iff_N2 R (FractionRing R)).1
    (module_finite_integralClosure_of_isIntegrallyClosed R (FractionRing R))
  refine { finite := fun L _ _ _ _ _ => ?_ }
  exact h L

/-- A Noetherian ring all of whose primes are maximal is a Nagata ring: every prime quotient is a
field, and a field is N-2. This covers item (1) of Tag 0335, a field having `0` as its only
prime. -/
private theorem isNagataRing_of_forall_isPrime_isMaximal (R : Type u) [CommRing R]
    [IsNoetherianRing R] (h : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) : IsNagataRing R := by
  refine ⟨inferInstance, fun p hp => ?_⟩
  have := h p hp
  exact isJapaneseRing_quotient_of_isMaximal p

/-- **Items (3) and (4) of Tag 0335.** A Dedekind domain whose fraction field has characteristic
zero is a Nagata ring: a nonzero prime is maximal, so its quotient is a field, and the quotient by
`0` is `R` itself, which is N-2 by `isJapaneseRing_of_isIntegrallyClosed`. -/
private theorem isNagataRing_of_isDedekindDomain_of_charZero (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero R] : IsNagataRing R := by
  refine ⟨inferInstance, fun p hp => ?_⟩
  rcases eq_or_ne p ⊥ with rfl | hp0
  · exact IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot R).symm
      (isJapaneseRing_of_isIntegrallyClosed R)
  · have := Ideal.isMaximal_of_isPrime_of_ne_bot p hp0
    exact isJapaneseRing_quotient_of_isMaximal p

/-- Fields, `ℤ` and Dedekind domains whose fraction field has characteristic zero are Nagata
rings: items (1), (3) and (4) of Tag 0335 as one conjunction. -/
public theorem solution :
    (∀ (K : Type u) [Field K], IsNagataRing K) ∧
    IsNagataRing ℤ ∧
    ∀ (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R], IsNagataRing R :=
  ⟨fun K _ => isNagataRing_of_forall_isPrime_isMaximal K fun _ hp => hp.isMaximal',
   isNagataRing_of_isDedekindDomain_of_charZero ℤ,
   fun R _ _ _ => isNagataRing_of_isDedekindDomain_of_charZero R⟩

end Stacks.Nagata.FieldAndDedekindDomain

/-- **Fields, `ℤ` and Dedekind domains whose fraction field has characteristic zero are Nagata
rings**, hence in particular universally Japanese. These are items (1), (3) and (4) of the source,
in its order; they share the one argument that inspects `R ⧸ 𝔭` for each prime `𝔭`.

The three classes on their own are `IsNagataRing.of_field`, `Int.isNagataRing` and
`IsNagataRing.of_isDedekindDomain_of_charZero`, which is how they are applied; see the module
docstring. -/
@[stacks 0335 "Items (1), (3) and (4) as one conjunction, since they share one proof; each is \
  available separately as `IsNagataRing.of_field`, `Int.isNagataRing` and \
  `IsNagataRing.of_isDedekindDomain_of_charZero`. Item (2) is Tag 032W and item (5) with the \
  closing clause \"and in particular universally Japanese\" is Tag 0334, both tagged 0335 below. \
  Nagata is `IsNagataRing` (032R(2)) and universally Japanese is `IsUniversallyJapaneseRing` \
  (032R(1)). See the module docstring."]
public theorem isNagataRing_field_and_int_and_isDedekindDomain :
    (∀ (K : Type u) [Field K], IsNagataRing K) ∧
    IsNagataRing ℤ ∧
    ∀ (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R], IsNagataRing R :=
      Stacks.Nagata.FieldAndDedekindDomain.solution.{u}

/-- **Stacks 0335 (1).** A field is a Nagata ring, hence in particular universally Japanese: the
only prime of a field `K` is `0`, and `K ⧸ 0 = K` is N-2 because the integral closure of `K` in a
finite extension `L` of `K` is `L` itself, a finite `K`-module. -/
@[stacks 0335 "(1) Fields."]
public theorem IsNagataRing.of_field {K : Type u} [Field K] : IsNagataRing K :=
  isNagataRing_field_and_int_and_isDedekindDomain.{u}.1 K

/-- **Stacks 0335 (3).** The ring `ℤ` is a Nagata ring, hence in particular universally Japanese.
This is the case `R = ℤ` of `IsNagataRing.of_isDedekindDomain_of_charZero`. -/
@[stacks 0335 "(3) The ring `ℤ`.",
  ega "IV 7.7.4" "in particular Z",
  ega "IV 7.8.3" "(vi), special case"]
public theorem Int.isNagataRing : IsNagataRing ℤ :=
  isNagataRing_field_and_int_and_isDedekindDomain.{0}.2.1

/-- **Stacks 0335 (4).** A Dedekind domain whose fraction field has characteristic zero is a
Nagata ring, hence in particular universally Japanese. For a prime `𝔭 ≠ 0` the quotient `R ⧸ 𝔭` is
a field and so is N-2; for `𝔭 = 0` the quotient is `R` itself, which is N-1 because it is
integrally closed, and N-1 implies N-2 in characteristic zero (Tag 032M).

The condition on the fraction field is stated as `CharZero R`, which for a domain `R` is
equivalent since `R → Frac R` is injective. It cannot be dropped: a one-dimensional Noetherian
integrally closed domain in characteristic `p` need not be N-2. -/
@[stacks 0335 "(4) Dedekind domains with fraction field of characteristic zero, the latter read \
  as `CharZero R`.",
  ega "IV 7.7.4" "Dedekind char 0",
  ega "IV 7.8.3" "(vi), special case",
  ega "IV 7.8.4" "special case"]
public theorem IsNagataRing.of_isDedekindDomain_of_charZero {R : Type u} [CommRing R]
    [IsDedekindDomain R] [CharZero R] : IsNagataRing R :=
  isNagataRing_field_and_int_and_isDedekindDomain.{u}.2.2 R

/- Item (2) of the source, a Noetherian complete local ring, is the statement of Tag 032W, whose
hypothesis of completeness for the topology defined by the maximal ideal is
`IsPrecomplete (IsLocalRing.maximalIdeal R) R`; the Hausdorff half of `IsAdicComplete` is
automatic for a Noetherian local ring, so nothing is added to the source's hypothesis. -/
add_to_stacks 0335 "(2) Noetherian complete local rings, which is Tag 032W."
  IsNagataRing.of_isPrecomplete_maximalIdeal

/- Item (5) of the source, a ring of finite type over any of the above, is the implication
(1) ⇒ (2) of Tag 0334, and the source's closing clause *and in particular universally Japanese*
is its implication (1) ⇒ (3), stated there once for all rings rather than repeated inside each of
the five classes, which is what "in particular" means here. -/
add_to_stacks 0335 "(5) Finite type ring extensions of any of the above, which is the \
  implication (1) ⇒ (2) of Tag 0334, and the closing clause \"and in particular universally \
  Japanese\", which is its implication (1) ⇒ (3)." isNagataRing_tfae

end
