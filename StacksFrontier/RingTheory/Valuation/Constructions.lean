module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotients, localizations and composites of valuation rings
-/

/-!
# Quotients and localizations of a valuation ring

Let `A` be a valuation ring. For any prime ideal `p ⊆ A` the quotient `A ⧸ p` is again a
valuation ring, and so is the localization `A_p`, and in fact any localization of `A`.
This is Stacks Lemma 10.50.9 (tag 088Y).

A commutative integral domain `A` is a *valuation ring* when divisibility on `A` is
total: for all `a b : A` either `a ∣ b` or `b ∣ a`, equivalently there is `c : A` with
`a * c = b` or `b * c = a`. This is Mathlib's `ValuationRing A`, characterized by
`ValuationRing.iff_dvd_total`, and it agrees with the Stacks characterization in
Lemma 10.50.5 (tag 052K).

## Main results

* `valuationRing_quotient_of_prime`: `A ⧸ p` is a valuation ring for `p` prime.
* `valuationRing_localization`: any localization of `A` at a submonoid of nonzerodivisors
  is a valuation ring.
* `valuationRing_localization_atPrime`: in particular `Localization.AtPrime p` is.

All three rest on the same observation: totality of divisibility passes to the image of
`A`. For a quotient the map is surjective, so divisibility transports directly. For a
localization every element is `a / m` with `m` invertible in the target, and dividing by
a unit changes nothing about divisibility, so `a ∣ b` in `A` already gives
`a / m ∣ b / n`.
-/

@[expose] public section

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

/-- A surjective ring homomorphism from a valuation ring onto an integral domain has a
valuation ring as target. -/
private theorem valuationRing_of_surjective {B : Type*} [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B :=
  Function.Surjective.valuationRing f hf

/-- For any prime ideal `p ⊆ A`, the quotient ring `A ⧸ p` is a valuation ring. -/
@[stacks 088Y]
theorem valuationRing_quotient_of_prime (𝔭 : Ideal A) [𝔭.IsPrime] :
    ValuationRing (A ⧸ 𝔭) :=
  valuationRing_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective

/-- Let `M ⊆ A` be a submonoid with `M ≤ nonZeroDivisors A`, and let `S` be any
commutative ring that is a localization of `A` at `M`. Then `S` is a valuation
ring. (`S` is an integral domain by
`IsLocalization.isDomain_of_le_nonZeroDivisors`.) -/
@[stacks 088Y, ega "II 7.1.1" "partial"]
theorem valuationRing_localization (M : Submonoid A) (hM : M ≤ nonZeroDivisors A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization M S] :
    haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors (S := S) hM
    ValuationRing S := by
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors (S := S) hM
  have key (a b : A) (m n : M) (h : a ∣ b) :
      IsLocalization.mk' S a m ∣ IsLocalization.mk' S b n :=
    (Dvd.intro _ (IsLocalization.mk'_spec S a m)).trans <| (map_dvd _ h).trans <|
      Dvd.intro _ (IsLocalization.mk'_eq_mul_mk'_one b n).symm
  refine ValuationRing.iff_dvd_total.mpr ⟨fun x y => ?_⟩
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨⟨b, n⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  exact ((ValuationRing.iff_dvd_total.mp ‹_›).total a b).imp (key a b m n) (key b a n m)

/-- For any prime ideal `p ⊆ A`, the localization `A_p = Localization.AtPrime p`
is a valuation ring. -/
@[stacks 088Y, ega "II 7.1.1" "partial"]
theorem valuationRing_localization_atPrime (𝔭 : Ideal A) [𝔭.IsPrime] :
    ValuationRing (Localization.AtPrime 𝔭) :=
  valuationRing_localization 𝔭.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
    (Localization.AtPrime 𝔭)

end

/-!
# Composing a valuation ring with a valuation ring of its residue field

Let `L` be a field, `A' ⊆ L` a valuation subring, and `K = A' / m_{A'}` the residue field
of the local ring `A'`, with residue map `res : A' → K`. Let `A ⊆ K` be a valuation
subring of `K`. Then

`C = {λ ∈ A' | res λ ∈ A} ⊆ L`

is again a valuation ring with fraction field `L`. This is Stacks Lemma 10.50.10
(tag 088Z).

Throughout, "valuation ring" is used in the sense of Stacks tag 00I9 and Lemma 10.50.5
(tag 052K): a subring `A` of a field is a valuation ring with that field as fraction
field exactly when `x ∈ A` or `x⁻¹ ∈ A` for every element `x` of the field. This is
Mathlib's `ValuationSubring`, and the criterion is `ValuationSubring.ofSubring`. So
proving `∀ x : L, x ∈ C ∨ x⁻¹ ∈ C` is proving that `C` is a valuation ring.

## Main definitions

* `residueValuationSubring A' A`: the subring `C`, obtained as the image in `L` of the
  preimage of `A` under `res`.
* `residueValuationSubring'`: the same subring packaged as a `ValuationSubring L`.

## Main results

* `mem_residueValuationSubring`: `x ∈ C` iff `x ∈ A'` and `res x ∈ A`.
* `residueValuationSubring_mem_or_inv_mem` (Stacks tag 088Z): `x ∈ C` or `x⁻¹ ∈ C` for
  every `x : L`.

## Implementation notes

`K` plays two roles at once: the residue field of `A'` and the fraction field of `A`.
This is made explicit by taking `K := IsLocalRing.ResidueField A'` and
`A : ValuationSubring K`; no hypothesis relates `A'` and `A` beyond that shared `K`.
-/

@[expose] public section

variable {L : Type*} [Field L]

/-- The subring `C = { λ ∈ A' | res λ ∈ A }` of `L`: the image, under the inclusion
`A' ↪ L`, of the preimage of `A` (a subring of the residue field `K` of `A'`) under
the residue map `res : A' →+* K`. -/
noncomputable def residueValuationSubring (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) : Subring L :=
  ((A.toSubring).comap (IsLocalRing.residue A')).map A'.subtype

/-- Membership in `C`: an `x : L` lies in `residueValuationSubring A' A` exactly when
`x ∈ A'` and the residue of `x` lies in `A`. -/
@[simp]
theorem mem_residueValuationSubring {A' : ValuationSubring L}
    {A : ValuationSubring (IsLocalRing.ResidueField A')} {x : L} :
    x ∈ residueValuationSubring A' A ↔ ∃ h : x ∈ A', IsLocalRing.residue A' ⟨x, h⟩ ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, by simpa using hy⟩
  · rintro ⟨h, hr⟩
    exact ⟨⟨x, h⟩, hr, rfl⟩

/-- The valuation criterion `x ∈ C ∨ x⁻¹ ∈ C` in the case `x ∈ A'`. -/
private theorem mem_or_inv_mem_residueValuationSubring_of_mem (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) (x : L) (hx : x ∈ A') :
    x ∈ residueValuationSubring A' A ∨ x⁻¹ ∈ residueValuationSubring A' A := by
  set a : A' := ⟨x, hx⟩
  set r := IsLocalRing.residue A' a with hr
  rcases A.mem_or_inv_mem r with hmem | hmem
  · exact Or.inl (mem_residueValuationSubring.mpr ⟨hx, hmem⟩)
  by_cases hr0 : r = 0
  · exact Or.inl (mem_residueValuationSubring.mpr ⟨hx, show r ∈ A from hr0 ▸ A.zero_mem⟩)
  right
  have hu : IsUnit a :=
    IsLocalRing.notMem_maximalIdeal.mp (by rwa [← IsLocalRing.residue_eq_zero_iff])
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hval : x * (b : L) = 1 := by simpa using congrArg Subtype.val hb
  have hxinv : x⁻¹ = (b : L) := inv_eq_of_mul_eq_one_right hval
  have hres : IsLocalRing.residue A' b = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm, hr, ← map_mul, hb, map_one])
  have heq : (⟨x⁻¹, hxinv ▸ b.property⟩ : A') = b := Subtype.ext hxinv
  exact mem_residueValuationSubring.mpr ⟨hxinv ▸ b.property, by rw [heq, hres]; exact hmem⟩

/-- **Stacks Tag 088Z.** `C` satisfies the valuation criterion of tag 052K: for every
`x : L`, either `x ∈ C` or `x⁻¹ ∈ C`. Via `ValuationSubring.ofSubring` this says exactly
that `C` is a valuation ring with fraction field `L`. -/
@[stacks 088Z]
theorem residueValuationSubring_mem_or_inv_mem (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) (x : L) :
    x ∈ residueValuationSubring A' A ∨ x⁻¹ ∈ residueValuationSubring A' A := by
  rcases A'.mem_or_inv_mem x with h | h
  · exact mem_or_inv_mem_residueValuationSubring_of_mem A' A x h
  · simpa only [inv_inv, or_comm] using mem_or_inv_mem_residueValuationSubring_of_mem A' A x⁻¹ h

/-- The subring `C` packaged as a `ValuationSubring L`. -/
noncomputable def residueValuationSubring' (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) : ValuationSubring L :=
  ValuationSubring.ofSubring (residueValuationSubring A' A)
    (residueValuationSubring_mem_or_inv_mem A' A)

/-- The underlying subring of `residueValuationSubring' A' A` is `residueValuationSubring A' A`. -/
@[simp]
theorem residueValuationSubring'_toSubring (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) :
    (residueValuationSubring' A' A).toSubring = residueValuationSubring A' A :=
  rfl

/-- An `x : L` lies in `residueValuationSubring' A' A` exactly when it lies in
`residueValuationSubring A' A`. -/
@[simp]
theorem mem_residueValuationSubring' {A' : ValuationSubring L}
    {A : ValuationSubring (IsLocalRing.ResidueField A')} {x : L} :
    x ∈ residueValuationSubring' A' A ↔ x ∈ residueValuationSubring A' A :=
  Iff.rfl

end
