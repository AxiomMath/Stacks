module

public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Self
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Steinberg
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction
public import StacksFrontier.RingTheory.LocalRing.PrepareTwoNonZeroDivisors

/-!
# The periodic-determinant symbol is a tame symbol

Let `(A, 𝔪)` be a Noetherian local ring of Krull dimension one, with no domain hypothesis. The
periodic determinant of Stacks 02PZ gives a symbol

`d_A(a, b) ∈ κ(𝔪)^*`

on pairs of nonzerodivisors of `A`: the determinant of the two-periodic complex on `A / abA` whose
two differentials are multiplication by `a` and multiplication by `b`. The four properties asked
of a tame symbol in Stacks 0EAH — Stacks 0EAL, 0EAM, 0EAN and 0EAP — are for `d_A` the identities
Stacks 02Q0, 0AY9, 02Q2 and 02Q8, so `d_A` is a `Stacks.Chow.RegularTameSymbol` on `A`, and
`Stacks.Chow.RegularTameSymbol.extend` turns it into the tame symbol
`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of Stacks 0EAI, 0EAJ and 0EAK.

The construction asks nothing of `A` beyond being Noetherian, local and of dimension one: no
domain hypothesis, no normal modification, and no auxiliary family of symbols carried as data. The
exponents of Stacks 0EAM and 0EAN are the length `length_A(A/bA)`, which for the ring itself is
`Ring.ord A b`. The Steinberg relation Stacks 02Q8 is proved in this development from the
preparation statement Stacks 02Q7, which
`Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors` proves.

## Main definitions

* `Stacks.Chow.periodicDeterminantSymbol` — `d_A` on a pair of nonzerodivisors of `A`.
* `Stacks.Chow.periodicDeterminantRegularTameSymbol` — `d_A` as a tame symbol on pairs of
  nonzerodivisors of `A`.
* `Stacks.Chow.periodicDeterminantTameSymbol` — the induced tame symbol on `Q(A)^*`.

## Main results

* `Stacks.Chow.periodicDeterminantSymbol_mul_left`,
  `Stacks.Chow.periodicDeterminantSymbol_mul_right`,
  `Stacks.Chow.periodicDeterminantSymbol_self`,
  `Stacks.Chow.periodicDeterminantSymbol_unit_left` and
  `Stacks.Chow.periodicDeterminantSymbol_steinberg` are the four properties Stacks 0EAL, 0EAM,
  0EAN and 0EAP of `d_A`.
* `Stacks.Chow.periodicDeterminantSymbol_swap` — `d_A(a, b) d_A(b, a) = 1`.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

section Symbol

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A nonzerodivisor of `A` acts injectively on `A`. -/
private theorem isSMulRegular_coe (a : nonZeroDivisors A) : IsSMulRegular A (a : A) :=
  (isRegular_iff_mem_nonZeroDivisors.mpr a.property).isSMulRegular

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A ring of Krull dimension one has support dimension one as a module over itself. -/
private theorem supportDim_self_eq_one (hdim : ringKrullDim A = 1) :
    Module.supportDim A A = 1 :=
  (Module.supportDim_self_eq_ringKrullDim A).trans hdim

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The length of `A / bA`, presented as the quotient by the range of multiplication by `b`, is
the order of vanishing of `b`. -/
private theorem moduleLength_quotient_range_lsmul_eq_ord (b : A) :
    Module.FiniteLength.moduleLength A (A ⧸ (LinearMap.lsmul A A b).range) =
      (Ring.ord A b).toNat := by
  have hrange : (LinearMap.lsmul A A b).range = Ideal.span {b} := by
    ext x
    rw [LinearMap.mem_range, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [LinearMap.lsmul_apply]⟩
  rw [hrange]
  rfl

/-- **The periodic-determinant symbol `d_A` of Stacks 02PZ on nonzerodivisors.** For a
one-dimensional Noetherian local ring `A` and nonzerodivisors `a` and `b`, the symbol of `A` as a
module over itself. -/
def periodicDeterminantSymbol (hdim : ringKrullDim A = 1) (a b : nonZeroDivisors A) :
    (ResidueField A)ˣ :=
  AlgebraicGeometry.moduleSymbol (M := A) (a : A) (b : A)
    (isRegular_iff_mem_nonZeroDivisors.mpr a.property).isSMulRegular
    (isRegular_iff_mem_nonZeroDivisors.mpr b.property).isSMulRegular
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- The symbol is the module symbol of any ring elements equal to its two arguments. -/
private theorem periodicDeterminantSymbol_eq_moduleSymbol (hdim : ringKrullDim A = 1)
    {a b : nonZeroDivisors A} {a' b' : A} (ha : (a : A) = a') (hb : (b : A) = b')
    (ha' : IsSMulRegular A a') (hb' : IsSMulRegular A b') :
    periodicDeterminantSymbol hdim a b =
      AlgebraicGeometry.moduleSymbol (M := A) a' b' ha' hb' (supportDim_self_eq_one hdim) := by
  subst ha hb
  rfl

/-- **Stacks 0EAL.** `d_A(a, b b') = d_A(a, b) d_A(a, b')`. -/
theorem periodicDeterminantSymbol_mul_right (hdim : ringKrullDim A = 1)
    (a b b' : nonZeroDivisors A) :
    periodicDeterminantSymbol hdim a (b * b') =
      periodicDeterminantSymbol hdim a b * periodicDeterminantSymbol hdim a b' :=
  AlgebraicGeometry.moduleSymbol_mul_right (A := A) (M := A) (a : A) (b : A) (b' : A)
    (isSMulRegular_coe a) (isSMulRegular_coe b) (isSMulRegular_coe b')
    (supportDim_self_eq_one hdim)

/-- **Stacks 0EAJ on nonzerodivisors.** `d_A(a, b) d_A(b, a) = 1`. -/
theorem periodicDeterminantSymbol_swap (hdim : ringKrullDim A = 1) (a b : nonZeroDivisors A) :
    periodicDeterminantSymbol hdim a b * periodicDeterminantSymbol hdim b a = 1 :=
  AlgebraicGeometry.moduleSymbol_mul_swap (A := A) (M := A) (a : A) (b : A)
    (isSMulRegular_coe a) (isSMulRegular_coe b) (supportDim_self_eq_one hdim)

/-- **Stacks 0EAL.** `d_A(a a', b) = d_A(a, b) d_A(a', b)`. -/
theorem periodicDeterminantSymbol_mul_left (hdim : ringKrullDim A = 1)
    (a a' b : nonZeroDivisors A) :
    periodicDeterminantSymbol hdim (a * a') b =
      periodicDeterminantSymbol hdim a b * periodicDeterminantSymbol hdim a' b := by
  rw [mul_eq_one_iff_eq_inv.mp (periodicDeterminantSymbol_swap hdim (a * a') b),
    periodicDeterminantSymbol_mul_right, mul_inv_rev,
    ← mul_eq_one_iff_eq_inv.mp (periodicDeterminantSymbol_swap hdim a b),
    ← mul_eq_one_iff_eq_inv.mp (periodicDeterminantSymbol_swap hdim a' b)]
  ac_rfl

/-- **Stacks 0EAM.** `d_A(b, b) = (-1)^m` with `m = length_A(A/bA)`. -/
theorem periodicDeterminantSymbol_self (hdim : ringKrullDim A = 1) (b : nonZeroDivisors A) :
    periodicDeterminantSymbol hdim b b = (-1) ^ (Ring.ord A (b : A)).toNat := by
  have h := AlgebraicGeometry.moduleSymbol_self_eq_negOne_pow_length (A := A) (M := A) (b : A)
    (isSMulRegular_coe b) (supportDim_self_eq_one hdim)
  rwa [moduleLength_quotient_range_lsmul_eq_ord] at h

/-- **Stacks 0EAN.** `d_A(u, b) = u^m mod 𝔪` with `m = length_A(A/bA)`, for `u ∈ A` a unit. -/
theorem periodicDeterminantSymbol_unit_left (hdim : ringKrullDim A = 1)
    (a b : nonZeroDivisors A) (u : Aˣ) (hu : (a : A) = u) :
    periodicDeterminantSymbol hdim a b =
      Units.map (residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat := by
  rw [periodicDeterminantSymbol_eq_moduleSymbol hdim hu rfl (Units.isSMulRegular A u)
    (isSMulRegular_coe b)]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  exact AlgebraicGeometry.moduleSymbol_unit_left_ring u (b : A) (isSMulRegular_coe b) hdim

/-- **Stacks 0EAP.** `d_A(a, b - a) d_A(b, b) = d_A(b, b - a) d_A(a, b)`. -/
theorem periodicDeterminantSymbol_steinberg (hdim : ringKrullDim A = 1)
    (a b c : nonZeroDivisors A) (hc : (c : A) = (b : A) - (a : A)) :
    periodicDeterminantSymbol hdim a c * periodicDeterminantSymbol hdim b b =
      periodicDeterminantSymbol hdim b c * periodicDeterminantSymbol hdim a b := by
  have hcreg : IsSMulRegular A ((b : A) - (a : A)) := hc ▸ isSMulRegular_coe c
  rw [periodicDeterminantSymbol_eq_moduleSymbol hdim rfl hc (isSMulRegular_coe a) hcreg,
    periodicDeterminantSymbol_eq_moduleSymbol hdim rfl hc (isSMulRegular_coe b) hcreg]
  exact AlgebraicGeometry.moduleSymbol_steinberg_prepare
    (A := A) (M := A) (a : A) (b : A) (isSMulRegular_coe a) (isSMulRegular_coe b) hcreg
    (supportDim_self_eq_one hdim)

end Symbol

/-- **Stacks 0EAH on nonzerodivisors, for an arbitrary one-dimensional Noetherian local ring.**
The periodic-determinant symbol `d_A` of Stacks 02PZ on pairs of nonzerodivisors of `A`,
with the four properties Stacks 0EAL, 0EAM, 0EAN and 0EAP. -/
noncomputable def periodicDeterminantRegularTameSymbol
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) : RegularTameSymbol A where
  toFun := periodicDeterminantSymbol hdim
  map_mul_left := periodicDeterminantSymbol_mul_left hdim
  map_mul_right := periodicDeterminantSymbol_mul_right hdim
  self := periodicDeterminantSymbol_self hdim
  unit_left := periodicDeterminantSymbol_unit_left hdim
  steinberg := periodicDeterminantSymbol_steinberg hdim

/-- The symbol is the periodic-determinant symbol of Stacks 02PZ. -/
theorem periodicDeterminantRegularTameSymbol_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (a b : nonZeroDivisors A) :
    periodicDeterminantRegularTameSymbol hdim a b =
      AlgebraicGeometry.moduleSymbol (M := A) (a : A) (b : A)
        (isRegular_iff_mem_nonZeroDivisors.mpr a.property).isSMulRegular
        (isRegular_iff_mem_nonZeroDivisors.mpr b.property).isSMulRegular
        ((Module.supportDim_self_eq_ringKrullDim A).trans hdim) := rfl

/-- **Stacks 0EAI, 0EAJ and 0EAK for an arbitrary one-dimensional Noetherian local ring.** The
tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` induced by the periodic-determinant symbol:
bimultiplicative, skew, and trivial on `(f, 1 - f)`. -/
noncomputable def periodicDeterminantTameSymbol
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q] :
    TameSymbol A Q :=
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_num)
  (periodicDeterminantRegularTameSymbol hdim).extend Q

end Stacks.Chow

end

end
