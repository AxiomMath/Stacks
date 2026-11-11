module

public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Self
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Steinberg
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction
public import StacksFrontier.RingTheory.LocalRing.PrepareTwoNonZeroDivisors

/-!
# The tame symbol of a one-dimensional Noetherian local ring

For a Noetherian local ring `(A, 𝔪)` of dimension one, the symbol of Stacks 02PZ for the module
`M = A`, restricted to pairs of nonzerodivisors of `A`, satisfies Stacks 0EAL, 0EAM, 0EAN and
0EAP. Its extension to `Q(A)^*` is a tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

satisfying the properties listed in Stacks 0EAH. (The section itself defines `∂_A` by the recipe
Stacks 0EAQ; that this symbol is that recipe is
`Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol`, and Stacks 0EAH is
`Stacks.Chow.formulaTameSymbol_isTameSymbol`.) No assumption beyond "Noetherian local of dimension one" is made;
in particular `A` need not be a domain or reduced.

## Main definitions

* `Stacks.Chow.regularModuleSymbol` — the symbol of Stacks 02PZ for `M = A`, on a pair of
  nonzerodivisors of `A`.
* `Stacks.Chow.regularTameSymbolOfKrullDimOne` — the tame symbol on pairs of nonzerodivisors, for
  every one-dimensional Noetherian local ring.
* `Stacks.Chow.tameSymbolOfKrullDimOne` — the tame symbol on `Q(A)^*`, for every
  one-dimensional Noetherian local ring.
* `Stacks.Chow.tameSymbolOfKrullDimOneDomain` — the specialization to a one-dimensional
  Noetherian local domain, as a term of `AlgebraicGeometry.TameSymbol`.

## Main results

* `Stacks.Chow.moduleLength_quotient_range_lsmul` — `length_A(A/bA)` is `Ring.ord A b`.
* `Stacks.Chow.regularModuleSymbol_mul_left`, `Stacks.Chow.regularModuleSymbol_mul_right`,
  `Stacks.Chow.regularModuleSymbol_self`, `Stacks.Chow.regularModuleSymbol_unit_left`,
  `Stacks.Chow.regularModuleSymbol_steinberg` — Stacks 0EAL, 0EAM, 0EAN and 0EAP for it.
* `Stacks.Chow.tameSymbolOfKrullDimOne_regularFractionUnit` — the symbol on `Q(A)^*` restricts
  to `AlgebraicGeometry.moduleSymbol` on nonzerodivisors of `A`.
* `Stacks.Chow.regularModuleSymbol_eq_regularSymbol` — for a domain, `regularModuleSymbol` is
  `AlgebraicGeometry.regularSymbol`.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public section

open IsLocalRing Module.FiniteLength

universe u v

namespace Stacks.Chow

/-! ### Replacing an argument of the symbol by an equal element -/

section Congr

variable {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The symbol of Stacks 02PZ depends on its first argument only through the element, not through
the chosen witness of its regularity. -/
theorem moduleSymbol_congr_left (a a' b : A) (h : a = a') (ha : IsSMulRegular M a)
    (ha' : IsSMulRegular M a') (hb : IsSMulRegular M b) (hd : Module.supportDim A M = 1) :
    AlgebraicGeometry.moduleSymbol a b ha hb hd =
      AlgebraicGeometry.moduleSymbol a' b ha' hb hd := by
  subst h
  rfl

/-- The symbol of Stacks 02PZ depends on its second argument only through the element, not through
the chosen witness of its regularity. -/
theorem moduleSymbol_congr_right (a b b' : A) (h : b = b') (ha : IsSMulRegular M a)
    (hb : IsSMulRegular M b) (hb' : IsSMulRegular M b') (hd : Module.supportDim A M = 1) :
    AlgebraicGeometry.moduleSymbol a b ha hb hd =
      AlgebraicGeometry.moduleSymbol a b' ha hb' hd := by
  subst h
  rfl

end Congr

/-! ### The length of the quotient by a principal ideal -/

section Length

variable {A : Type u} [CommRing A]

/-- `length_A(A/bA)`, written as the length of the quotient by the range of multiplication by
`b`, is the order of vanishing `Ring.ord A b` of Stacks 02MD. -/
theorem moduleLength_quotient_range_lsmul (b : A) :
    moduleLength A (A ⧸ (LinearMap.lsmul A A b).range) = (Ring.ord A b).toNat := by
  have hrange : (LinearMap.lsmul A A b).range = Ideal.span {b} := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  rw [hrange]
  rfl

/-- A nonzerodivisor of `A` is a regular element of the `A`-module `A`. -/
private theorem isSMulRegular_of_mem_nonZeroDivisors (a : nonZeroDivisors A) :
    IsSMulRegular A (a : A) :=
  (isRegular_iff_mem_nonZeroDivisors.mpr a.2).isSMulRegular

/-- If `A` has Krull dimension one, then the `A`-module `A` has support dimension one. -/
private theorem supportDim_self_eq_one (hdim : ringKrullDim A = 1) : Module.supportDim A A = 1 :=
  (Module.supportDim_self_eq_ringKrullDim A).trans hdim

end Length

/-! ### The symbol of Stacks 02PZ on the ring itself -/

section KrullDimOne

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The symbol of Stacks 02PZ for the module `M = A`, on a pair of nonzerodivisors of `A`. -/
noncomputable def regularModuleSymbol (hdim : ringKrullDim A = 1) (a b : nonZeroDivisors A) :
    (ResidueField A)ˣ :=
  AlgebraicGeometry.moduleSymbol (M := A) a b
    (isRegular_iff_mem_nonZeroDivisors.mpr a.2).isSMulRegular
    (isRegular_iff_mem_nonZeroDivisors.mpr b.2).isSMulRegular
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

variable (hdim : ringKrullDim A = 1)

/-- `Stacks.Chow.regularModuleSymbol` is the symbol of Stacks 02PZ, for any witnesses of the
hypotheses. -/
theorem regularModuleSymbol_eq_moduleSymbol (a b : nonZeroDivisors A)
    (ha : IsSMulRegular A (a : A)) (hb : IsSMulRegular A (b : A))
    (hd : Module.supportDim A A = 1) :
    regularModuleSymbol hdim a b =
      AlgebraicGeometry.moduleSymbol (M := A) (a : A) (b : A) ha hb hd :=
  rfl

/-- **Stacks 0EAL.** `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')`. -/
theorem regularModuleSymbol_mul_right (a b c : nonZeroDivisors A) :
    regularModuleSymbol hdim a (b * c) =
      regularModuleSymbol hdim a b * regularModuleSymbol hdim a c :=
  AlgebraicGeometry.moduleSymbol_mul_right (A := A) (M := A) a b c
    (isSMulRegular_of_mem_nonZeroDivisors a)
    (isSMulRegular_of_mem_nonZeroDivisors b)
    (isSMulRegular_of_mem_nonZeroDivisors c)
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- Swapping the two arguments inverts the symbol. -/
theorem regularModuleSymbol_swap (a b : nonZeroDivisors A) :
    regularModuleSymbol hdim a b * regularModuleSymbol hdim b a = 1 :=
  AlgebraicGeometry.moduleSymbol_mul_swap (A := A) (M := A) a b
    (isSMulRegular_of_mem_nonZeroDivisors a)
    (isSMulRegular_of_mem_nonZeroDivisors b)
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- The symbol is trivial when its second argument is `1`. -/
theorem regularModuleSymbol_one_right (a : nonZeroDivisors A) :
    regularModuleSymbol hdim a 1 = 1 := by
  simpa using regularModuleSymbol_mul_right hdim a 1 1

/-- **Stacks 0EAL.** `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)`. -/
theorem regularModuleSymbol_mul_left (a b c : nonZeroDivisors A) :
    regularModuleSymbol hdim (a * b) c =
      regularModuleSymbol hdim a c * regularModuleSymbol hdim b c := by
  rw [mul_eq_one_iff_eq_inv.mp (regularModuleSymbol_swap hdim (a * b) c),
    regularModuleSymbol_mul_right, mul_inv_rev,
    ← mul_eq_one_iff_eq_inv.mp (regularModuleSymbol_swap hdim a c),
    ← mul_eq_one_iff_eq_inv.mp (regularModuleSymbol_swap hdim b c)]
  ac_rfl

/-- **Stacks 0EAM.** `∂_A(b, b) = (-1)^m` with `m = length_A(A/bA)`. -/
theorem regularModuleSymbol_self (b : nonZeroDivisors A) :
    regularModuleSymbol hdim b b = (-1) ^ (Ring.ord A (b : A)).toNat :=
  (AlgebraicGeometry.moduleSymbol_self_eq_negOne_pow_length (A := A) (M := A) b
    (isSMulRegular_of_mem_nonZeroDivisors b)
    (supportDim_self_eq_one hdim)).trans
    (by rw [moduleLength_quotient_range_lsmul])

/-- **Stacks 0EAN.** `∂_A(u, b) = u^m mod 𝔪` with `m = length_A(A/bA)`, for `u ∈ A` a unit. -/
theorem regularModuleSymbol_unit_left (a b : nonZeroDivisors A) (u : Aˣ) (hu : (a : A) = u) :
    regularModuleSymbol hdim a b =
      Units.map (residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat := by
  have hb := isSMulRegular_of_mem_nonZeroDivisors b
  have hd := supportDim_self_eq_one hdim
  have hcongr : regularModuleSymbol hdim a b =
      AlgebraicGeometry.moduleSymbol (M := A) ((u : Aˣ) : A) (b : A)
        (Units.isSMulRegular A u) hb hd :=
    moduleSymbol_congr_left (M := A) (a : A) ((u : Aˣ) : A) (b : A) hu _ _ hb hd
  apply Units.ext
  rw [hcongr, AlgebraicGeometry.moduleSymbol_unit_left_ring u (b : A) hb hdim]
  simp

/-- **Stacks 0EAP.** `∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)`. -/
theorem regularModuleSymbol_steinberg (a b c : nonZeroDivisors A)
    (hc : (c : A) = (b : A) - (a : A)) :
    regularModuleSymbol hdim a c * regularModuleSymbol hdim b b =
      regularModuleSymbol hdim b c * regularModuleSymbol hdim a b := by
  have hd := supportDim_self_eq_one hdim
  have hba : IsSMulRegular A ((b : A) - (a : A)) := hc ▸ isSMulRegular_of_mem_nonZeroDivisors c
  have h : ∀ x : nonZeroDivisors A, regularModuleSymbol hdim x c =
      AlgebraicGeometry.moduleSymbol (M := A) (x : A) ((b : A) - (a : A))
        (isSMulRegular_of_mem_nonZeroDivisors x) hba hd := fun x =>
    moduleSymbol_congr_right (M := A) (x : A) (c : A) ((b : A) - (a : A)) hc _ _ hba hd
  rw [h a, h b]
  exact AlgebraicGeometry.moduleSymbol_steinberg_prepare (a : A) (b : A)
    (isSMulRegular_of_mem_nonZeroDivisors a) (isSMulRegular_of_mem_nonZeroDivisors b) hba hd

/-- A tame symbol of a one-dimensional Noetherian local ring `A` on pairs of nonzerodivisors:
the symbol of Stacks 02PZ on the module `A` itself, which satisfies Stacks 0EAL, 0EAM, 0EAN and
0EAP. Section 0EAH defines `∂_A` by the recipe Stacks 0EAQ instead; that recipe is
`Stacks.Chow.formulaRegularTameSymbol`, the two agree by
`Stacks.Chow.regularTameSymbolOfKrullDimOne_eq_formulaRegularTameSymbol`, and Stacks 0EAH itself
is `Stacks.Chow.formulaTameSymbol_isTameSymbol`. -/
noncomputable def regularTameSymbolOfKrullDimOne : RegularTameSymbol A where
  toFun := regularModuleSymbol hdim
  map_mul_left := regularModuleSymbol_mul_left hdim
  map_mul_right := regularModuleSymbol_mul_right hdim
  self := regularModuleSymbol_self hdim
  unit_left := regularModuleSymbol_unit_left hdim
  steinberg := regularModuleSymbol_steinberg hdim

/-- `Stacks.Chow.regularTameSymbolOfKrullDimOne` evaluates to
`Stacks.Chow.regularModuleSymbol`. -/
@[simp]
theorem regularTameSymbolOfKrullDimOne_apply (a b : nonZeroDivisors A) :
    regularTameSymbolOfKrullDimOne hdim a b = regularModuleSymbol hdim a b :=
  rfl

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A ring of Krull dimension one satisfies `Ring.KrullDimLE 1`. -/
theorem krullDimLE_one_of_ringKrullDim_eq_one (hdim' : ringKrullDim A = 1) :
    Ring.KrullDimLE 1 A :=
  Ring.krullDimLE_iff.mpr (by rw [hdim']; exact_mod_cast le_rfl)

/-- A tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of a one-dimensional Noetherian local
ring `A`, satisfying Stacks 0EAI, 0EAJ and 0EAK: the extension
(`Stacks.Chow.RegularTameSymbol.extend`) of the symbol of Stacks 02PZ on pairs of
nonzerodivisors. It is the map `Stacks.Chow.formulaTameSymbol` that the recipe Stacks 0EAQ
defines, by `Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol`; Stacks 0EAH (the seven
properties of that map) is `Stacks.Chow.formulaTameSymbol_isTameSymbol`. -/
noncomputable def tameSymbolOfKrullDimOne (Q : Type v) [CommRing Q] [Algebra A Q]
    [IsFractionRing A Q] : TameSymbol A Q :=
  haveI := krullDimLE_one_of_ringKrullDim_eq_one hdim
  (regularTameSymbolOfKrullDimOne hdim).extend Q

/-- The tame symbol of `Stacks.Chow.tameSymbolOfKrullDimOne` restricts on pairs of
nonzerodivisors of `A` to the symbol of Stacks 02PZ. -/
theorem tameSymbolOfKrullDimOne_regularFractionUnit (Q : Type v) [CommRing Q] [Algebra A Q]
    [IsFractionRing A Q] (a b : nonZeroDivisors A) :
    tameSymbolOfKrullDimOne hdim Q (regularFractionUnit a) (regularFractionUnit b) =
      regularModuleSymbol hdim a b :=
  have := krullDimLE_one_of_ringKrullDim_eq_one hdim
  (regularTameSymbolOfKrullDimOne hdim).extend_regularFractionUnit Q a b

end KrullDimOne

/-! ### The specialization to a one-dimensional Noetherian local domain -/

section Domain

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
  (hdim : ringKrullDim A = 1)

/-- For a one-dimensional Noetherian local domain, `Stacks.Chow.regularModuleSymbol` is the symbol
`AlgebraicGeometry.regularSymbol`. -/
theorem regularModuleSymbol_eq_regularSymbol (a b : nonZeroDivisors A) :
    regularModuleSymbol hdim a b = AlgebraicGeometry.regularSymbol hdim a b :=
  rfl

/-- `Stacks.Chow.tameSymbolOfKrullDimOne` for a one-dimensional Noetherian local domain `A` with
fraction field `K`, as a term of `AlgebraicGeometry.TameSymbol`: a bimultiplicative pairing on
`Kˣ` with values in `κ(𝔪)^*` agreeing with the symbol of Stacks 02PZ on nonzerodivisors of
`A`. -/
noncomputable def tameSymbolOfKrullDimOneDomain :
    AlgebraicGeometry.TameSymbol (A := A) (K := K) hdim where
  toFun := tameSymbolOfKrullDimOne hdim K
  map_mul_left x x' y := (tameSymbolOfKrullDimOne hdim K).map_mul_left x x' y
  map_mul_right x y y' := (tameSymbolOfKrullDimOne hdim K).map_mul_right x y y'
  eq_moduleSymbol a b ha hb :=
    tameSymbolOfKrullDimOne_regularFractionUnit hdim K
      ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩
      ⟨b, isRegular_iff_mem_nonZeroDivisors.mp hb⟩

end Domain

end Stacks.Chow

end
