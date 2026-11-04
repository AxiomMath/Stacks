module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Defs

/-!
# The tame symbol on the total ring of fractions

Stacks 0EAH asks for a tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

on the total ring of fractions of a one-dimensional Noetherian local ring `A`, satisfying

* Stacks 0EAI, `∂_A(f, g h) = ∂_A(f, g) ∂_A(f, h)`;
* Stacks 0EAJ, `∂_A(f, g) ∂_A(g, f) = 1`;
* Stacks 0EAK, `∂_A(f, 1 - f) = 1` whenever `f` and `1 - f` are both units.

The source constructs it from a symbol on pairs of nonzerodivisors of `A` — the data recorded by
`Stacks.Chow.RegularTameSymbol` — by the formula

`∂_A(a/b, c/d) = ∂_A(a, c) ∂_A(a, d)⁻¹ ∂_A(b, c)⁻¹ ∂_A(b, d)`,

and leaves as an exercise that this is well defined and has the three properties above. That
exercise is what this file proves: `Stacks.Chow.RegularTameSymbol.extend` is the resulting tame
symbol and `Stacks.Chow.RegularTameSymbol.extend_eq` is the displayed formula, valid for every
presentation of the two arguments as quotients of nonzerodivisors.

Well-definedness uses only bimultiplicativity (Stacks 0EAL): two presentations with `a/b = a'/b'`
satisfy `a b' = a' b`, so `∂_A(a, c) ∂_A(b, c)⁻¹ = ∂_A(a', c) ∂_A(b', c)⁻¹`. Skew-symmetry on
`Q(A)^*` reduces to skew-symmetry on nonzerodivisors, which is
`Stacks.Chow.RegularTameSymbol.skew`, and the Steinberg relation on `Q(A)^*` is exactly
Stacks 0EAP applied to the presentations `f = a/b` and `1 - f = (b - a)/b`.

The extension is unique: `Stacks.Chow.TameSymbol.eq_extend_apply` shows that a tame symbol on
`Q(A)^*` is determined by its restriction to nonzerodivisors of `A`, because bimultiplicativity
on a group is determined by its values on generators.

## Main definitions

* `Stacks.Chow.TameSymbol` — a tame symbol on `Q(A)^*`, as Stacks 0EAH asks for it.
* `Stacks.Chow.RegularTameSymbol.extend` — the extension of a symbol on nonzerodivisors.

## Main results

* `Stacks.Chow.RegularTameSymbol.extend_eq` — the defining fraction formula.
* `Stacks.Chow.RegularTameSymbol.extend_regularFractionUnit` — the extension restricts to the
  given symbol on nonzerodivisors.
* `Stacks.Chow.TameSymbol.eq_extend_apply` — uniqueness of the extension.

## Implementation notes

Identities in the commutative group `κ(𝔪)^*` are discharged by transporting to the additive
group `Additive κ(𝔪)^*` and calling `abel` (or `linear_combination (norm := abel)` when a
hypothesis is involved); there is no multiplicative analogue of `abel`, and `group` does not use
commutativity.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAS](https://stacks.math.columbia.edu/tag/0EAS)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

/-- **Stacks 0EAH, the tame symbol.** A tame symbol on the total ring of fractions `Q` of a
one-dimensional Noetherian local ring `A` is a map `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` which is
multiplicative in its second argument (Stacks 0EAI), skew-symmetric (Stacks 0EAJ) and satisfies
the Steinberg relation `∂_A(f, 1 - f) = 1` (Stacks 0EAK).

Multiplicativity in the first argument is a consequence, `Stacks.Chow.TameSymbol.map_mul_left`.
The source does not claim such a map is unique, and gives a recipe producing one; the recipe is
`Stacks.Chow.RegularTameSymbol.extend` applied to the datum Stacks 0EAQ constructs. -/
structure TameSymbol (A : Type u) [CommRing A] [IsLocalRing A]
    (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q] where
  /-- The symbol `∂_A(f, g)` on a pair of units of `Q(A)`. -/
  toFun : Qˣ → Qˣ → (ResidueField A)ˣ
  /-- **Stacks 0EAI.** `∂_A(f, g h) = ∂_A(f, g) ∂_A(f, h)`. -/
  map_mul_right (f g h : Qˣ) : toFun f (g * h) = toFun f g * toFun f h
  /-- **Stacks 0EAJ.** `∂_A(f, g) ∂_A(g, f) = 1`. -/
  skew (f g : Qˣ) : toFun f g * toFun g f = 1
  /-- **Stacks 0EAK.** `∂_A(f, 1 - f) = 1` for `f` and `1 - f` units of `Q(A)`. -/
  steinberg (f g : Qˣ) (h : (f : Q) + (g : Q) = 1) : toFun f g = 1

namespace TameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] {Q : Type v} [CommRing Q] [Algebra A Q]
  [IsFractionRing A Q] (symb : TameSymbol A Q)

/-- A tame symbol is applied to a pair of units of `Q` as a function. -/
instance : CoeFun (TameSymbol A Q) fun _ ↦ Qˣ → Qˣ → (ResidueField A)ˣ := ⟨TameSymbol.toFun⟩

/-- The symbol is trivial when its second argument is `1`. -/
@[simp]
theorem one_right (f : Qˣ) : symb f 1 = 1 :=
  right_eq_mul.mp (by simpa only [one_mul] using symb.map_mul_right f 1 1)

/-- The symbol is trivial when its first argument is `1`. -/
@[simp]
theorem one_left (f : Qˣ) : symb 1 f = 1 := by
  have h := symb.skew 1 f
  rwa [symb.one_right, mul_one] at h

/-- **Stacks 0EAJ**, in the form `∂_A(g, f) = ∂_A(f, g)⁻¹`. -/
theorem symm_eq_inv (f g : Qˣ) : symb g f = (symb f g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact symb.skew f g)

/-- **Stacks 0EAI in the first argument.** `∂_A(f g, h) = ∂_A(f, h) ∂_A(g, h)`; this follows from
multiplicativity in the second argument together with skew-symmetry. -/
theorem map_mul_left (f g h : Qˣ) : symb (f * g) h = symb f h * symb g h := by
  rw [symb.symm_eq_inv h (f * g), symb.map_mul_right h f g, mul_inv, ← symb.symm_eq_inv h f,
    ← symb.symm_eq_inv h g]

/-- The symbol inverts under inversion of its second argument. -/
theorem inv_right (f g : Qˣ) : symb f g⁻¹ = (symb f g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← symb.map_mul_right, inv_mul_cancel, symb.one_right])

/-- The symbol inverts under inversion of its first argument. -/
theorem inv_left (f g : Qˣ) : symb f⁻¹ g = (symb f g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← symb.map_mul_left, inv_mul_cancel, symb.one_left])

end TameSymbol

section Presentation

variable {A : Type u} [CommRing A] (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]

/-- A chosen numerator of a unit of `Q(A)`, as a nonzerodivisor of `A`. -/
def fractionNum (f : Qˣ) : nonZeroDivisors A :=
  (exists_regularFractionUnit_div (A := A) (Q := Q) f).choose

/-- A chosen denominator of a unit of `Q(A)`, as a nonzerodivisor of `A`. -/
def fractionDen (f : Qˣ) : nonZeroDivisors A :=
  (exists_regularFractionUnit_div (A := A) (Q := Q) f).choose_spec.choose

/-- The chosen presentation of a unit of `Q(A)` as a quotient of nonzerodivisors of `A`. -/
theorem regularFractionUnit_fractionNum_div_fractionDen (f : Qˣ) :
    f = regularFractionUnit (fractionNum (A := A) Q f) *
      (regularFractionUnit (Q := Q) (fractionDen (A := A) Q f))⁻¹ :=
  (exists_regularFractionUnit_div (A := A) (Q := Q) f).choose_spec.choose_spec

/-- Any presentation `f = a/b` is cross-multiplication equivalent to the chosen one. -/
private theorem fractionNum_mul_eq {f : Qˣ} {a b : nonZeroDivisors A}
    (hf : f = regularFractionUnit a * (regularFractionUnit (Q := Q) b)⁻¹) :
    fractionNum (A := A) Q f * b = a * fractionDen (A := A) Q f :=
  regularFractionUnit_div_eq_iff.mp
    ((regularFractionUnit_fractionNum_div_fractionDen Q f).symm.trans hf)

end Presentation

namespace RegularTameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] (symb : RegularTameSymbol A)
variable (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]

/-- The right hand side of the fraction formula of Stacks 0EAH:
`∂_A(a, c) ∂_A(a, d)⁻¹ ∂_A(b, c)⁻¹ ∂_A(b, d)`, the candidate value of the extended symbol on the
pair of fractions `a/b` and `c/d`. -/
def fractionAux (a b c d : nonZeroDivisors A) : (ResidueField A)ˣ :=
  symb a c * (symb a d)⁻¹ * (symb b c)⁻¹ * symb b d

/-- The fraction formula, grouped by its second argument. -/
theorem fractionAux_eq_div_second (a b c d : nonZeroDivisors A) :
    symb.fractionAux a b c d = symb a c / symb b c / (symb a d / symb b d) := by
  apply Additive.ofMul.injective
  simp only [fractionAux, div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

/-- The fraction formula, grouped by its first argument. -/
theorem fractionAux_eq_div_first (a b c d : nonZeroDivisors A) :
    symb.fractionAux a b c d = symb a c / symb a d / (symb b c / symb b d) := by
  apply Additive.ofMul.injective
  simp only [fractionAux, div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

/-- The fraction formula only depends on the fraction `a/b`: this is where bimultiplicativity
(Stacks 0EAL) is used. -/
theorem fractionAux_congr_left {a b a' b' : nonZeroDivisors A} (h : a * b' = a' * b)
    (c d : nonZeroDivisors A) : symb.fractionAux a b c d = symb.fractionAux a' b' c d := by
  have key (e : nonZeroDivisors A) : symb a e / symb b e = symb a' e / symb b' e :=
    div_eq_div_iff_mul_eq_mul.mpr (by rw [← symb.map_mul_left, ← symb.map_mul_left, h])
  rw [fractionAux_eq_div_second, fractionAux_eq_div_second, key c, key d]

/-- The fraction formula only depends on the fraction `c/d`: again by bimultiplicativity. -/
theorem fractionAux_congr_right (a b : nonZeroDivisors A) {c d c' d' : nonZeroDivisors A}
    (h : c * d' = c' * d) : symb.fractionAux a b c d = symb.fractionAux a b c' d' := by
  have key (e : nonZeroDivisors A) : symb e c / symb e d = symb e c' / symb e d' :=
    div_eq_div_iff_mul_eq_mul.mpr (by rw [← symb.map_mul_right, ← symb.map_mul_right, h])
  rw [fractionAux_eq_div_first, fractionAux_eq_div_first, key a, key b]

/-- The underlying map of `Stacks.Chow.RegularTameSymbol.extend`: the fraction formula of
Stacks 0EAH, evaluated on the chosen presentations of its two arguments as quotients of
nonzerodivisors of `A`. -/
def extendFun (f g : Qˣ) : (ResidueField A)ˣ :=
  symb.fractionAux (fractionNum (A := A) Q f) (fractionDen (A := A) Q f)
    (fractionNum (A := A) Q g) (fractionDen (A := A) Q g)

/-- The extended symbol is computed by the fraction formula of Stacks 0EAH for *every*
presentation of its arguments as quotients of nonzerodivisors of `A`, not only for the chosen
one. -/
theorem extendFun_eq {f g : Qˣ} (a b c d : nonZeroDivisors A)
    (hf : f = regularFractionUnit a * (regularFractionUnit (Q := Q) b)⁻¹)
    (hg : g = regularFractionUnit c * (regularFractionUnit (Q := Q) d)⁻¹) :
    symb.extendFun Q f g = symb.fractionAux a b c d := by
  rw [extendFun, symb.fractionAux_congr_left (fractionNum_mul_eq Q hf),
    symb.fractionAux_congr_right a b (fractionNum_mul_eq Q hg)]

/-- **Stacks 0EAI for the extended symbol.** -/
theorem extendFun_map_mul_right (f g h : Qˣ) :
    symb.extendFun Q f (g * h) = symb.extendFun Q f g * symb.extendFun Q f h := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) g
  obtain ⟨e, k, hh⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) h
  have hgh : g * h =
      regularFractionUnit (c * e) * (regularFractionUnit (Q := Q) (d * k))⁻¹ := by
    rw [hg, hh, map_mul, map_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [symb.extendFun_eq Q a b (c * e) (d * k) hf hgh, symb.extendFun_eq Q a b c d hf hg,
    symb.extendFun_eq Q a b e k hf hh]
  apply Additive.ofMul.injective
  simp only [fractionAux, symb.map_mul_right, ofMul_mul, ofMul_inv]
  abel

/-- **Stacks 0EAK for the extended symbol.** The presentation `f = a/b` forces
`1 - f = (b - a)/b`, and the identity is then exactly Stacks 0EAP. -/
theorem extendFun_steinberg (f g : Qˣ) (hfg : (f : Q) + (g : Q) = 1) :
    symb.extendFun Q f g = 1 := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  have hfbU : f * regularFractionUnit (Q := Q) b = regularFractionUnit a := by
    rw [hf, inv_mul_cancel_right]
  have hfb : (f : Q) * (regularFractionUnit (Q := Q) b : Q) = algebraMap A Q a := by
    rw [← Units.val_mul, hfbU, regularFractionUnit_val]
  have hval : (g * regularFractionUnit (Q := Q) b : Q) =
      algebraMap A Q ((b : A) - (a : A)) := by
    have hg : (g : Q) = 1 - (f : Q) := by rw [eq_sub_iff_add_eq, add_comm]; exact hfg
    rw [hg, sub_mul, one_mul, hfb, map_sub, regularFractionUnit_val]
  have hc : ((b : A) - (a : A)) ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_of_isUnit_algebraMap (Q := Q) ?_
    rw [← hval]
    exact (g * regularFractionUnit b).isUnit
  have hg : g = regularFractionUnit ⟨(b : A) - (a : A), hc⟩ *
      (regularFractionUnit (Q := Q) b)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr (Units.ext (by rw [regularFractionUnit_val]; exact hval))
  have hst := symb.steinberg a b ⟨(b : A) - (a : A), hc⟩ rfl
  rw [symb.extendFun_eq Q a b ⟨(b : A) - (a : A), hc⟩ b hf hg, fractionAux]
  apply Additive.ofMul.injective
  replace hst : Additive.ofMul (symb a ⟨(b : A) - (a : A), hc⟩) + Additive.ofMul (symb b b) =
      Additive.ofMul (symb b ⟨(b : A) - (a : A), hc⟩) + Additive.ofMul (symb a b) := by
    simpa only [ofMul_mul] using congrArg Additive.ofMul hst
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  linear_combination (norm := abel) hst

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- **Stacks 0EAJ for the extended symbol.** -/
theorem extendFun_skew (f g : Qˣ) : symb.extendFun Q f g * symb.extendFun Q g f = 1 := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) g
  rw [symb.extendFun_eq Q a b c d hf hg, symb.extendFun_eq Q c d a b hg hf]
  apply Additive.ofMul.injective
  simp only [fractionAux, symb.symm_eq_inv a c, symb.symm_eq_inv a d, symb.symm_eq_inv b c,
    symb.symm_eq_inv b d, ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- **Stacks 0EAH, the tame symbol of a one-dimensional Noetherian local ring.** The symbol on
pairs of nonzerodivisors of `A` extends to the units of the total ring of fractions `Q(A)` by the
formula `∂_A(a/b, c/d) = ∂_A(a, c) ∂_A(a, d)⁻¹ ∂_A(b, c)⁻¹ ∂_A(b, d)`, and the extension
satisfies Stacks 0EAI, 0EAJ and 0EAK.

This is the "exercise" of Stacks 0EAH and the second half of Stacks 0EAS: the properties
Stacks 0EAL, 0EAM, 0EAN and 0EAP of the symbol on nonzerodivisors give the three properties of
the symbol on `Q(A)^*`. The symbol on nonzerodivisors is an argument here rather than the explicit
product of Stacks 0EAQ. The 0EAQ half — the first half of Stacks 0EAS — is supplied in
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.PairSymbol`, for an arbitrary one-dimensional
Noetherian local ring: `Stacks.Chow.tameSymbolValue` is the symbol of an arbitrary pair of
nonzerodivisors, `Stacks.Chow.tameSymbolValue_eq_symbolValue` identifies it with the product
formula of Stacks 0EAQ at every preparation, and `Stacks.Chow.formulaTameSymbol` feeds it through
this definition to deliver the map on `Q(A)^*`. -/
@[stacks 0EAS "the passage from (4), (5), (6), (7) to (1), (2), (3), for a symbol on \
nonzerodivisors given as data rather than by the product formula of Stacks 0EAQ"]
def extend : TameSymbol A Q where
  toFun := symb.extendFun Q
  map_mul_right := symb.extendFun_map_mul_right Q
  skew := symb.extendFun_skew Q
  steinberg := symb.extendFun_steinberg Q

/-- The extended symbol evaluates to `extendFun` on every pair of units of `Q`. -/
@[simp]
theorem extend_apply (f g : Qˣ) : (symb.extend Q) f g = symb.extendFun Q f g := rfl

/-- **The defining formula of Stacks 0EAH.** `∂_A(a/b, c/d)` is
`∂_A(a, c) ∂_A(a, d)⁻¹ ∂_A(b, c)⁻¹ ∂_A(b, d)`, for every presentation of the arguments as
quotients of nonzerodivisors of `A`. -/
theorem extend_eq {f g : Qˣ} (a b c d : nonZeroDivisors A)
    (hf : f = regularFractionUnit a * (regularFractionUnit (Q := Q) b)⁻¹)
    (hg : g = regularFractionUnit c * (regularFractionUnit (Q := Q) d)⁻¹) :
    (symb.extend Q) f g = symb a c * (symb a d)⁻¹ * (symb b c)⁻¹ * symb b d :=
  symb.extendFun_eq Q a b c d hf hg

/-- The extended symbol restricts to the given symbol on nonzerodivisors of `A`. -/
@[simp]
theorem extend_regularFractionUnit (a c : nonZeroDivisors A) :
    (symb.extend Q) (regularFractionUnit a) (regularFractionUnit c) = symb a c := by
  rw [symb.extend_eq Q a 1 c 1 (by simp) (by simp)]
  simp

end RegularTameSymbol

namespace TameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {Q : Type v} [CommRing Q] [Algebra A Q] [IsFractionRing A Q]

/-- **The extension of Stacks 0EAH is unique.** A tame symbol on `Q(A)^*` is determined by its
restriction to nonzerodivisors of `A`: every unit of `Q(A)` is a quotient of two of them, and the
symbol is bimultiplicative. -/
theorem eq_extend_apply (T : TameSymbol A Q) (symb : RegularTameSymbol A)
    (h : ∀ a c : nonZeroDivisors A,
      T (regularFractionUnit a) (regularFractionUnit c) = symb a c) (f g : Qˣ) :
    T f g = (symb.extend Q) f g := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) g
  rw [symb.extend_eq Q a b c d hf hg, hf, hg, T.map_mul_left, T.inv_left, T.map_mul_right,
    T.map_mul_right, T.inv_right, T.inv_right, h a c, h a d, h b c, h b d]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end TameSymbol

end Stacks.Chow

end
