module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FormulaTower

/-!
# Stacks 0EAH: the tame symbol of the recipe Stacks 0EAQ and its seven properties

Let `(A, 𝔪)` be a Noetherian local ring of dimension one, with total ring of fractions `Q(A)`.
Section 0EAH of the Stacks project asks for a map

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

with the seven properties

1. `∂_A(f, g h) = ∂_A(f, g) ∂_A(f, h)` (Stacks 0EAI);
2. `∂_A(f, g) ∂_A(g, f) = 1` (Stacks 0EAJ);
3. `∂_A(f, 1 - f) = 1` when `f` and `1 - f` are units of `Q(A)` (Stacks 0EAK);
4. `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)` and `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')` for
   nonzerodivisors `a, a', b, b'` of `A` (Stacks 0EAL);
5. `∂_A(b, b) = (-1)^m`, `m = length_A(A/bA)`, for `b` a nonzerodivisor (Stacks 0EAM);
6. `∂_A(u, b) = u^m mod 𝔪`, `m = length_A(A/bA)`, for `u ∈ A^*` and `b` a nonzerodivisor
   (Stacks 0EAN);
7. `∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)` when `a, b, b - a` are nonzerodivisors
   (Stacks 0EAP).

It does not claim such a map is unique; it defines `∂_A` by the recipe Stacks 0EAQ on pairs of
nonzerodivisors, extended to `Q(A)^*` by the fraction formula.

`Stacks.Chow.IsTameSymbol` is the predicate "satisfies (1)–(7)" on a function
`Q(A)^* × Q(A)^* → κ(𝔪)^*`. `Stacks.Chow.formulaTameSymbol_isTameSymbol` is the content of the
section: the map `Stacks.Chow.formulaTameSymbol` built from the recipe satisfies all seven
properties, and on a pair of nonzerodivisors of `A` it is the recipe Stacks 0EAQ itself,
`Stacks.Chow.tameSymbolFormula` (the displayed product on one chosen extension of Stacks 0EAG,
which by `Stacks.Chow.tameSymbolFormula_eq` is the displayed product on every such extension).
No hypothesis beyond the source's is made: `A` is Noetherian local with `ringKrullDim A = 1`.

## Main definitions

* `Stacks.Chow.IsTameSymbol` — the seven properties of Stacks 0EAH.

## Main results

* `Stacks.Chow.tameSymbolValue_eq_tameSymbolFormula` — the function of a pair of
  `Stacks.Chow.tameSymbolValue` is the recipe `Stacks.Chow.tameSymbolFormula`.
* `Stacks.Chow.formulaTameSymbol_regularFractionUnit_eq_tameSymbolFormula` — on nonzerodivisors
  of `A` the map `Stacks.Chow.formulaTameSymbol` is the recipe Stacks 0EAQ.
* `Stacks.Chow.formulaTameSymbol_isTameSymbol` — Stacks 0EAH.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAS](https://stacks.math.columbia.edu/tag/0EAS)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Chow

/-- **The seven properties of a tame symbol, Stacks 0EAH.** A function
`∂ : Q(A)^* × Q(A)^* → κ(𝔪)^*` on the units of the total ring of fractions `Q` of a local ring
`A` satisfies properties (1)–(7) of Stacks 0EAH; properties (4)–(7) concern nonzerodivisors of
`A`, read in `Q(A)^*` through `Stacks.Chow.regularFractionUnit`, and `length_A(A/bA)` is
`Ring.ord A b`. -/
structure IsTameSymbol (A : Type u) [CommRing A] [IsLocalRing A] (Q : Type v) [CommRing Q]
    [Algebra A Q] [IsFractionRing A Q] (symb : Qˣ → Qˣ → (ResidueField A)ˣ) : Prop where
  /-- **(1), Stacks 0EAI.** `∂_A(f, g h) = ∂_A(f, g) ∂_A(f, h)`. -/
  map_mul_right (f g h : Qˣ) : symb f (g * h) = symb f g * symb f h
  /-- **(2), Stacks 0EAJ.** `∂_A(f, g) ∂_A(g, f) = 1`. -/
  mul_swap (f g : Qˣ) : symb f g * symb g f = 1
  /-- **(3), Stacks 0EAK.** `∂_A(f, 1 - f) = 1` for `f` and `1 - f` units of `Q(A)`. -/
  apply_one_sub (f g : Qˣ) (hg : (g : Q) = 1 - (f : Q)) : symb f g = 1
  /-- **(4), Stacks 0EAL, first argument.** `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)`. -/
  regular_mul_left (a a' b : nonZeroDivisors A) :
    symb (regularFractionUnit (a * a')) (regularFractionUnit b) =
      symb (regularFractionUnit a) (regularFractionUnit b) *
        symb (regularFractionUnit a') (regularFractionUnit b)
  /-- **(4), Stacks 0EAL, second argument.** `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')`. -/
  regular_mul_right (a b b' : nonZeroDivisors A) :
    symb (regularFractionUnit a) (regularFractionUnit (b * b')) =
      symb (regularFractionUnit a) (regularFractionUnit b) *
        symb (regularFractionUnit a) (regularFractionUnit b')
  /-- **(5), Stacks 0EAM.** `∂_A(b, b) = (-1)^m` with `m = length_A(A/bA)`. -/
  regular_self (b : nonZeroDivisors A) :
    symb (regularFractionUnit b) (regularFractionUnit b) = (-1) ^ (Ring.ord A (b : A)).toNat
  /-- **(6), Stacks 0EAN.** `∂_A(u, b) = u^m mod 𝔪` with `m = length_A(A/bA)`, for `u ∈ A` a
  unit. -/
  regular_unit_left (a b : nonZeroDivisors A) (u : Aˣ) (hu : (a : A) = u) :
    symb (regularFractionUnit a) (regularFractionUnit b) =
      Units.map (residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat
  /-- **(7), Stacks 0EAP.** `∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)` for `a`, `b`,
  `b - a` nonzerodivisors. -/
  regular_steinberg (a b c : nonZeroDivisors A) (hc : (c : A) = (b : A) - (a : A)) :
    symb (regularFractionUnit a) (regularFractionUnit c) *
        symb (regularFractionUnit b) (regularFractionUnit b) =
      symb (regularFractionUnit b) (regularFractionUnit c) *
        symb (regularFractionUnit a) (regularFractionUnit b)

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **`Stacks.Chow.tameSymbolValue` is the recipe Stacks 0EAQ.** On a pair of nonzerodivisors of
a one-dimensional Noetherian local ring, the function of a pair `Stacks.Chow.tameSymbolValue` is
the displayed product `Stacks.Chow.tameSymbolFormula` of Stacks 0EAQ: both are the formula on one
preparation of the pair, and Stacks 0EAR makes the choice irrelevant. -/
theorem tameSymbolValue_eq_tameSymbolFormula (hdim : ringKrullDim A = 1)
    (x y : nonZeroDivisors A) :
    tameSymbolValue x y = tameSymbolFormula hdim (x : A) (y : A)
      (isRegular_iff_mem_nonZeroDivisors.mpr x.2) (isRegular_iff_mem_nonZeroDivisors.mpr y.2) := by
  obtain ⟨E⟩ := nonempty_preparedTameSymbolExtension hdim
    (isRegular_iff_mem_nonZeroDivisors.mpr x.2) (isRegular_iff_mem_nonZeroDivisors.mpr y.2)
  let : Fintype (MaximalSpectrum E.extension) :=
    @Fintype.ofFinite _ E.preparation.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum E.extension,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := E.preparation.isLocalHom
  rw [tameSymbolFormula_eq_symbolValue hdim _ _ E.preparation]
  exact tameSymbolValue_eq_symbolValue hdim E.preparation 0 1 x y (by simp) (by simp)

/-- **The map `Stacks.Chow.formulaTameSymbol` is the recipe Stacks 0EAQ on nonzerodivisors.** -/
theorem formulaTameSymbol_regularFractionUnit_eq_tameSymbolFormula (hdim : ringKrullDim A = 1)
    (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q] (x y : nonZeroDivisors A) :
    formulaTameSymbol hdim Q (regularFractionUnit x) (regularFractionUnit y) =
      tameSymbolFormula hdim (x : A) (y : A)
        (isRegular_iff_mem_nonZeroDivisors.mpr x.2)
        (isRegular_iff_mem_nonZeroDivisors.mpr y.2) := by
  rw [formulaTameSymbol_regularFractionUnit, tameSymbolValue_eq_tameSymbolFormula]

/-- **Stacks 0EAH.** Let `(A, 𝔪)` be a Noetherian local ring of dimension one with total ring of
fractions `Q`. The tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` defined by the recipe Stacks
0EAQ — on a pair of nonzerodivisors `a₁, a₂` of `A` it is the displayed product
`Stacks.Chow.tameSymbolFormula` computed from a finite extension with local factorizations as in
Stacks 0EAG, and on `Q(A)^*` it is given by the fraction formula
`∂_A(a/b, c/d) = ∂_A(a, c) ∂_A(a, d)^{-1} ∂_A(b, c)^{-1} ∂_A(b, d)` — satisfies all seven
properties (1)–(7) of the section (`Stacks.Chow.IsTameSymbol`).

The map is `Stacks.Chow.formulaTameSymbol`; the second clause identifies it on nonzerodivisors
with the recipe `Stacks.Chow.tameSymbolFormula`, which does not depend on the choices by
`Stacks.Chow.tameSymbolFormula_eq` (Stacks 0EAR). As in the source, no uniqueness is claimed. -/
@[stacks 0EAH "the tame symbol defined by the recipe 0EAQ (formulaTameSymbol, equal on \
nonzerodivisors to tameSymbolFormula) satisfies properties (1)-(7), for every one-dimensional \
Noetherian local ring with its total ring of fractions"]
theorem formulaTameSymbol_isTameSymbol (hdim : ringKrullDim A = 1) (Q : Type v) [CommRing Q]
    [Algebra A Q] [IsFractionRing A Q] :
    IsTameSymbol A Q (formulaTameSymbol hdim Q) ∧
      ∀ x y : nonZeroDivisors A,
        formulaTameSymbol hdim Q (regularFractionUnit x) (regularFractionUnit y) =
          tameSymbolFormula hdim (x : A) (y : A)
            (isRegular_iff_mem_nonZeroDivisors.mpr x.2)
            (isRegular_iff_mem_nonZeroDivisors.mpr y.2) := by
  refine ⟨⟨(formulaTameSymbol hdim Q).map_mul_right, (formulaTameSymbol hdim Q).skew,
    fun f g hg => (formulaTameSymbol hdim Q).steinberg f g (by rw [hg]; ring),
    fun a a' b => ?_, fun a b b' => ?_, fun b => ?_, fun a b u hu => ?_,
    fun a b c hc => ?_⟩, formulaTameSymbol_regularFractionUnit_eq_tameSymbolFormula hdim Q⟩
  · simp only [formulaTameSymbol_regularFractionUnit]
    exact tameSymbolValue_mul_left hdim a a' b
  · simp only [formulaTameSymbol_regularFractionUnit]
    exact tameSymbolValue_mul_right hdim a b b'
  · rw [formulaTameSymbol_regularFractionUnit]
    exact tameSymbolValue_self hdim b
  · rw [formulaTameSymbol_regularFractionUnit]
    exact tameSymbolValue_unit_left hdim a b u hu
  · simp only [formulaTameSymbol_regularFractionUnit]
    exact tameSymbolValue_steinberg hdim a b c hc

end Stacks.Chow

end
