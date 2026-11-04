module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The tame symbol on nonzerodivisors

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `Q(A)` be its total ring of
fractions. Stacks 0EAH asks for a *tame symbol*

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

satisfying bimultiplicativity, skew-symmetry and the Steinberg relation. As the source observes,
it is easier to work with elements of `A`, and `∂_A` is therefore described first as a map on
pairs of nonzerodivisors of `A` satisfying the four properties Stacks 0EAL, 0EAM, 0EAN and 0EAP:

* `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)` and `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')`;
* `∂_A(b, b) = (-1)^m` with `m = length_A(A/bA)`;
* `∂_A(u, b) = u^m mod 𝔪` for `u ∈ A` a unit;
* `∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)`.

This file records that package of data as `Stacks.Chow.RegularTameSymbol` and derives from it the
two consequences the extension to `Q(A)^*` needs: the symbol is trivial when either argument is
`1`, and it is skew-symmetric. The latter is the one place where the length condition Stacks 0EAM
is used: `length_A(A/abA) = length_A(A/aA) + length_A(A/bA)`, which is Mathlib's `Ring.ord_mul`.

The nonzerodivisors of `A` are handled as the submonoid `nonZeroDivisors A` rather than as
elements with a side condition, so that the two multiplicativity properties are statements about
a monoid and `length_A(A/bA)` is literally Mathlib's `Ring.ord A b`.

## Main definitions

* `Stacks.Chow.regularFractionUnit` — a nonzerodivisor of `A`, as a unit of `Q(A)`.
* `Stacks.Chow.RegularTameSymbol` — the data of a tame symbol on pairs of nonzerodivisors of `A`.

## Main results

* `Stacks.Chow.mem_nonZeroDivisors_of_isUnit_algebraMap`,
  `Stacks.Chow.exists_regularFractionUnit_div`,
  `Stacks.Chow.regularFractionUnit_div_eq_iff` — `Q(A)^*` is the group of fractions of the monoid
  `nonZeroDivisors A`: every unit is a quotient of two nonzerodivisors of `A`, and two such
  quotients agree exactly when their cross products do.
* `Stacks.Chow.RegularTameSymbol.skew` — `∂_A(a, b) ∂_A(b, a) = 1`.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAS](https://stacks.math.columbia.edu/tag/0EAS)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.Chow

section Fractions

variable {A : Type u} [CommRing A] {Q : Type v} [CommRing Q] [Algebra A Q] [IsFractionRing A Q]

/-- A nonzerodivisor of `A`, as a unit of the total ring of fractions `Q(A)`. -/
noncomputable def regularFractionUnit : nonZeroDivisors A →* Qˣ where
  toFun a := (IsLocalization.map_units Q a).unit
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp)

/-- The unit `Stacks.Chow.regularFractionUnit a` of `Q(A)` is the image of `a` in `Q(A)`. -/
@[simp]
theorem regularFractionUnit_val (a : nonZeroDivisors A) :
    ((regularFractionUnit (Q := Q) a : Qˣ) : Q) = algebraMap A Q a := rfl

/-- Distinct nonzerodivisors of `A` give distinct units of `Q(A)`. -/
theorem regularFractionUnit_injective :
    Function.Injective (regularFractionUnit (A := A) (Q := Q)) := fun a b hab ↦
  Subtype.ext (IsFractionRing.injective A Q (by
    simpa only [regularFractionUnit_val] using congrArg Units.val hab))

/-- An element of `A` whose image in the total ring of fractions is a unit is a
nonzerodivisor. Together with `Stacks.Chow.regularFractionUnit` this says that `Q(A)^*` is the
group of fractions of the monoid `nonZeroDivisors A`. -/
theorem mem_nonZeroDivisors_of_isUnit_algebraMap {a : A} (h : IsUnit (algebraMap A Q a)) :
    a ∈ nonZeroDivisors A := by
  have key : ∀ x : A, x * a = 0 → x = 0 := fun x hx ↦
    IsFractionRing.injective A Q (by
      rw [map_zero]
      refine h.mul_left_eq_zero.mp ?_
      rw [← map_mul, hx, map_zero])
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ key x (by rw [mul_comm]; exact hx), key⟩

/-- Every unit of the total ring of fractions is a quotient of two nonzerodivisors of `A`. -/
theorem exists_regularFractionUnit_div (f : Qˣ) :
    ∃ a b : nonZeroDivisors A,
      f = regularFractionUnit a * (regularFractionUnit (Q := Q) b)⁻¹ := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) (f : Q)
  replace hab : IsLocalization.mk' Q a b = (f : Q) := hab
  have key : (f * regularFractionUnit (Q := Q) b : Q) = algebraMap A Q a := by
    rw [regularFractionUnit_val, ← hab, IsLocalization.mk'_spec]
  have ha : a ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_of_isUnit_algebraMap (Q := Q) ?_
    rw [← key]
    exact (f * regularFractionUnit b).isUnit
  refine ⟨⟨a, ha⟩, b, eq_mul_inv_iff_mul_eq.mpr (Units.ext ?_)⟩
  rw [regularFractionUnit_val]
  exact key

/-- Two quotients of nonzerodivisors are equal in `Q(A)` exactly when the cross products agree
in `A`. -/
theorem regularFractionUnit_div_eq_iff {a b a' b' : nonZeroDivisors A} :
    regularFractionUnit (Q := Q) a * (regularFractionUnit b)⁻¹ =
        regularFractionUnit a' * (regularFractionUnit b')⁻¹ ↔ a * b' = a' * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, ← map_mul, ← map_mul]
  exact ⟨fun h ↦ regularFractionUnit_injective (Q := Q) h, fun h ↦ congrArg _ h⟩

end Fractions

/-- **Stacks 0EAH, the data of a tame symbol on nonzerodivisors.** A tame symbol on a
one-dimensional Noetherian local ring `A` is described in Stacks 0EAH by its restriction to pairs
of nonzerodivisors of `A`, which is required to satisfy the four conditions Stacks 0EAL, 0EAM,
0EAN and 0EAP. A term of this type is exactly that restriction together with those conditions.

The source gives a recipe producing such a datum (Stacks 0EAQ, well defined by Stacks 0EAR and
satisfying these conditions by Stacks 0EAS); it does not claim that the datum is unique, which is
why it is carried as data here. `Stacks.Chow.RegularTameSymbol.extend` turns a term of this type
into the tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of the source. -/
structure RegularTameSymbol (A : Type u) [CommRing A] [IsLocalRing A] where
  /-- The symbol `∂_A(a, b)` on a pair of nonzerodivisors of `A`. -/
  toFun : nonZeroDivisors A → nonZeroDivisors A → (ResidueField A)ˣ
  /-- **Stacks 0EAL.** `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)`. -/
  map_mul_left (a a' b : nonZeroDivisors A) : toFun (a * a') b = toFun a b * toFun a' b
  /-- **Stacks 0EAL.** `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')`. -/
  map_mul_right (a b b' : nonZeroDivisors A) : toFun a (b * b') = toFun a b * toFun a b'
  /-- **Stacks 0EAM.** `∂_A(b, b) = (-1)^m` with `m = length_A(A/bA)`. -/
  self (b : nonZeroDivisors A) : toFun b b = (-1) ^ (Ring.ord A (b : A)).toNat
  /-- **Stacks 0EAN.** `∂_A(u, b) = u^m mod 𝔪` with `m = length_A(A/bA)`, for `u ∈ A` a unit. -/
  unit_left (a b : nonZeroDivisors A) (u : Aˣ) (hu : (a : A) = u) :
    toFun a b = Units.map (residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat
  /-- **Stacks 0EAP.** `∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)`. -/
  steinberg (a b c : nonZeroDivisors A) (hc : (c : A) = (b : A) - (a : A)) :
    toFun a c * toFun b b = toFun b c * toFun a b

namespace RegularTameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] (symb : RegularTameSymbol A)

/-- A tame symbol on nonzerodivisors is applied to a pair `(a, b)` as `symb a b`. -/
instance : CoeFun (RegularTameSymbol A)
    fun _ ↦ nonZeroDivisors A → nonZeroDivisors A → (ResidueField A)ˣ :=
  ⟨RegularTameSymbol.toFun⟩

/-- The symbol is trivial when its first argument is `1`. -/
@[simp]
theorem one_left (b : nonZeroDivisors A) : symb 1 b = 1 :=
  right_eq_mul.mp (by simpa only [one_mul] using symb.map_mul_left 1 1 b)

/-- The symbol is trivial when its second argument is `1`. -/
@[simp]
theorem one_right (a : nonZeroDivisors A) : symb a 1 = 1 :=
  right_eq_mul.mp (by simpa only [one_mul] using symb.map_mul_right a 1 1)

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- **Stacks 0EAJ on nonzerodivisors.** `∂_A(a, b) ∂_A(b, a) = 1`.

This is where the length condition Stacks 0EAM enters: expanding `∂_A(ab, ab)` by
bimultiplicativity gives `∂_A(a, a) ∂_A(a, b) ∂_A(b, a) ∂_A(b, b)`, while Stacks 0EAM evaluates
all three diagonal terms, and `length_A(A/abA) = length_A(A/aA) + length_A(A/bA)`. -/
theorem skew (a b : nonZeroDivisors A) : symb a b * symb b a = 1 := by
  have hord : (Ring.ord A ((a * b : nonZeroDivisors A) : A)).toNat =
      (Ring.ord A (a : A)).toNat + (Ring.ord A (b : A)).toNat := by
    rw [show (((a * b : nonZeroDivisors A) : A)) = (a : A) * (b : A) from rfl,
      Ring.ord_mul A b.2]
    exact ENat.toNat_add (Ring.ord_ne_top a.2) (Ring.ord_ne_top b.2)
  have hdiag : symb (a * b) (a * b) = symb a a * symb b b := by
    rw [symb.self, symb.self, symb.self, hord, pow_add]
  rw [symb.map_mul_left, symb.map_mul_right, symb.map_mul_right] at hdiag
  have hperm : symb a a * symb b b * (symb a b * symb b a) =
      symb a a * symb a b * (symb b a * symb b b) := by
    simp only [mul_assoc, mul_comm, mul_left_comm]
  refine mul_left_cancel (a := symb a a * symb b b) ?_
  rw [mul_one, hperm, hdiag]

/-- **Stacks 0EAJ on nonzerodivisors**, in the form `∂_A(b, a) = ∂_A(a, b)⁻¹`. -/
theorem symm_eq_inv (a b : nonZeroDivisors A) : symb b a = (symb a b)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact symb.skew a b)

end RegularTameSymbol

end Stacks.Chow

end
