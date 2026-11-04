module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Recognising a localization of a subalgebra inside a localization of the ambient ring

Let `B → Bf` be the localization of `B` away from the image of an element `r` of a base ring `A`,
let `C` be a subalgebra of `B`, and let `D` be a `C`-algebra embedded in `Bf` compatibly. If
every element of `D` is a fraction whose numerator comes from `C`, then `D` is the localization
of `C` away from `r`.

Nothing else is required. The equality condition of the localization is inherited from `B → Bf`
because `C` sits inside `B` and `D` sits inside `Bf`, and the unit condition is the single
hypothesis that `r` becomes a unit in `D`.

## Main definitions

None.

## Main results

* `IsLocalization.Away.of_subalgebra`.

## Implementation notes

`D` is an arbitrary ring with an injection into `Bf`, not a subalgebra of `Bf`. In the intended
use `D` is a subalgebra of `Bf` over a localization of `A`, and asking for a subalgebra over `A`
instead would force a `Subalgebra.restrictScalars` into the statement, which changes the carrier
type only up to unfolding and so does not match the algebra instances a caller has.

The algebra structure of `D` over `C` and the fact that `r` becomes a unit in `D` are both
parameters rather than constructions. A caller has them for its own reasons -- usually from the
inclusion it is separately proving -- and deriving them here would need `D` to see more of `Bf`
than the statement gives it.
-/

@[expose] public section

universe u

namespace IsLocalization

variable {A B Bf : Type u} [CommRing A] [CommRing B] [CommRing Bf]
  [Algebra A B] [Algebra B Bf] [Algebra A Bf] [IsScalarTower A B Bf]

/-- A ring embedded in a localization of `B`, whose elements are exactly the fractions with
numerator in a subalgebra `C` of `B`, is the localization of `C` away from `r`. -/
theorem Away.of_subalgebra (r : A) [IsLocalization.Away (algebraMap A B r) Bf]
    (C : Subalgebra A B) (D : Type u) [CommRing D] [Algebra C D]
    (i : D →+* Bf) (hi : Function.Injective i)
    (hmap : ∀ c : C, i (algebraMap C D c) = algebraMap B Bf (c : B))
    (hunit : IsUnit (algebraMap C D (algebraMap A C r)))
    (hsurj : ∀ d : D, ∃ (n : ℕ) (c : C),
      i d * algebraMap A Bf r ^ n = algebraMap B Bf (c : B)) :
    IsLocalization.Away (algebraMap A C r) D := by
  have hrC : ((algebraMap A C r : C) : B) = algebraMap A B r := rfl
  have hir : i (algebraMap C D (algebraMap A C r)) = algebraMap A Bf r := by
    rw [hmap, hrC, ← IsScalarTower.algebraMap_apply]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨-, n, rfl⟩
    rw [map_pow]
    exact hunit.pow n
  · intro z
    obtain ⟨n, c, hc⟩ := hsurj z
    refine ⟨⟨c, ⟨algebraMap A C r ^ n, n, rfl⟩⟩, hi ?_⟩
    rw [map_mul, map_pow, map_pow, hir, hc, hmap]
  · intro x y hxy
    have hB : algebraMap B Bf (x : B) = algebraMap B Bf (y : B) := by
      rw [← hmap, ← hmap, hxy]
    obtain ⟨m, hm⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap A B r)) Bf).mp hB
    obtain ⟨n, hn⟩ := m.2
    have hn' : algebraMap A B r ^ n = (m : B) := hn
    refine ⟨⟨algebraMap A C r ^ n, n, rfl⟩, Subtype.ext ?_⟩
    push_cast
    rw [hn']
    exact hm

end IsLocalization

end
