module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Localizations at a prime and away from an element

Stacks tag 02C5 lists four examples of localizations of a ring `A` and of an `A`-module `M`:

1. for a prime `𝔭 ⊂ A` and `S = A \ 𝔭`, the localizations `A_𝔭` and `M_𝔭`; in Mathlib these are
   `Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`;
2. for `f ∈ A` and `S = {1, f, f², ...}`, the localizations `A_f` and `M_f`; in Mathlib these are
   `Localization.Away f` and `LocalizedModule (Submonoid.powers f) M`. Moreover `A_f = 0` if and
   only if `f` is nilpotent, which is `IsLocalization.Away.subsingleton_iff_isNilpotent` below;
3. the total ring of fractions `Q(A)`, which is `FractionRing A`;
4. when `A` is a domain, `Q(A)` is the field of fractions of `A` (`FractionRing.field`).

The ring localizations of items 1–4 are registered next to their Mathlib definitions; this file
records the module localizations of items 1 and 2 and the characterization of `A_f = 0`.
-/

@[expose] public section

add_to_stacks 02C5 "Items 1 and 2: for an `A`-module `M`, the localization `M_𝔭` at a prime `𝔭`
is `LocalizedModule 𝔭.primeCompl M`, and the localization `M_f` with respect to `f ∈ A` is
`LocalizedModule (Submonoid.powers f) M`." LocalizedModule

namespace IsLocalization.Away

variable {R : Type*} [CommRing R] (f : R) (S : Type*) [CommRing S] [Algebra R S]

/-- A localization `R_f` of `R` away from `f` is the zero ring if and only if `f` is nilpotent
in `R`. -/
@[stacks 02C5 "Item 2: `A_f = 0` if and only if `f` is nilpotent in `A`, for every localization
`A_f` of `A` with respect to `f`."]
theorem subsingleton_iff_isNilpotent [IsLocalization.Away f S] :
    Subsingleton S ↔ IsNilpotent f := by
  constructor
  · intro h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S 1).1 (Subsingleton.elim _ _)
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact IsLocalization.subsingleton (M := Submonoid.powers f) ⟨n, hn⟩

end IsLocalization.Away

/-- The localization `Localization.Away f` is the zero ring if and only if `f` is nilpotent. -/
theorem Localization.Away.subsingleton_iff_isNilpotent {R : Type*} [CommRing R] (f : R) :
    Subsingleton (Localization.Away f) ↔ IsNilpotent f :=
  IsLocalization.Away.subsingleton_iff_isNilpotent f _
