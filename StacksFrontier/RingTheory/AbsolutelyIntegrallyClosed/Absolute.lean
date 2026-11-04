module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed

/-!
# The absolute integral closure of a domain

The *absolute integral closure* `A⁺` of an integral domain `A` is the integral closure of `A`
inside a fixed algebraic closure of its fraction field. This file constructs it, proves its
elementary properties, and defines the predicate of being an absolute integral closure, which is
stable under integral extensions of the base and under localization.

## Main definitions

* `IsAbsoluteIntegralClosure A B`: `B` is an absolute integral closure of the domain `A`, that is
  `B` is a domain extension of `A` which is integral over `A` and absolutely integrally closed.
* `absoluteIntegralClosure A`: the integral closure of `A` in `AlgebraicClosure (FractionRing A)`,
  a concrete absolute integral closure of `A`.

## Main results

* `IsAbsolutelyIntegrallyClosed.isIntegrallyClosedIn`: an absolutely integrally closed ring is
  integrally closed in every domain extension of it.
* `isAbsoluteIntegralClosure_absoluteIntegralClosure`: `absoluteIntegralClosure A` is an absolute
  integral closure of `A`; `exists_isAbsoluteIntegralClosure` is the resulting existence
  statement.
* `IsAbsoluteIntegralClosure.isAlgClosed_fractionRing` and
  `IsAbsoluteIntegralClosure.isAlgebraic_fractionRing`: the fraction field of an absolute integral
  closure of `A` is an algebraic closure of the fraction field of `A`.
* `IsAbsoluteIntegralClosure.trans`: an absolute integral closure of an integral extension `A'` of
  `A` is an absolute integral closure of `A`.
* `IsAbsoluteIntegralClosure.localization`: localizing an absolute integral closure of `A` at the
  image of a submonoid of nonzerodivisors of `A` gives an absolute integral closure of the
  corresponding localization of `A`.
* `IsAbsoluteIntegralClosure.isStrictlyHenselian_atPrime`: a local ring of an absolute integral
  closure is strictly henselian (Stacks 0DCS).

## Implementation notes

The predicate `IsAbsoluteIntegralClosure` mentions neither a fraction field nor an algebraic
closure: it asks only that `B` be an absolutely integrally closed domain which is an integral
extension of `A`. The usual description is recovered by `isAlgClosed_fractionRing` and
`isAlgebraic_fractionRing`.

## References

* [Stacks: Tag 0DCK](https://stacks.math.columbia.edu/tag/0DCK)
-/

@[expose] public section

open Polynomial

open scoped nonZeroDivisors

universe u

section AbsolutelyIntegrallyClosed

variable {B : Type*} [CommRing B]

/-- An absolutely integrally closed ring is integrally closed in every extension of it which is
a domain. -/
theorem IsAbsolutelyIntegrallyClosed.isIntegrallyClosedIn
    (hB : IsAbsolutelyIntegrallyClosed B) (K : Type*) [CommRing K] [IsDomain K] [Algebra B K]
    (hinj : Function.Injective (algebraMap B K)) : IsIntegrallyClosedIn B K := by
  refine isIntegrallyClosedIn_iff.mpr ⟨hinj, ?_⟩
  intro x hx
  obtain ⟨f, hf, hroot⟩ := hx
  obtain ⟨s, hs⟩ := hB f hf
  rw [hs, eval₂_multiset_prod, Multiset.map_map] at hroot
  obtain ⟨b, hb_mem, hb_zero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hroot)
  have hx_eq : x - algebraMap B K b = 0 := by simpa using hb_zero
  exact ⟨b, (sub_eq_zero.mp hx_eq).symm⟩

/-- An absolutely integrally closed domain is integrally closed. -/
theorem IsAbsolutelyIntegrallyClosed.isIntegrallyClosed [IsDomain B]
    (hB : IsAbsolutelyIntegrallyClosed B) : IsIntegrallyClosed B :=
  hB.isIntegrallyClosedIn (FractionRing B) (IsFractionRing.injective B (FractionRing B))

/-- The fraction field of an absolutely integrally closed domain is algebraically closed. -/
theorem IsAbsolutelyIntegrallyClosed.isAlgClosed_fractionRing [IsDomain B]
    (hB : IsAbsolutelyIntegrallyClosed B) (K : Type*) [Field K] [Algebra B K]
    [IsFractionRing B K] : IsAlgClosed K :=
  have := hB.isIntegrallyClosed
  (isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing B K).mp hB

end AbsolutelyIntegrallyClosed

/-- `B` is an *absolute integral closure* of the domain `A` if it is a domain extension of `A`
which is integral over `A` and absolutely integrally closed. -/
structure IsAbsoluteIntegralClosure (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] : Prop where
  /-- An absolute integral closure is an extension: its structure map is injective. -/
  injective : Function.Injective (algebraMap A B)
  /-- An absolute integral closure is integral over the base. -/
  isIntegral : Algebra.IsIntegral A B
  /-- An absolute integral closure is absolutely integrally closed. -/
  isAbsolutelyIntegrallyClosed : IsAbsolutelyIntegrallyClosed B

namespace IsAbsoluteIntegralClosure

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]

/-- Every element of an absolute integral closure of `A` is a root of a monic polynomial with
coefficients in `A`. -/
theorem exists_monic_aeval_eq_zero (h : IsAbsoluteIntegralClosure A B) (b : B) :
    ∃ f : A[X], f.Monic ∧ aeval b f = 0 :=
  h.isIntegral.isIntegral b

/-- Every monic polynomial of positive degree over an absolute integral closure has a root in
it. -/
theorem exists_isRoot (h : IsAbsoluteIntegralClosure A B) (f : B[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : ∃ b : B, f.IsRoot b :=
  (isAbsolutelyIntegrallyClosed_iff_exists_root B).mp h.isAbsolutelyIntegrallyClosed f hf hdeg

/-- An absolute integral closure is integrally closed. -/
theorem isIntegrallyClosed (h : IsAbsoluteIntegralClosure A B) : IsIntegrallyClosed B :=
  h.isAbsolutelyIntegrallyClosed.isIntegrallyClosed

/-- The fraction field of an absolute integral closure is algebraically closed. -/
theorem isAlgClosed_fractionRing (h : IsAbsoluteIntegralClosure A B) (L : Type*) [Field L]
    [Algebra B L] [IsFractionRing B L] : IsAlgClosed L :=
  h.isAbsolutelyIntegrallyClosed.isAlgClosed_fractionRing L

/-- The fraction field of an absolute integral closure of `A` is algebraic over the fraction
field of `A`. -/
theorem isAlgebraic_fractionRing (h : IsAbsoluteIntegralClosure A B) (K L : Type*) [Field K]
    [CommRing L] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Algebra.IsAlgebraic K L :=
  have := h.isIntegral
  isAlgebraic_of_isFractionRing A B K L

/-- An absolute integral closure of `A` is the integral closure of `A` in its own fraction
field. -/
theorem isIntegralClosure (h : IsAbsoluteIntegralClosure A B) (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L] : IsIntegralClosure B A L where
  algebraMap_injective := IsFractionRing.injective B L
  isIntegral_iff := by
    have hclosed : IsIntegrallyClosedIn B L :=
      h.isAbsolutelyIntegrallyClosed.isIntegrallyClosedIn L (IsFractionRing.injective B L)
    refine fun {x} => ⟨fun hx => ?_, fun ⟨y, hy⟩ => ?_⟩
    · exact (isIntegrallyClosedIn_iff.mp hclosed).2 hx.tower_top
    · have := h.isIntegral
      rw [← hy]
      exact (Algebra.IsIntegral.isIntegral y).algebraMap

/-- An absolute integral closure of an integral extension `A'` of `A` is an absolute integral
closure of `A`. -/
theorem trans {A' : Type*} [CommRing A'] [IsDomain A'] [Algebra A A'] [Algebra A' B]
    [IsScalarTower A A' B] (h : IsAbsoluteIntegralClosure A' B)
    (hinj : Function.Injective (algebraMap A A')) (hint : Algebra.IsIntegral A A') :
    IsAbsoluteIntegralClosure A B where
  injective := by
    rw [IsScalarTower.algebraMap_eq A A' B]
    exact h.injective.comp hinj
  isIntegral :=
    have := h.isIntegral
    Algebra.IsIntegral.trans A'
  isAbsolutelyIntegrallyClosed := h.isAbsolutelyIntegrallyClosed

/-- Localizing an absolute integral closure `B` of `A` at the image of a submonoid `S` of
nonzerodivisors of `A` gives an absolute integral closure of the localization of `A` at `S`. -/
theorem localization (h : IsAbsoluteIntegralClosure A B) {S : Submonoid A} (hS : S ≤ A⁰)
    (Aₛ Bₛ : Type*) [CommRing Aₛ] [CommRing Bₛ] [Algebra A Aₛ] [Algebra B Bₛ]
    [IsLocalization S Aₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
    [Algebra Aₛ Bₛ] [Algebra A Bₛ] [IsScalarTower A Aₛ Bₛ] [IsScalarTower A B Bₛ]
    (hAₛ : IsDomain Aₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Aₛ hS)
    (hBₛ : IsDomain Bₛ := IsLocalization.isDomain_of_le_nonZeroDivisors
      (M := Algebra.algebraMapSubmonoid B S) Bₛ
      (map_le_nonZeroDivisors_of_injective (algebraMap A B) h.injective hS)) :
    IsAbsoluteIntegralClosure Aₛ Bₛ := by
  have hSB : Algebra.algebraMapSubmonoid B S ≤ B⁰ :=
    map_le_nonZeroDivisors_of_injective (algebraMap A B) h.injective hS
  have hinjB : Function.Injective (algebraMap B Bₛ) := IsLocalization.injective Bₛ hSB
  refine ⟨?_, ⟨?_⟩, isAbsolutelyIntegrallyClosed_localization B
    (Algebra.algebraMapSubmonoid B S) Bₛ h.isAbsolutelyIntegrallyClosed⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, hx'⟩ := IsLocalization.surj (M := S) x
    have ha : a = 0 := h.injective <| hinjB <| by
      rw [map_zero, map_zero, ← IsScalarTower.algebraMap_apply A B Bₛ,
        IsScalarTower.algebraMap_apply A Aₛ Bₛ, ← hx', map_mul, hx, zero_mul]
    rw [ha, map_zero] at hx'
    exact (IsLocalization.map_units Aₛ s).mul_left_eq_zero.mp hx'
  · intro x
    obtain ⟨⟨b, t⟩, hx'⟩ := IsLocalization.surj (M := Algebra.algebraMapSubmonoid B S) x
    obtain ⟨s, hs, hst⟩ := Submonoid.mem_map.mp t.2
    obtain ⟨w, hw⟩ := (IsLocalization.map_units Aₛ ⟨s, hs⟩).exists_right_inv
    have ht : algebraMap B Bₛ (t : B) = algebraMap Aₛ Bₛ (algebraMap A Aₛ s) := by
      rw [← hst, ← IsScalarTower.algebraMap_apply A B Bₛ,
        IsScalarTower.algebraMap_apply A Aₛ Bₛ]
    have hb : IsIntegral Aₛ (algebraMap B Bₛ b) :=
      IsIntegral.tower_top (R := A) (h.isIntegral.isIntegral b).algebraMap
    have hxeq : x = algebraMap B Bₛ b * algebraMap Aₛ Bₛ w := by
      calc x = x * algebraMap Aₛ Bₛ (algebraMap A Aₛ s * w) := by
            rw [hw, map_one, mul_one]
        _ = x * algebraMap B Bₛ (t : B) * algebraMap Aₛ Bₛ w := by
            rw [map_mul, ht, mul_assoc]
        _ = algebraMap B Bₛ b * algebraMap Aₛ Bₛ w := by rw [hx']
    rw [hxeq]
    exact hb.mul isIntegral_algebraMap

/-- A local ring of an absolute integral closure is strictly henselian: it is a henselian local
ring and its residue field is separably closed. This is **Stacks 0DCS** for `B` absolutely
integrally closed. -/
theorem isStrictlyHenselian_atPrime (h : IsAbsoluteIntegralClosure A B) (C : Type*) [CommRing C]
    [Algebra B C] (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    (hC : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C q) :
    HenselianLocalRing C ∧ IsSepClosed (IsLocalRing.ResidueField C) :=
  h.isAbsolutelyIntegrallyClosed.isStrictlyHenselian_atPrime q hC

end IsAbsoluteIntegralClosure

/-- The *absolute integral closure* `A⁺` of an integral domain `A`: the integral closure of `A`
inside a fixed algebraic closure of its fraction field. -/
noncomputable def absoluteIntegralClosure (A : Type u) [CommRing A] [IsDomain A] :
    Subalgebra A (AlgebraicClosure (FractionRing A)) :=
  integralClosure A (AlgebraicClosure (FractionRing A))

namespace absoluteIntegralClosure

variable (A : Type u) [CommRing A] [IsDomain A]

/-- `A⁺` is integral over `A`. -/
instance isIntegral : Algebra.IsIntegral A (absoluteIntegralClosure A) :=
  inferInstanceAs (Algebra.IsIntegral A (integralClosure A (AlgebraicClosure (FractionRing A))))

/-- `A⁺` is the integral closure of `A` in the algebraic closure of the fraction field of `A`. -/
instance isIntegralClosure :
    IsIntegralClosure (absoluteIntegralClosure A) A (AlgebraicClosure (FractionRing A)) :=
  inferInstanceAs (IsIntegralClosure (integralClosure A (AlgebraicClosure (FractionRing A))) A
    (AlgebraicClosure (FractionRing A)))

/-- The algebraic closure of the fraction field of `A` is algebraic over `A`. -/
theorem isAlgebraic_algebraicClosure :
    Algebra.IsAlgebraic A (AlgebraicClosure (FractionRing A)) :=
  (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
    (C := AlgebraicClosure (FractionRing A))).mpr inferInstance

/-- The chosen algebraic closure of the fraction field of `A` is the fraction field of `A⁺`. -/
instance isFractionRing :
    IsFractionRing (absoluteIntegralClosure A) (AlgebraicClosure (FractionRing A)) :=
  have := isAlgebraic_algebraicClosure A
  IsIntegralClosure.isFractionRing_of_algebraic A (absoluteIntegralClosure A) fun x hx => by
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) (AlgebraicClosure (FractionRing A)),
      map_eq_zero] at hx
    exact IsFractionRing.to_map_eq_zero_iff.mp hx

/-- `A⁺` is integrally closed. -/
instance isIntegrallyClosed : IsIntegrallyClosed (absoluteIntegralClosure A) :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn (AlgebraicClosure (FractionRing A))).mpr
    (inferInstanceAs (IsIntegrallyClosedIn
      (integralClosure A (AlgebraicClosure (FractionRing A)))
      (AlgebraicClosure (FractionRing A))))

/-- The structure map `A → A⁺` is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap A (absoluteIntegralClosure A)) := by
  have hbig : Function.Injective (algebraMap A (AlgebraicClosure (FractionRing A))) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) (AlgebraicClosure (FractionRing A))]
    exact (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective.comp
      (IsFractionRing.injective A (FractionRing A))
  intro x y hxy
  refine hbig ?_
  rw [IsScalarTower.algebraMap_apply A (absoluteIntegralClosure A)
    (AlgebraicClosure (FractionRing A)), IsScalarTower.algebraMap_apply A
    (absoluteIntegralClosure A) (AlgebraicClosure (FractionRing A)), hxy]

/-- `A⁺` is absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed :
    IsAbsolutelyIntegrallyClosed (absoluteIntegralClosure A) :=
  (isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing (absoluteIntegralClosure A)
    (AlgebraicClosure (FractionRing A))).mpr inferInstance

/-- Every element of `A⁺` is a root of a monic polynomial with coefficients in `A`. -/
theorem exists_monic_aeval_eq_zero (b : absoluteIntegralClosure A) :
    ∃ f : A[X], f.Monic ∧ aeval b f = 0 :=
  Algebra.IsIntegral.isIntegral (R := A) b

/-- Every monic polynomial of positive degree over `A⁺` has a root in `A⁺`. -/
theorem exists_isRoot (f : (absoluteIntegralClosure A)[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : ∃ b : absoluteIntegralClosure A, f.IsRoot b :=
  (isAbsolutelyIntegrallyClosed_iff_exists_root _).mp (isAbsolutelyIntegrallyClosed A) f hf hdeg

end absoluteIntegralClosure

/-- `A⁺` is an absolute integral closure of `A`. -/
theorem isAbsoluteIntegralClosure_absoluteIntegralClosure (A : Type u) [CommRing A] [IsDomain A] :
    IsAbsoluteIntegralClosure A (absoluteIntegralClosure A) where
  injective := absoluteIntegralClosure.algebraMap_injective A
  isIntegral := absoluteIntegralClosure.isIntegral A
  isAbsolutelyIntegrallyClosed := absoluteIntegralClosure.isAbsolutelyIntegrallyClosed A

/-- Every integral domain has an absolute integral closure. -/
theorem exists_isAbsoluteIntegralClosure (A : Type u) [CommRing A] [IsDomain A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B),
      IsAbsoluteIntegralClosure A B :=
  ⟨absoluteIntegralClosure A, inferInstance, inferInstance, inferInstance,
    isAbsoluteIntegralClosure_absoluteIntegralClosure A⟩

end
