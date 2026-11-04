module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Ideal.Over

/-!
# Localizing a pushout square along a surjection at a prime

Let `R → R'` be surjective and let `A' = R' ⊗_R A` be a pushout of `R`-algebras. For a prime `𝔮'`
of `A'`, write `𝔮`, `𝔭'` and `𝔭` for its contractions to `A`, `R'` and `R`. Then the square of
local rings `R_𝔭 → A_𝔮`, `R_𝔭 → R'_𝔭'`, `A_𝔮 → A'_𝔮'`, `R'_𝔭' → A'_𝔮'` is again a pushout:
`A'_𝔮' = R'_𝔭' ⊗_{R_𝔭} A_𝔮`. This is the ring-theoretic form of the fact that the local ring of a
closed fibre at a point is the local ring of the total space modulo the ideal of the base.

## Main results

* `IsLocalization.algebraMapSubmonoid_primeCompl_of_surjective`: along a surjection, a
  localization at a prime is the localization at the image of the complement of its contraction.
* `Algebra.IsPushout.algebraMap_surjective_of_surjective`: the base change of a surjective ring
  map is surjective.
* `Algebra.IsPushout.of_isLocalization_atPrime_of_surjective`: the localized square is a
  pushout.
-/

@[expose] public noncomputable section

open Algebra

/-- Along a surjective ring map `A → A'`, a localization of `A'` at a prime `𝔮'` is its
localization at the image of the complement of the contraction `𝔭` of `𝔮'`: that image is the
complement of `𝔮'`. -/
theorem IsLocalization.algebraMapSubmonoid_primeCompl_of_surjective {A A' A'q : Type*}
    [CommRing A] [CommRing A'] [CommRing A'q] [Algebra A A'] [Algebra A' A'q]
    (h : Function.Surjective (algebraMap A A')) (q' : Ideal A') [q'.IsPrime]
    [IsLocalization.AtPrime A'q q'] (p : Ideal A) [p.IsPrime] (hp : q'.under A = p) :
    IsLocalization (algebraMapSubmonoid A' p.primeCompl) A'q := by
  subst hp
  have hsub : algebraMapSubmonoid A' (q'.under A).primeCompl = q'.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := h x
    exact ⟨fun ⟨z, hz, hzy⟩ hmem => hz (show algebraMap A A' z ∈ q' by rwa [hzy]),
      fun hx => ⟨y, hx, rfl⟩⟩
  rw [hsub]
  infer_instance

namespace Algebra.IsPushout

variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R R'] [Algebra R A] [Algebra R A'] [Algebra R' A'] [Algebra A A']
  [IsScalarTower R R' A'] [IsScalarTower R A A'] [Algebra.IsPushout R R' A A']

include R' in
/-- The base change of a surjective ring map is surjective. -/
theorem algebraMap_surjective_of_surjective (h : Function.Surjective (algebraMap R R')) :
    Function.Surjective (algebraMap A A') := by
  intro x
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv R R' A A').surjective x
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r' a =>
    obtain ⟨r, rfl⟩ := h r'
    refine ⟨r • a, ?_⟩
    rw [Algebra.IsPushout.equiv_tmul, ← IsScalarTower.algebraMap_apply R R' A',
      IsScalarTower.algebraMap_apply R A A', ← map_mul, ← Algebra.smul_def]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

variable (q' : Ideal A') [q'.IsPrime]

/-- **Localizing a pushout along a surjection at a prime.** Let `R → R'` be surjective and let
`A'` be the pushout `R' ⊗_R A`. For a prime `𝔮'` of `A'`, let `R_𝔭`, `R'_𝔭'`, `A_𝔮`, `A'_𝔮'` be the
localizations at `𝔮'` and its contractions, with compatible structure maps. Then
`A'_𝔮' = R'_𝔭' ⊗_{R_𝔭} A_𝔮`.

The square `A → A'`, `A → A_𝔮`, `A' → A'_𝔮'` is a pushout because `A'_𝔮'` is the localization of
`A'` at the image of the complement of `𝔮` (the map `A → A'` being surjective), and likewise for
`R → R'`; pasting with the given square and cancelling the second gives the claim. -/
theorem of_isLocalization_atPrime_of_surjective (h : Function.Surjective (algebraMap R R'))
    (q' : Ideal A') [q'.IsPrime] (Rp R'p Aq A'q : Type*) [CommRing Rp] [CommRing R'p] [CommRing Aq]
    [CommRing A'q] [Algebra R Rp] [IsLocalization.AtPrime Rp ((q'.under A).under R)]
    [Algebra R' R'p] [IsLocalization.AtPrime R'p (q'.under R')]
    [Algebra A Aq] [IsLocalization.AtPrime Aq (q'.under A)]
    [Algebra A' A'q] [IsLocalization.AtPrime A'q q']
    [Algebra Rp Aq] [Algebra Rp R'p] [Algebra R'p A'q] [Algebra Aq A'q] [Algebra Rp A'q]
    [Algebra R Aq] [Algebra R R'p] [Algebra R A'q] [Algebra A A'q] [Algebra R' A'q]
    [IsScalarTower R A Aq] [IsScalarTower R Rp Aq] [IsScalarTower R R' R'p]
    [IsScalarTower R Rp R'p] [IsScalarTower A A' A'q] [IsScalarTower A Aq A'q]
    [IsScalarTower R' A' A'q] [IsScalarTower R' R'p A'q] [IsScalarTower R A' A'q]
    [IsScalarTower R Aq A'q] [IsScalarTower R R'p A'q] [IsScalarTower R R' A'q]
    [IsScalarTower Rp Aq A'q] [IsScalarTower Rp R'p A'q] :
    Algebra.IsPushout Rp Aq R'p A'q := by
  have : IsLocalization (algebraMapSubmonoid A' (q'.under A).primeCompl) A'q :=
    IsLocalization.algebraMapSubmonoid_primeCompl_of_surjective
      (algebraMap_surjective_of_surjective (R' := R') h) q' _ rfl
  have : IsLocalization (algebraMapSubmonoid R' ((q'.under A).under R).primeCompl) R'p :=
    IsLocalization.algebraMapSubmonoid_primeCompl_of_surjective h (q'.under R') _
      ((Ideal.under_under _).trans (Ideal.under_under _).symm)
  have : Algebra.IsPushout R A R' A' := (inferInstance : Algebra.IsPushout R R' A A').symm
  have h₂ : Algebra.IsPushout A Aq A' A'q :=
    (Algebra.isPushout_of_isLocalization (q'.under A).primeCompl Aq A' A'q).symm
  have h₃ : Algebra.IsPushout R Aq R' A'q :=
    (Algebra.IsPushout.comp_iff R A R' A' (T := Aq) (T' := A'q)).2 h₂
  have : Algebra.IsPushout R Rp R' R'p :=
    (Algebra.isPushout_of_isLocalization ((q'.under A).under R).primeCompl Rp R' R'p).symm
  exact (Algebra.IsPushout.comp_iff R Rp R' R'p (T := Aq) (T' := A'q)).1 h₃

end Algebra.IsPushout
