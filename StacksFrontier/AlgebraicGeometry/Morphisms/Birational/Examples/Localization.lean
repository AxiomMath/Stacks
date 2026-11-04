module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Localization gives a birational morphism that is nowhere an isomorphism

If `A` is a domain and `S` a multiplicative subset avoiding zero, then
`Spec (S⁻¹A) ⟶ Spec A` is birational: both spectra are irreducible with generic point the zero
ideal, and the local rings there are both `Frac A`.

Birational does not mean isomorphic over an open. If the morphism were an isomorphism over a
nonempty open, every element of `S` would already be invertible on some nonempty principal
open `D(a)`. Localizing `ℤ` at the odd integers makes that impossible: a prime larger than
`|a|` would have to be invertible in `ℤ_a`.

## Main definitions

* `AlgebraicGeometry.oddIntegers` is the multiplicative submonoid of odd integers.

## Main results

* `AlgebraicGeometry.localization_isBirational`: the localization morphism on spectra is
  birational.
* `AlgebraicGeometry.exists_nonzero_away_isUnit_of_isIso_restrict`: a nonempty open isomorphism
  locus forces all denominators to become units on a nonempty principal open.
* `AlgebraicGeometry.localization_not_isIso_restrict_nonempty`: for `ℤ` localized at the odd
  integers, no nonempty open of the target is an isomorphism locus.

## Implementation notes

The localization is `Localization S` and the principal localization `Localization.Away a`. The
morphism over an open is the canonical restriction of the spectrum map.

## References

* [Stacks Project, Tag 01RQ](https://stacks.math.columbia.edu/tag/01RQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The localization morphism of spectra is birational: both spectra are irreducible with generic
point the zero ideal, and the local rings there agree. -/
@[stacks 01RQ "localization_birational"]
theorem localization_isBirational (A : Type u) [CommRing A] [IsDomain A]
    (S : Submonoid A) (hS : (0 : A) ∉ S) :
    IsBirational
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (Localization S))).op) := by
  have hM : S ≤ nonZeroDivisors A := fun s hs =>
    mem_nonZeroDivisors_iff_ne_zero.mpr (fun hz => hS (hz ▸ hs))
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hM
  let f : Spec (.of (Localization S)) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (Localization S))).op
  show Set.BijOn f (genericPoints _) (genericPoints _) ∧ _
  refine ⟨?_, fun x _ => isIso_SpecMap_stakMap_localization (CommRingCat.of A) S x⟩
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
  apply Set.bijOn_singleton.mpr
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  show PrimeSpectrum.comap (algebraMap A (Localization S)) ⊥ = ⊥
  ext a
  show (algebraMap A (Localization S)) a = 0 ↔ a = 0
  exact ⟨fun ha => IsLocalization.injective (Localization S) hM (by simpa using ha),
    fun ha => by simp [ha]⟩

/-- If the localization morphism is an isomorphism over a nonempty open, then every denominator
already becomes a unit on some nonempty principal open. -/
@[stacks 01RQ "localization_open_criterion"]
theorem exists_nonzero_away_isUnit_of_isIso_restrict
    (A : Type u) [CommRing A] [IsDomain A]
    (S : Submonoid A) (_hS : (0 : A) ∉ S)
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : Set.Nonempty (U : Set (Spec (CommRingCat.of A))))
    (hiso : IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (Localization S))).op) ∣_ U)) :
    ∃ a : A, a ≠ 0 ∧ ∀ s : S, IsUnit (algebraMap A (Localization.Away a) s.1) := by
  let Y : Scheme := Spec (CommRingCat.of A)
  obtain ⟨x, hx⟩ := hU
  obtain ⟨W, hW, hxW, hWU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  rcases hW with ⟨V, hV, rfl⟩
  rcases hV with ⟨a, rfl⟩
  let g : Localization.Away a →+* Localization.Away (algebraMap A (Localization S) a) :=
    Localization.awayMap (algebraMap A (Localization S)) a
  have hxa : a ∉ x.asIdeal := (PrimeSpectrum.mem_basicOpen a x).mp hxW
  have hax : a ≠ 0 := by
    rintro rfl
    exact hxa (by simp)
  let f : Spec (CommRingCat.of (Localization S)) ⟶ Y :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (Localization S))).op
  let V : Y.Opens := PrimeSpectrum.basicOpen a
  let V' : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have himage : U.ι ''ᵁ V' = V := by
    ext p
    refine ⟨?_, fun hp => ⟨⟨p, hWU hp⟩, hp, rfl⟩⟩
    rintro ⟨q, hq, rfl⟩
    exact hq
  have hV_iso : IsIso (f ∣_ V) := by
    have : IsIso (f ∣_ U) := hiso
    exact (MorphismProperty.arrow_mk_iso_iff
      (CategoryTheory.MorphismProperty.isomorphisms Scheme)
      (morphismRestrictRestrict f U V' ≪≫ morphismRestrictEq f himage)).mp (by infer_instance)
  have hSpec : IsIso (Scheme.Spec.map (CommRingCat.ofHom g).op) :=
    (MorphismProperty.arrow_mk_iso_iff
      (CategoryTheory.MorphismProperty.isomorphisms Scheme)
      (SpecMapRestrictBasicOpenIso
        (CommRingCat.ofHom (algebraMap A (Localization S))) a)).mp hV_iso
  let e : Localization.Away a ≃+* Localization.Away (algebraMap A (Localization S) a) :=
    RingEquiv.ofBijective g (isIso_SpecMap_iff.mp hSpec)
  refine ⟨a, hax, fun s => ?_⟩
  apply (isUnit_map_iff e _).mp
  have hs : IsUnit (algebraMap (Localization S)
      (Localization.Away (algebraMap A (Localization S) a))
      (algebraMap A (Localization S) s.1)) :=
    RingHom.isUnit_map _ (IsLocalization.map_units (Localization S) s)
  show IsUnit (g (algebraMap A (Localization.Away a) s.1))
  simpa [g, Localization.awayMap, IsLocalization.Away.map] using hs

/-- The multiplicative submonoid of odd integers. -/
@[stacks 01RQ "integer_counterexample"]
def oddIntegers : Submonoid ℤ where
  carrier := {n | Odd n}
  one_mem' := odd_one
  mul_mem' := fun ha hb => ha.mul hb

/-- The localization of `ℤ` at all odd integers is not an isomorphism over any
nonempty open of its target. -/
@[stacks 01RQ "integer_counterexample"]
theorem localization_not_isIso_restrict_nonempty
    (U : (Scheme.Spec.obj (Opposite.op (CommRingCat.of ℤ))).Opens) (hU : U ≠ ⊥) :
    ¬ IsIso
      ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap ℤ (Localization oddIntegers))).op) ∣_ U) := by
  intro hIso
  obtain ⟨a, ha, hunit⟩ :=
    exists_nonzero_away_isUnit_of_isIso_restrict
      ℤ oddIntegers (by simp [oddIntegers]) U (U.ne_bot_iff_nonempty.mp hU) hIso
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (a.natAbs + 3)
  obtain ⟨n, hdiv⟩ : ∃ n : ℕ, (p : ℤ) ∣ a ^ n := by
    simpa [Submonoid.mem_powers_iff] using
      (IsLocalization.algebraMap_isUnit_iff (M := Submonoid.powers a)).mp
        (hunit ⟨(p : ℤ), (hp.odd_iff.mpr (by omega)).natCast⟩)
  have hpa : p ∣ a.natAbs := hp.dvd_of_dvd_pow (by
    simpa only [Int.natAbs_pow] using (Int.natCast_dvd).mp hdiv)
  have : p ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hpa
  omega

end AlgebraicGeometry
