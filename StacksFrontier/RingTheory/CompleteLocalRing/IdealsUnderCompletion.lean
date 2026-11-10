module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nakayama
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recognising the maximal ideal of a Noetherian local ring

An ideal inside the maximal ideal of a Noetherian local ring is the maximal ideal exactly when
it generates the cotangent space, and exactly when its extension to the completion is the
maximal ideal there.

## Main results

* `IsLocalRing.eq_maximalIdeal_iff_sup_sq`: an ideal inside the maximal ideal is the maximal
  ideal exactly when it generates it modulo the square.
* `IsLocalRing.maximalIdeal_quotient_eq_map`: the maximal ideal of a quotient of a local ring
  is the image of the maximal ideal.
* `IsLocalRing.map_quotient_eq_maximalIdeal_iff`: an ideal of a Noetherian local ring `A`
  generates the maximal ideal of `A ⧸ Jh` exactly when, together with `Jh`, it generates the
  maximal ideal of `A` modulo its square.
* `AdicCompletion.ideal_map_algebraMap_injective`: extension of ideals along the completion map
  is injective.
* `AdicCompletion.ideal_map_eq_maximalIdeal_iff`: an ideal is the maximal ideal exactly when its
  extension to the completion is the maximal ideal there.
* `IsLocalRing.map_atPrime_eq_maximalIdeal_iff`: an ideal generates the maximal ideal of the
  localization at a maximal ideal exactly when it generates that maximal ideal modulo its
  square.
* `IsLocalRing.quotientPowEquivAtPrime`: the quotient by a power of a maximal ideal does not
  change under localization at that ideal.

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsLocalRing

/-- An ideal contains its square-sum with itself: `p ⊔ p ^ 2 = p`. -/
private theorem sup_pow_two_eq_self {R : Type u} [CommRing R] (p : Ideal R) : p ⊔ p ^ 2 = p :=
  sup_eq_left.2 (Ideal.pow_le_self (by norm_num))

/-- An ideal inside the maximal ideal of a Noetherian local ring is the maximal ideal exactly
when it generates the maximal ideal modulo its square. -/
theorem eq_maximalIdeal_iff_sup_sq {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    I = maximalIdeal R ↔ I ⊔ maximalIdeal R ^ 2 = maximalIdeal R := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, sup_pow_two_eq_self]
  · refine le_antisymm hI (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
      (IsNoetherian.noetherian (maximalIdeal R)) ?_ ?_)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [smul_eq_mul, ← sq, h]

/-- The maximal ideal of a proper quotient of a local ring is the image of the maximal ideal. -/
theorem maximalIdeal_quotient_eq_map {A : Type u} [CommRing A] [IsLocalRing A] {Jh : Ideal A}
    (hJ : Jh ≠ ⊤) :
    letI : Nontrivial (A ⧸ Jh) := Ideal.Quotient.nontrivial_iff.mpr hJ
    letI : IsLocalRing (A ⧸ Jh) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk Jh) Ideal.Quotient.mk_surjective
    (maximalIdeal A).map (Ideal.Quotient.mk Jh) = maximalIdeal (A ⧸ Jh) := by
  have : Nontrivial (A ⧸ Jh) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (A ⧸ Jh) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jh) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk Jh) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk Jh) Ideal.Quotient.mk_surjective
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [sup_eq_left.mpr (le_maximalIdeal hJ)]

/-- An ideal inside the maximal ideal of a Noetherian local ring `A` generates the maximal ideal
of the quotient `A ⧸ Jh` exactly when, together with `Jh`, it generates the maximal ideal of `A`
modulo its square. -/
theorem map_quotient_eq_maximalIdeal_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {Jh N : Ideal A} (hJ : Jh ≤ maximalIdeal A) (hN : N ≤ maximalIdeal A) :
    letI : Nontrivial (A ⧸ Jh) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hJ)
    letI : IsLocalRing (A ⧸ Jh) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk Jh) Ideal.Quotient.mk_surjective
    (N.map (Ideal.Quotient.mk Jh) = maximalIdeal (A ⧸ Jh) ↔
      N ⊔ Jh ⊔ maximalIdeal A ^ 2 = maximalIdeal A) := by
  have hJtop : Jh ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hJ
  have : Nontrivial (A ⧸ Jh) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ Jh) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jh) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (A ⧸ Jh) :=
    isNoetherianRing_of_surjective A (A ⧸ Jh) (Ideal.Quotient.mk Jh)
      Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal A).map (Ideal.Quotient.mk Jh) = maximalIdeal (A ⧸ Jh) :=
    maximalIdeal_quotient_eq_map hJtop
  have hcomap : ∀ I : Ideal A,
      (I.map (Ideal.Quotient.mk Jh)).comap (Ideal.Quotient.mk Jh) = I ⊔ Jh := fun I => by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := congrArg (Ideal.comap (Ideal.Quotient.mk Jh)) h
    rw [hcomap, ← hmax, hcomap] at h1
    rw [h1, sup_eq_left.2 hJ, sup_pow_two_eq_self]
  · have h2 := congrArg (Ideal.map (Ideal.Quotient.mk Jh)) h
    rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_pow,
      hmax] at h2
    exact (IsLocalRing.eq_maximalIdeal_iff_sup_sq (hmax ▸ Ideal.map_mono hN)).2 h2

/-- A maximal ideal has inverses modulo itself: for `s ∉ p` there is a `t` with `t * s - 1 ∈ p`. -/
private theorem exists_mul_sub_one_mem {A : Type u} [CommRing A] {p : Ideal A} [p.IsMaximal]
    {s : A} (hs : s ∉ p) : ∃ t : A, t * s - 1 ∈ p := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  have hne : Ideal.Quotient.mk p s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk p s)⁻¹
  exact ⟨t, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one,
    inv_mul_cancel₀ hne, sub_self]⟩

/-- If `t * s - 1` times `a` and `s * a` both lie in an ideal `M`, then so does `a`. -/
private theorem mem_of_mul_mem_of_mul_sub_one_mul_mem {A : Type u} [CommRing A] {M : Ideal A}
    {a s t : A} (hsa : s * a ∈ M) (h : (t * s - 1) * a ∈ M) : a ∈ M := by
  rw [show a = t * (s * a) - (t * s - 1) * a by ring]
  exact M.sub_mem (M.mul_mem_left _ hsa) h

/-- An ideal containing the square of a maximal ideal `p` is saturated at `p` on elements of `p`:
if `s ∉ p`, `a ∈ p` and `s * a ∈ M`, then `a ∈ M`. -/
theorem mem_of_mul_mem_of_sq_le {A : Type u} [CommRing A] {p : Ideal A} [p.IsMaximal]
    {M : Ideal A} (h2 : p ^ 2 ≤ M) {a : A} (ha : a ∈ p) {s : A} (hs : s ∉ p)
    (hsa : s * a ∈ M) : a ∈ M := by
  obtain ⟨t, ht⟩ := exists_mul_sub_one_mem hs
  exact mem_of_mul_mem_of_mul_sub_one_mul_mem hsa (h2 (sq p ▸ Ideal.mul_mem_mul ht ha))

/-- An ideal of a Noetherian ring generates the maximal ideal of the localization at a maximal
ideal `p` exactly when it generates `p` modulo `p ^ 2`. The ideal is not assumed to lie in
`p`. -/
theorem map_atPrime_eq_maximalIdeal_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsMaximal] (Ap : Type v) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap p] [IsLocalRing Ap] [IsNoetherianRing Ap]
    {N : Ideal A} :
    N.map (algebraMap A Ap) = maximalIdeal Ap ↔ N ⊔ p ^ 2 = p := by
  have hpm : p.map (algebraMap A Ap) = maximalIdeal Ap :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p Ap
  by_cases hN : N ≤ p
  case neg =>
    obtain ⟨a, haN, hap⟩ := IsConcreteLE.not_le_iff_exists.1 hN
    have hunit : IsUnit (algebraMap A Ap a) :=
      IsLocalization.map_units (M := p.primeCompl) Ap ⟨a, hap⟩
    have htop : N.map (algebraMap A Ap) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haN) hunit
    exact iff_of_false (fun h => (maximalIdeal.isMaximal Ap).ne_top (htop ▸ h).symm)
      fun h => hN (le_sup_left.trans h.le)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hsup : (N ⊔ p ^ 2).map (algebraMap A Ap) = maximalIdeal Ap := by
      rw [Ideal.map_sup, h, Ideal.map_pow, hpm, sup_pow_two_eq_self]
    refine le_antisymm (sup_le hN (Ideal.pow_le_self (by norm_num))) fun a ha => ?_
    have hmem : algebraMap A Ap a ∈ (N ⊔ p ^ 2).map (algebraMap A Ap) := by
      rw [hsup, ← hpm]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hsM, hsa⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl Ap _ _).1 hmem
    exact mem_of_mul_mem_of_sq_le le_sup_right ha hsM hsa
  · have hmapped := congrArg (Ideal.map (algebraMap A Ap)) h
    rw [Ideal.map_sup, Ideal.map_pow, hpm] at hmapped
    exact (IsLocalRing.eq_maximalIdeal_iff_sup_sq (hpm ▸ Ideal.map_mono hN)).2 hmapped

/-! ### Powers of a maximal ideal under localization -/

/-- A maximal ideal is invertible modulo each of its powers: for `s ∉ p` there is a `t` with
`t * s - 1 ∈ p ^ i`. -/
theorem exists_mul_sub_one_mem_pow {A : Type u} [CommRing A] {p : Ideal A} [p.IsMaximal] {s : A}
    (hs : s ∉ p) (i : ℕ) : ∃ t : A, t * s - 1 ∈ p ^ i := by
  obtain ⟨t₁, ht₁⟩ := exists_mul_sub_one_mem hs
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t - t₁ * (t * s - 1), ?_⟩
      have heq : (t - t₁ * (t * s - 1)) * s - 1 = (t * s - 1) * (1 - t₁ * s) := by ring
      rw [heq, pow_succ]
      refine Ideal.mul_mem_mul ht ?_
      simpa using (Ideal.neg_mem_iff p).2 ht₁

/-- A power of a maximal ideal `p` is saturated at `p`: if a multiple of `a` by an element
outside `p` lies in `p ^ i`, then so does `a`. -/
theorem mem_pow_of_mul_mem_pow {A : Type u} [CommRing A] {p : Ideal A} [p.IsMaximal] (i : ℕ)
    {a s : A} (hs : s ∉ p) (hsa : s * a ∈ p ^ i) : a ∈ p ^ i := by
  obtain ⟨t, ht⟩ := exists_mul_sub_one_mem_pow hs i
  exact mem_of_mul_mem_of_mul_sub_one_mul_mem hsa (Ideal.mul_mem_right _ _ ht)

section AtPrime

variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsMaximal] (Ap : Type v) [CommRing Ap]
  [Algebra A Ap] [IsLocalization.AtPrime Ap p] (i : ℕ)

/-- The `i`-th power of the maximal ideal of a localization at a maximal ideal `p` is the
extension of `p ^ i`. -/
theorem maximalIdeal_pow_eq_map_pow [IsLocalRing Ap] :
    maximalIdeal Ap ^ i = (p ^ i).map (algebraMap A Ap) := by
  rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal p Ap]

/-- The kernel of `A → A_p ⧸ 𝔪 ^ i` is `p ^ i`. -/
theorem ker_quotient_pow_comp_algebraMap :
    RingHom.ker ((Ideal.Quotient.mk ((p ^ i).map (algebraMap A Ap))).comp
      (algebraMap A Ap)) = p ^ i := by
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  refine le_antisymm (fun a ha => ?_) (fun a ha => Ideal.mem_comap.2 (Ideal.mem_map_of_mem _ ha))
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl Ap _ _).1
      (Ideal.mem_comap.1 ha)
  exact mem_pow_of_mul_mem_pow i hs hsa

/-- The map `A → A_p ⧸ 𝔪 ^ i` is surjective. -/
theorem surjective_quotient_pow_comp_algebraMap :
    Function.Surjective
      ((Ideal.Quotient.mk ((p ^ i).map (algebraMap A Ap))).comp (algebraMap A Ap)) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  obtain ⟨t, ht⟩ := exists_mul_sub_one_mem_pow s.2 i
  refine ⟨t * a, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq]
  have hsplit : algebraMap A Ap (t * a) - IsLocalization.mk' Ap a s =
      algebraMap A Ap (t * (s : A) - 1) * IsLocalization.mk' Ap a s := by
    rw [map_sub, map_mul, map_mul, map_one, sub_mul, one_mul, ← IsLocalization.mk'_spec Ap a s]
    ring
  rw [hsplit]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ht)

/-- **The quotient by a power of a maximal ideal does not change under localization at that
ideal.** -/
noncomputable def quotientPowEquivAtPrime :
    (A ⧸ p ^ i) ≃+* (Ap ⧸ (p ^ i).map (algebraMap A Ap)) :=
  (Ideal.quotEquivOfEq (ker_quotient_pow_comp_algebraMap p Ap i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_quotient_pow_comp_algebraMap p Ap i))

end AtPrime

end IsLocalRing

namespace AdicCompletion

/-- Extending ideals along the completion map of a Noetherian local ring is injective. -/
theorem ideal_map_algebraMap_injective {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    Function.Injective fun I : Ideal R =>
      I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  have : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro I J h
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal R) R) I,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal R) R) J]
  exact congrArg (Ideal.comap _) h

/-- An ideal of a Noetherian local ring is the maximal ideal exactly when its extension to the
completion is the maximal ideal of the completion. -/
@[sga "7 VIII 7.3.5.3" "Completion clause"]
theorem ideal_map_eq_maximalIdeal_iff {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) :
    I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔ I = maximalIdeal R := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact ⟨fun h => ideal_map_algebraMap_injective h, fun h => by rw [h]⟩

end AdicCompletion

end
