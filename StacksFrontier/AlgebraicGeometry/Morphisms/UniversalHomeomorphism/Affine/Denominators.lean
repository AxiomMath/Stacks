module

public import Mathlib.RingTheory.Localization.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Clearing denominators for special elements

For a subring `A` of a commutative ring `B`, an element of the localization of `B` which is
not in the localized subring, but whose prescribed power multiples are in it, can be
represented with a numerator having the analogous properties before localization.

## Main definitions

None.

## Main results

* `IsLocalization.exists_numerator_not_mem_of_localization`: simultaneously clears the
  denominators in these membership and non-membership conditions.

## Implementation notes

The ring extension is represented by a subring `A : Subring B`. Both localizations are the
canonical `Localization` types, and membership in the localized copy of `A` is expressed as
membership in the range of its canonical map to the localization of `B`. A family indexed by
`Fin n` corresponds to the indices `1, ..., n`, so its exponent is `i + 1`.

## References

* [Stacks Project, Tag 0CN9](https://stacks.math.columbia.edu/tag/0CN9)
-/

@[expose] public section

namespace IsLocalization

universe u

/-- If the image of `z` in the localization of `B` lies in the range of the induced map from
the localization of a subring `A`, then some element of the localizing submonoid of `A`
scales `z` into `A`. -/
private theorem exists_mul_mem_of_map_mem
    {B : Type u} [CommRing B] (A : Subring B) (S : Submonoid A) (z : B)
    (hz : algebraMap B (Localization (S.map A.subtype)) z ∈ Set.range
      (IsLocalization.map (M := S) (S := Localization S) (T := S.map A.subtype)
        (Localization (S.map A.subtype)) A.subtype S.le_comap_map)) :
    ∃ s : S, (s.1 : B) * z ∈ A := by
  let T : Submonoid B := S.map A.subtype
  let f := IsLocalization.map (M := S) (S := Localization S) (T := T)
    (Localization T) A.subtype S.le_comap_map
  obtain ⟨w, hw⟩ := hz
  obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj S w
  have heq : algebraMap B (Localization T) (z * (t : B)) =
      algebraMap B (Localization T) (a : B) := by
    have h := congrArg f ht
    rw [map_mul, show f w = algebraMap B (Localization T) z from hw] at h
    simpa [f, map_mul, IsLocalization.map_eq, mul_comm] using h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists T (Localization T)).mp heq
  obtain ⟨s, hsm, hsc⟩ := c.property
  refine ⟨(⟨s, hsm⟩ : S) * t, ?_⟩
  have hA : (c : B) * (z * (t : B)) ∈ A := by
    rw [hc]
    exact A.mul_mem (by rw [← hsc]; exact s.property) a.property
  convert hA using 1
  simp [← hsc, mul_comm, mul_left_comm]

/-- **Stacks 0CN9.** Special-element conditions over a localization can be witnessed by a
numerator before localization. -/
@[stacks 0CN9]
theorem exists_numerator_not_mem_of_localization
    {B : Type u} [CommRing B] (A : Subring B) (S : Submonoid A)
    {n : ℕ} (b : Fin n → B) (x : Localization (S.map A.subtype))
    (hx : x ∉ Set.range
      (IsLocalization.map (M := S) (S := Localization S) (T := S.map A.subtype)
        (Localization (S.map A.subtype)) A.subtype S.le_comap_map))
    (hbx : ∀ i, algebraMap B (Localization (S.map A.subtype)) (b i) *
      x ^ (i.val + 1) ∈ Set.range
        (IsLocalization.map (M := S) (S := Localization S) (T := S.map A.subtype)
          (Localization (S.map A.subtype)) A.subtype S.le_comap_map)) :
    ∃ (s : S) (y : B),
      x = IsLocalization.mk' (Localization (S.map A.subtype)) y
          ⟨A.subtype s.1, Submonoid.mem_map_of_mem A.subtype s.2⟩ ∧
        y ∉ A ∧ ∀ i, b i * y ^ (i.val + 1) ∈ A := by
  let T : Submonoid B := S.map A.subtype
  let f := IsLocalization.map (M := S) (S := Localization S) (T := T)
    (Localization T) A.subtype S.le_comap_map
  let den (s : S) : T :=
    ⟨A.subtype s.1, Submonoid.mem_map_of_mem A.subtype s.2⟩
  have hfin (F : Finset (Fin n)) :
      ∃ (s : S) (y : B), x = IsLocalization.mk' (Localization T) y (den s) ∧
        ∀ i ∈ F, b i * y ^ (i.val + 1) ∈ A := by
    induction F using Finset.induction_on with
    | empty =>
      obtain ⟨y, d, hd⟩ := IsLocalization.exists_mk'_eq T x
      obtain ⟨s, hs, hsd⟩ := d.property
      refine ⟨⟨s, hs⟩, y, ?_, by simp⟩
      rw [show den (⟨s, hs⟩ : S) = d from Subtype.ext hsd]
      exact hd.symm
    | @insert i F hi ih =>
      obtain ⟨s, y, hrep, hprev⟩ := ih
      let k := i.val + 1
      have hspec : x * algebraMap B (Localization T) (s : B) =
          algebraMap B (Localization T) y := by
        simpa [den] using (hrep.symm ▸ IsLocalization.mk'_spec (Localization T) y (den s))
      have hpow : x ^ k * algebraMap B (Localization T) ((s : B) ^ k) =
          algebraMap B (Localization T) (y ^ k) := by
        simpa [mul_pow, map_pow] using congrArg (fun z : Localization T => z ^ k) hspec
      have hden : algebraMap B (Localization T) ((s : B) ^ k) ∈ Set.range f :=
        ⟨algebraMap A (Localization S) (s.1 ^ k), by simp [f, IsLocalization.map_eq]⟩
      have hz : algebraMap B (Localization T) (b i * y ^ k) ∈ Set.range f := by
        have hm : (algebraMap B (Localization T) (b i) * x ^ k) *
            algebraMap B (Localization T) ((s : B) ^ k) ∈ Set.range f :=
          f.range.mul_mem (hbx i) hden
        convert hm using 1
        rw [map_mul, ← hpow]
        ring
      obtain ⟨c, hc⟩ := exists_mul_mem_of_map_mem A S (b i * y ^ k) hz
      refine ⟨c * s, (c : B) * y, ?_, ?_⟩
      · calc
          x = IsLocalization.mk' (Localization T) y (den s) := hrep
          _ = IsLocalization.mk' (Localization T) (c : B) (den c) *
              IsLocalization.mk' (Localization T) y (den s) := by
                simp [den]
          _ = IsLocalization.mk' (Localization T) ((c : B) * y) (den (c * s)) := by
                rw [← IsLocalization.mk'_mul]
                rfl
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [k, pow_succ, mul_pow, mul_assoc, mul_comm, mul_left_comm] using
            (A.mul_mem (A.pow_mem c.1.property j.val) hc)
        · simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using
            (A.mul_mem (A.pow_mem c.1.property (j.val + 1)) (hprev j hj))
  obtain ⟨s, y, hrep, hy⟩ := hfin Finset.univ
  refine ⟨s, y, hrep, fun hya => hx ?_, fun i => hy i (Finset.mem_univ i)⟩
  rw [hrep]
  exact ⟨IsLocalization.mk' (Localization S) ⟨y, hya⟩ s, by simp [T, den, IsLocalization.map_mk']⟩

end IsLocalization

end
