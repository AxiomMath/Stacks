module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Colon ideals and localization

Let `R → S` be a localization of commutative rings at a submonoid `M`, and let `I`, `J` be ideals
of `R`. The colon ideal, or ideal quotient,

`(I : J) = {r ∈ R | r · J ⊆ I}`,

is `Submodule.colon I (J : Set R)` in Mathlib. This file proves that forming it commutes with
localization as soon as `J` is finitely generated:

`(I : J) · S = (I · S : J · S)`.

## Main results

* `Ideal.map_colon_of_fg`: the displayed equality.

## Implementation notes

The inclusion `⊆` holds for arbitrary `J`: it says only that the image of `(I : J)` multiplies
the generators of `J · S` into `I · S`, which is the image of a relation already available over
`R`.

Finite generation is used, and is genuinely needed, for the reverse inclusion. An element of
`(I · S : J · S)` is `x / s`, and for each generator `y` of `J` the hypothesis provides *some*
`m ∈ M` with `m · x · y ∈ I`, by `IsLocalization.mk'_mem_map_algebraMap_iff`. A single `m` must
serve all the generators at once for `m · x` to lie in `(I : J)`, and that is arranged by taking
the product of the finitely many witnesses. Since `m` becomes a unit in `S`, multiplying by it
does not change membership in the image ideal.
-/

@[expose] public section

universe u v

namespace Ideal

/-- **Colon ideals commute with localization.** Let `S` be a localization of `R` at a submonoid
`M` and let `I`, `J` be ideals of `R` with `J` finitely generated. Then the image in `S` of the
colon ideal `(I : J)` is the colon ideal of the images,

`(I : J) · S = (I · S : J · S)`.

Finite generation of `J` is needed: a single denominator must clear the finitely many relations
coming from the generators of `J`. -/
theorem map_colon_of_fg {R : Type u} [CommRing R] (M : Submonoid R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]
    (I J : Ideal R) (hJ : (J : Submodule R R).FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon ((J.map (algebraMap R S) : Ideal S) : Set S) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, Submodule.mem_colon]
    intro z hz
    have h1 : Ideal.span {r} * J ≤ I := Ideal.mul_le.mpr fun a ha b hb => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      have := (Submodule.mem_colon.mp hr) (c * b) (J.mul_mem_left c hb)
      simpa [mul_assoc, smul_eq_mul] using this
    have h2 : Ideal.span {algebraMap R S r} * J.map (algebraMap R S) ≤
        I.map (algebraMap R S) := by
      have := Ideal.map_mono (f := algebraMap R S) h1
      rwa [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at this
    exact h2 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
  · intro z hz
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
    obtain ⟨t, hts⟩ := hJ
    have key : ∀ y : t, ∃ m : M, (m : R) * (x * (y : R)) ∈ I := by
      intro y
      have hy : (y : R) ∈ J := by rw [← hts]; exact Ideal.subset_span y.2
      have h0 : IsLocalization.mk' S x s * algebraMap R S (y : R) ∈
          I.map (algebraMap R S) :=
        (Submodule.mem_colon.mp hz) _ (Ideal.mem_map_of_mem _ hy)
      rw [← IsLocalization.mk'_one (M := M) (S := S) (y : R), ← IsLocalization.mk'_mul,
        mul_one] at h0
      obtain ⟨m, hm, hmem⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff M S I _ s).mp h0
      exact ⟨⟨m, hm⟩, hmem⟩
    choose m hm using key
    set m0 : M := ∏ y ∈ t.attach, m y with hm0
    have hmem : (m0 : R) * x ∈ I.colon (J : Set R) := by
      rw [← hts, Submodule.colon_span]
      refine Submodule.mem_colon.mpr fun y hy => ?_
      have hyt : y ∈ t := hy
      have hsplit : (m0 : R) = (m ⟨y, hyt⟩ : R) * ∏ w ∈ t.attach.erase ⟨y, hyt⟩, (m w : R) := by
        rw [hm0]
        push_cast
        exact (Finset.mul_prod_erase _ _ (Finset.mem_attach t ⟨y, hyt⟩)).symm
      have hI := I.mul_mem_left (∏ w ∈ t.attach.erase ⟨y, hyt⟩, (m w : R)) (hm ⟨y, hyt⟩)
      rw [smul_eq_mul]
      refine Eq.mp (congrArg (· ∈ I) ?_) hI
      rw [hsplit]; ring
    refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S (s * m0))).mp ?_
    have hkey : algebraMap R S ((s * m0 : M) : R) * IsLocalization.mk' S x s =
        algebraMap R S ((m0 : R) * x) := by
      rw [show ((s * m0 : M) : R) = (s : R) * (m0 : R) from rfl, map_mul,
        mul_comm ((algebraMap R S) (s : R)), mul_assoc, IsLocalization.mk'_spec', map_mul]
    rw [hkey]
    exact Ideal.mem_map_of_mem _ hmem

end Ideal

end
