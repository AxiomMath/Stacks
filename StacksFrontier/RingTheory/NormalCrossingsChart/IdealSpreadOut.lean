module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Spreading out an equality of ideals from a localization at a prime

Two ideals of a commutative ring whose extensions to a localization at a prime `q` agree already
agree "up to a denominator": there is an element `s ∉ q` carrying each into the other. This is the
elementary Zariski-shrinking step: any ring map sending `s` to a unit then carries the two ideals
to the same ideal, so the two ideals have the same extension to every localization at a prime not
containing `s`.

## Main results

* `Ideal.map_eq_map_of_mul_mem`: an equality of extensions along a map inverting `s`.
* `Ideal.exists_notMem_mul_mem_of_map_eq_map`: the denominator `s`, for finitely generated ideals.

## Implementation notes

Finite generation enters only through `Submodule.FG`: an element of the extension of `J` is a
fraction with numerator in `J`, so each of the finitely many generators of `I` is carried into `J`
by one denominator, and the product of those denominators works for all of `I` by span induction.
No Noetherian hypothesis is imposed, and the localization is an arbitrary one, so the statements
apply to the stalk of an affine scheme as it stands.

## References

* [Stacks Project, Tag 00QU](https://stacks.math.columbia.edu/tag/00QU)
-/

@[expose] public section

universe u v

namespace Ideal

/-- **An equality of ideals after inverting one element.** If `s` carries `I` into `J` and `J`
into `I`, then any ring map sending `s` to a unit carries `I` and `J` to the same ideal. -/
public theorem map_eq_map_of_mul_mem {B : Type u} {S : Type v} [CommRing B] [CommRing S]
    (φ : B →+* S) {I J : Ideal B} {s : B} (hs : IsUnit (φ s))
    (h₁ : ∀ a ∈ I, s * a ∈ J) (h₂ : ∀ a ∈ J, s * a ∈ I) :
    I.map φ = J.map φ := by
  have key : ∀ (K L : Ideal B), (∀ a ∈ K, s * a ∈ L) → K.map φ ≤ L.map φ := by
    intro K L h
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hs, ← map_mul]
    exact Ideal.mem_map_of_mem _ (h a ha)
  exact le_antisymm (key I J h₁) (key J I h₂)

/-- **Spreading out an equality of ideals.** If two finitely generated ideals of `B` have the same
extension to a localization of `B` at a prime `q`, then there is an element `s ∉ q` carrying each
of the two ideals into the other. -/
public theorem exists_notMem_mul_mem_of_map_eq_map {B : Type u} [CommRing B]
    {I J : Ideal B} (hI : I.FG) (hJ : J.FG) {q : Ideal B} [q.IsPrime]
    (S : Type v) [CommRing S] [Algebra B S] [IsLocalization.AtPrime S q]
    (h : I.map (algebraMap B S) = J.map (algebraMap B S)) :
    ∃ s ∉ q, (∀ a ∈ I, s * a ∈ J) ∧ (∀ a ∈ J, s * a ∈ I) := by
  classical
  -- One direction, for a finitely generated source ideal.
  have key : ∀ (K L : Ideal B), K.FG → K.map (algebraMap B S) ≤ L.map (algebraMap B S) →
      ∃ s ∉ q, ∀ a ∈ K, s * a ∈ L := by
    intro K L hK hle
    obtain ⟨T, hT⟩ := hK
    have hgen : ∀ a ∈ (T : Set B), ∃ m ∈ q.primeCompl, m * a ∈ L := fun a ha ↦
      (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl S L a).mp
        (hle (Ideal.mem_map_of_mem _ (hT ▸ Ideal.subset_span ha)))
    choose! m hm hmem using hgen
    refine ⟨∏ a ∈ T, m a, q.primeCompl.prod_mem fun a ha ↦ hm a ha, fun a ha ↦ ?_⟩
    rw [← hT] at ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.prod_erase_mul T m hx, mul_assoc]
      exact L.mul_mem_left _ (hmem x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact L.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact L.mul_mem_left _ hx
  obtain ⟨s₁, hs₁, h₁⟩ := key I J hI h.le
  obtain ⟨s₂, hs₂, h₂⟩ := key J I hJ h.ge
  refine ⟨s₁ * s₂, q.primeCompl.mul_mem hs₁ hs₂, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · rw [mul_comm s₁ s₂, mul_assoc]
    exact J.mul_mem_left _ (h₁ a ha)
  · rw [mul_assoc]
    exact I.mul_mem_left _ (h₂ a ha)

end Ideal

end
