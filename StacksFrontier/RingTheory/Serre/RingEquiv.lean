module

public import StacksFrontier.RingTheory.Etale.LocalRingPropertyList
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Serre's condition `(Sₖ)` is invariant under a ring isomorphism

`PropertySkRing R k` quantifies over the primes of `R` and compares, at each of them, the Krull
dimension of the localization with its depth. Both quantities are invariant under an
isomorphism of local rings, so the predicate transports along any isomorphism of rings — and so
does the depth of a local ring itself, `ringDepth_eq_of_ringEquiv` of
`StacksFrontier/RingTheory/Etale/LocalRingPropertyList.lean`, which is where the proof starts.

The depth here is `ringDepth`, the supremum of the lengths of the regular sequences in the
maximal ideal, not `Module.depth`: the two are compared nowhere in the library, so the
ring-equivalence lemmas proved for `Module.depth` in
`StacksFrontier/RingTheory/Depth/RingEquiv.lean` do not serve `PropertySkRing`.

## Main results

* `propertySkRing_of_ringEquiv` — **Serre's condition `(Sₖ)` is invariant under an isomorphism
  of rings.**

## Implementation notes

The two statements are universe-polymorphic in the two rings separately, so that a ring and a
ring built over it in another universe — a localization of a ring of sections, say — may be
compared.

An isomorphism carries a regular sequence to a regular sequence of the same length lying in the
maximal ideal, by `IsLocalRing.map_ringEquiv_maximalIdeal` and `AddEquiv.isRegular_congr`; the
two suprema then bound one another. For the predicate, a prime `p` of the target pulls back to
`p.comap e`, and `Localization.localRingEquiv` identifies the two localizations, under which
`ringKrullDim_eq_of_ringEquiv` and the depth statement move the inequality.

## References

* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public section

universe u v

/-- **The depth of a local ring does not increase along an isomorphism.** An isomorphism carries
a regular sequence in the maximal ideal of the source to one of the same length in the maximal
ideal of the target. -/
public theorem ringDepth_le_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : ringDepth A ≤ ringDepth B := by
  unfold ringDepth moduleDepth
  refine iSup_le fun xs => iSup_le fun hx => ?_
  have hmem : ∀ b ∈ xs.map e, b ∈ IsLocalRing.maximalIdeal B := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hx.1 a ha)
  have hreg : RingTheory.Sequence.IsRegular B (xs.map e) :=
    (AddEquiv.isRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun a _ x => e.map_mul a x))).mp hx.2
  simpa only [ringDepth, moduleDepth, List.length_map] using
    (show ((xs.map e).length : ℕ∞) ≤ ringDepth B from
      le_iSup_of_le (xs.map e) (le_iSup_of_le ⟨hmem, hreg⟩ le_rfl))

/-- **Serre's condition `(Sₖ)` is invariant under an isomorphism of rings.** A prime of the
target pulls back along the isomorphism, `Localization.localRingEquiv` identifies the two
localizations, and both the Krull dimension and the depth are invariant under that
isomorphism. -/
@[stacks 031P "Sk ring, isomorphism invariance"]
public theorem propertySkRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) (k : ℕ) (h : PropertySkRing A k) : PropertySkRing B k := by
  intro p hp
  have hq := h (p.comap e)
  rwa [(Localization.localRingEquiv (p.comap e) p e rfl).ringKrullDim,
    ringDepth_eq_of_ringEquiv (Localization.localRingEquiv (p.comap e) p e rfl)] at hq

/-- **Serre's condition `(Sₖ)` is the same for two isomorphic rings.** -/
public theorem propertySkRing_iff_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) (k : ℕ) : PropertySkRing A k ↔ PropertySkRing B k :=
  ⟨propertySkRing_of_ringEquiv e k, propertySkRing_of_ringEquiv e.symm k⟩

end
