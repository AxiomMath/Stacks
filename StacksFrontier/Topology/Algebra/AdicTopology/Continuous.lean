module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Continuity of ring homomorphisms for adic topologies

Let `R` and `S` be commutative rings, let `I : Ideal R` and `J : Ideal S`, and let `φ : R →+* S`
be a ring homomorphism. Equipping `R` with the `I`-adic topology and `S` with the `J`-adic
topology makes both of them topological rings, so `φ` is a homomorphism of topological rings
precisely when it is continuous.

## Main results

* `RingHom.continuous_adic_iff`: `φ` is continuous for the `I`-adic topology on `R` and the
  `J`-adic topology on `S` if and only if `φ (I ^ n) ⊆ J` for some `n ≥ 1`.

## References

* Lemma 15.37.2 of the Stacks project (Tag 07E9).
-/

@[expose] public section

/-- A ring homomorphism `φ : R → S` between commutative rings is continuous with respect to the
`I`-adic topology on `R` and the `J`-adic topology on `S` if and only if there exists `n ≥ 1` with
`φ(I ^ n) ⊆ J`. -/
@[stacks 07E9]
theorem RingHom.continuous_adic_iff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    @Continuous R S I.adicTopology J.adicTopology φ ↔
      ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ I ^ n, φ x ∈ J := by
  let tR : TopologicalSpace R := I.adicTopology
  let tS : TopologicalSpace S := J.adicTopology
  have htR : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  have htS : IsTopologicalRing S := J.ringFilterBasis.isTopologicalRing
  have h := (Ideal.hasBasis_nhds_adic I 0).tendsto_iff (Ideal.hasBasis_nhds_adic J 0) (f := φ)
  simp only [zero_add, Set.image_id', SetLike.mem_coe, true_and, forall_const] at h
  constructor
  · intro hcont
    obtain ⟨k, hk⟩ := h.mp (by simpa [ContinuousAt] using hcont.continuousAt (x := 0)) 1
    exact ⟨max k 1, le_max_right _ _, fun x hx =>
      by simpa using hk x (Ideal.pow_le_pow_right (le_max_left _ _) hx)⟩
  · rintro ⟨n, -, hsub⟩
    refine continuous_of_continuousAt_zero φ ?_
    rw [ContinuousAt, map_zero, h]
    refine fun m => ⟨n * m, fun x hx => ?_⟩
    rw [pow_mul] at hx
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hsub) m
      (Ideal.map_pow φ _ m ▸ Ideal.mem_map_of_mem φ hx)
