module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# A countably indexed weakly admissible ring is its own completion over itself

The completion `TopologicalRing.CompletionOver f` attached to a ring map `f : B →+* A` is the
inverse limit of the discrete quotients `A / JA`, taken over the weak ideals of definition `J` of
`B`. For a weakly admissible `B` whose topology is countably indexed, the canonical map
`B → CompletionOver (RingHom.id B)` is bijective and open, hence an isomorphism of topological
rings.

## Main results

* `TopologicalRing.CompletionOver.bijective_canonicalMap_id`: the canonical map
  `B → CompletionOver (RingHom.id B)` is bijective.
* `TopologicalRing.CompletionOver.isOpenMap_canonicalMap_id`: it is an open map.
* `TopologicalRing.exists_ringEquiv_completionOver_id`: it is a ring isomorphism and a
  homeomorphism.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0APT](https://stacks.math.columbia.edu/tag/0APT)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
-/

@[expose] public section

namespace TopologicalRing

universe u

namespace CompletionOver

section Identity

variable {B : Type u} [CommRing B] [TopologicalSpace B]

/-- Completing `B` along its own weak ideals of definition, the canonical map from the base and
the canonical map from the ring being completed coincide. -/
public lemma canonicalMap_id : canonicalMap (RingHom.id B) = ofTarget (RingHom.id B) := by
  rw [← ofTarget_comp (RingHom.id B), RingHom.comp_id]

/-- The image of `B` is dense in the completion of `B` over itself. -/
public lemma denseRange_canonicalMap_id (hB : IsWeaklyPreAdmissible B) :
    DenseRange (canonicalMap (RingHom.id B)) := by
  rw [canonicalMap_id]
  exact denseRange_ofTarget (RingHom.id B) hB

/-- An element of `B` killed by the canonical map to the completion of `B` over itself lies in
every weak ideal of definition of `B`. -/
public lemma mem_of_canonicalMap_id_eq_zero {J : Ideal B} (hJ : IsWeakIdealOfDefinition J)
    {b : B} (hb : canonicalMap (RingHom.id B) b = 0) : b ∈ J := by
  have h : projection (RingHom.id B) ⟨J, hJ⟩ (canonicalMap (RingHom.id B) b) = 0 := by
    rw [hb, map_zero]
  rw [projection_canonicalMap] at h
  simpa only [extendedIdeal, Ideal.map_id, RingHom.id_apply] using
    Ideal.Quotient.eq_zero_iff_mem.mp h

end Identity

section WeaklyAdmissible

variable {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B]

/-- The canonical map from a weakly admissible ring to its completion over itself is injective.
-/
public lemma injective_canonicalMap_id (hB : IsWeaklyAdmissible B) :
    Function.Injective (canonicalMap (RingHom.id B)) := by
  have := hB.2.2
  have hzero : ∀ b : B, canonicalMap (RingHom.id B) b = 0 → b = 0 := by
    intro b hb
    by_contra hne
    obtain ⟨J, hJ, hJsub⟩ :=
      (hasBasis_nhds_zero_isWeakIdealOfDefinition hB).mem_iff.mp
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hne)))
    exact hJsub (mem_of_canonicalMap_id_eq_zero hJ hb) rfl
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by rw [map_sub, hxy, sub_self]))

/-- The canonical map from a countably indexed weakly admissible ring to its completion over
itself is bijective. -/
public lemma bijective_canonicalMap_id (hB : IsWeaklyAdmissible B)
    (hcount : (nhds (0 : B)).IsCountablyGenerated) :
    Function.Bijective (canonicalMap (RingHom.id B)) := by
  have := hB.2.2
  exact ⟨injective_canonicalMap_id hB,
    RingHom.surjective_of_isTaut_of_denseRange (canonicalMap (RingHom.id B))
      (continuous_canonicalMap (RingHom.id B)) hB.2.1 hcount
      (isTaut_canonicalMap (RingHom.id B) hB.1) (denseRange_canonicalMap_id hB.1)⟩

/-- The canonical map from a countably indexed weakly admissible ring to its completion over
itself is an open map. -/
public lemma isOpenMap_canonicalMap_id (hB : IsWeaklyAdmissible B)
    (hcount : (nhds (0 : B)).IsCountablyGenerated) :
    IsOpenMap (canonicalMap (RingHom.id B)) := by
  have := hB.2.2
  exact RingHom.isOpenMap_of_isTaut_of_denseRange (canonicalMap (RingHom.id B))
    (continuous_canonicalMap (RingHom.id B)) hB.2.1 hcount
    (isTaut_canonicalMap (RingHom.id B) hB.1) (denseRange_canonicalMap_id hB.1)

end WeaklyAdmissible

end CompletionOver

section Main

variable {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B]

/-- A countably indexed weakly admissible topological ring is its own completion over itself:
the canonical map `B → CompletionOver (RingHom.id B)` is a ring isomorphism and a homeomorphism.
-/
public theorem exists_ringEquiv_completionOver_id (hB : IsWeaklyAdmissible B)
    (hcount : (nhds (0 : B)).IsCountablyGenerated) :
    ∃ e : B ≃+* CompletionOver (RingHom.id B),
      (∀ b : B, e b = CompletionOver.canonicalMap (RingHom.id B) b) ∧
        Continuous e ∧ Continuous e.symm := by
  have := hB.2.2
  have hopen := CompletionOver.isOpenMap_canonicalMap_id hB hcount
  let e : B ≃+* CompletionOver (RingHom.id B) :=
    RingEquiv.ofBijective (CompletionOver.canonicalMap (RingHom.id B))
      (CompletionOver.bijective_canonicalMap_id hB hcount)
  exact ⟨e, fun _ ↦ rfl, continuous_canonicalMap (RingHom.id B),
    (e.toEquiv.toHomeomorphOfContinuousOpen (continuous_canonicalMap (RingHom.id B))
      hopen).continuous_symm⟩

end Main

end TopologicalRing

end
