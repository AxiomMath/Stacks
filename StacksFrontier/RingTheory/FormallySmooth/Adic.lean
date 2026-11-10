module

public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous

/-!
# Topological and algebraic adic formal smoothness

For a discrete source and an adic target, the continuous square-zero lifting property is
equivalent to the algebraic lifting property in which the test map kills a power of an ideal of
definition.

## Main results

* `RingHom.formallySmoothTop_of_formallySmoothNAdic`: the algebraic adic lifting property
  implies the topological one, with no hypothesis on the topology of the source.
* `RingHom.formallySmoothTop_iff_formallySmoothNAdic`: comparison of the topological and
  algebraic formulations.

## References

* [Stacks Project, Tag 07EG](https://stacks.math.columbia.edu/tag/07EG)
-/

@[expose] public section

namespace RingHom

/-- A ring map from an adic ring to a discrete ring is continuous iff it kills a positive power
of the ideal of definition. -/
private theorem continuous_iff_pow_le_ker_of_isAdic {S T : Type*} [CommRing S] [CommRing T]
    [TopologicalSpace S] [TopologicalSpace T] [DiscreteTopology T] (n : Ideal S) (hn : IsAdic n)
    (f : S →+* T) : Continuous f ↔ ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker f := by
  have hbot : IsAdic (⊥ : Ideal T) := is_bot_adic_iff.mpr inferInstance
  change (inferInstance : TopologicalSpace S) = n.adicTopology at hn
  change (inferInstance : TopologicalSpace T) = (⊥ : Ideal T).adicTopology at hbot
  have := RingHom.continuous_adic_iff f n ⊥
  rw [← hn, ← hbot] at this
  exact this.trans (by simp [IsConcreteLE.le_iff])

/-- The algebraic adic lifting property implies the topological one, for an arbitrary topology
on the source: if `phi` is formally smooth for the `n`-adic topology on `S`, then `phi` is
topologically formally smooth. -/
theorem formallySmoothTop_of_formallySmoothNAdic.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsTopologicalRing S]
    (phi : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (h : FormallySmoothNAdic.{u, v, w} phi n) : FormallySmoothTop.{u, v, w} phi := by
  intro A _ _ _ J hJ f _ psi hpsi hcomm
  have : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
  obtain ⟨k, hk1, hkle⟩ := (continuous_iff_pow_le_ker_of_isAdic n hn psi).mp hpsi
  obtain ⟨g, hqg, hgf⟩ := h A J hJ f psi hcomm ⟨k, hk1, hkle⟩
  have hJg : n ^ k ≤ J.comap g := by
    intro x hx
    have hq' : Ideal.Quotient.mk J (g x) = psi x :=
      congrArg (fun q : S →+* A ⧸ J ↦ q x) hqg
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp (hq'.trans (hkle hx))
  have hzero : (n ^ (k * 2)).map g ≤ (⊥ : Ideal A) := by
    rw [pow_mul, Ideal.map_pow]
    exact (pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hJg) 2).trans hJ.le
  exact ⟨g, (continuous_iff_pow_le_ker_of_isAdic n hn g).mpr ⟨k * 2, by omega,
    Ideal.map_le_iff_le_comap.mp hzero⟩, hgf, hqg⟩

/-- For a discrete source and an adic target, topological formal smoothness is equivalent to
formal smoothness for the adic topology. -/
@[stacks 07EG]
theorem formallySmoothTop_iff_formallySmoothNAdic.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]
    [TopologicalSpace S] [IsTopologicalRing S]
    (phi : R →+* S) (n : Ideal S) (hn : IsAdic n) :
    FormallySmoothTop.{u, v, w} phi ↔ FormallySmoothNAdic.{u, v, w} phi n := by
  refine ⟨?_, formallySmoothTop_of_formallySmoothNAdic phi n hn⟩
  intro h A _ J hJ f psi hcomm ⟨k, hk1, hkle⟩
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
  have hpsi : Continuous psi :=
    (continuous_iff_pow_le_ker_of_isAdic n hn psi).mpr ⟨k, hk1, hkle⟩
  obtain ⟨g, _, hgf, hqg⟩ :=
    h A J hJ f continuous_of_discreteTopology psi hpsi hcomm
  exact ⟨g, hqg, hgf⟩

end RingHom
