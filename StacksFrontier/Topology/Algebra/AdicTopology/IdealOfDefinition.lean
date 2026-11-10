module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Comparison of ideals of definition

An ideal of definition of a topological ring is an open ideal whose powers are cofinal among
the neighbourhoods of zero.  This file records the elementary facts about such ideals
which make the notions defined relative to an ideal of definition independent of the choice,
and which compare them with the weak ideals of definition:

* the powers of one ideal of definition are cofinal below *every* open ideal, so any two
  ideals of definition `I` and `J` satisfy `I ^ n ≤ J` and `J ^ n ≤ I` for a common `n`;
* a finitely generated weak ideal of definition is an ideal of definition, so a weakly
  admissible Noetherian topological ring has an ideal of definition;
* an ideal of definition is a weak ideal of definition;
* an open ideal contained in an ideal of definition is an ideal of definition, so in an
  admissible topological ring all sufficiently small open ideals are ideals of definition.

## Main results

* `TopologicalRing.IsIdealOfDefinition.exists_pow_le`
* `TopologicalRing.IsIdealOfDefinition.exists_pow_le_and_pow_le`
* `TopologicalRing.isIdealOfDefinition_of_isWeakIdealOfDefinition`
* `TopologicalRing.isPreAdmissible_of_isWeaklyPreAdmissible`
* `TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition`
* `TopologicalRing.isIdealOfDefinition_of_le_of_isOpen`

## References

* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- The powers of an ideal of definition are cofinal below every open ideal. -/
@[ega "I 10.12.1" "Affine comparison"]
public theorem IsIdealOfDefinition.exists_pow_le {I J : Ideal R}
    (hI : IsIdealOfDefinition I) (hJ : IsOpen (J : Set R)) :
    ∃ n : ℕ, I ^ n ≤ J := by
  obtain ⟨n, hn⟩ := hI.2 (J : Set R) (hJ.mem_nhds J.zero_mem)
  exact ⟨n, fun _ hx ↦ hn hx⟩

/-- Any two ideals of definition are mutually cofinal: a common exponent `n` satisfies both
`I ^ n ≤ J` and `J ^ n ≤ I`. -/
public theorem IsIdealOfDefinition.exists_pow_le_and_pow_le {I J : Ideal R}
    (hI : IsIdealOfDefinition I) (hJ : IsIdealOfDefinition J) :
    ∃ n : ℕ, I ^ n ≤ J ∧ J ^ n ≤ I := by
  obtain ⟨m, hm⟩ := hI.exists_pow_le hJ.1
  obtain ⟨k, hk⟩ := hJ.exists_pow_le hI.1
  refine ⟨max m k, (Ideal.pow_le_pow_right (le_max_left m k)).trans hm,
    (Ideal.pow_le_pow_right (le_max_right m k)).trans hk⟩

/-- A finitely generated weak ideal of definition of a linearly topologized ring is an ideal
of definition: its elements are topologically nilpotent, so it is contained in the radical of
every ideal neighbourhood of zero, and finite generation turns that into an inclusion of a
power. -/
@[sga "3 VIIB 1.6.D" "partial"]
public theorem isIdealOfDefinition_of_isWeakIdealOfDefinition [IsTopologicalRing R]
    [IsLinearTopology R R] {I : Ideal R} (hI : IsWeakIdealOfDefinition I) (hfg : I.FG) :
    IsIdealOfDefinition I := by
  refine ⟨hI.1, fun U hU ↦ ?_⟩
  obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_ideal (R := R)).mem_iff.mp hU
  have hrad : I ≤ J.radical := fun x hx ↦ (hI.2 x hx).exists_pow_mem_of_mem_nhds hJ
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  exact ⟨n, fun x hx ↦ hJU (hn hx)⟩

/-- An ideal of definition is a weak ideal of definition: given a neighbourhood of zero, some
power of the ideal lies inside it, hence so does every higher power of each of its elements. -/
public theorem isWeakIdealOfDefinition_of_isIdealOfDefinition {I : Ideal R}
    (hI : IsIdealOfDefinition I) : IsWeakIdealOfDefinition I := by
  refine ⟨hI.1, fun x hx ↦ ?_⟩
  change Filter.Tendsto (x ^ ·) Filter.atTop (𝓝 (0 : R))
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨n, hn⟩ := hI.2 U hU
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact hn (Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m))

/-- A pre-admissible topological ring is weakly pre-admissible: its ideal of definition is a
weak ideal of definition. -/
public theorem isWeaklyPreAdmissible_of_isPreAdmissible (hR : IsPreAdmissible R) :
    IsWeaklyPreAdmissible R :=
  hR.imp fun _ hI ↦ isWeakIdealOfDefinition_of_isIdealOfDefinition hI

/-- **Stacks 0AIW.** An open ideal contained in an ideal of definition is an ideal of definition:
its powers lie inside the corresponding powers of the larger ideal, and those are cofinal among
the neighbourhoods of zero. Since in an admissible topological ring the open ideals form a basis
of neighbourhoods of zero, this is the source's observation that all sufficiently small open
ideals of such a ring are ideals of definition. -/
@[stacks 0AIW "in an admissible topological ring all sufficiently small open ideals are ideals \
of definition: any open ideal contained in an ideal of definition is one"]
public theorem isIdealOfDefinition_of_le_of_isOpen {I J : Ideal R}
    (hJ : IsIdealOfDefinition J) (hI : IsOpen (I : Set R)) (hIJ : I ≤ J) :
    IsIdealOfDefinition I := by
  refine ⟨hI, fun U hU ↦ ?_⟩
  obtain ⟨n, hn⟩ := hJ.2 U hU
  exact ⟨n, fun _ hx ↦ hn (pow_le_pow_left' hIJ n hx)⟩

/-- A weakly pre-admissible Noetherian topological ring is pre-admissible. -/
public theorem isPreAdmissible_of_isWeaklyPreAdmissible [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R] (hR : IsWeaklyPreAdmissible R) :
    IsPreAdmissible R :=
  ⟨hR.choose, isIdealOfDefinition_of_isWeakIdealOfDefinition hR.choose_spec
    (Ideal.fg_of_isNoetherianRing _)⟩

end TopologicalRing

end
