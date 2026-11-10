module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings

/-!
# Weak ideals of definition and weakly admissible topological rings

A *weak ideal of definition* of a topological ring is an open ideal all of whose elements are
topologically nilpotent. A ring is *weakly pre-admissible* when it has one, and a linearly
topologized ring is *weakly admissible* when it is weakly pre-admissible, complete and separated.

## Main definitions

* `TopologicalRing.IsWeakIdealOfDefinition`: an open ideal of topologically nilpotent elements.
* `TopologicalRing.IsWeaklyPreAdmissible`: the existence of a weak ideal of definition.
* `TopologicalRing.IsWeaklyAdmissible`: weakly pre-admissible, complete and separated.

## Main results

* `TopologicalRing.topologicalNilradical_isRadical`,
  `TopologicalRing.isClosed_topologicalNilradical`: in a linearly topologized ring the ideal of
  topologically nilpotent elements is radical, and closed when the ring is a topological ring.
* `TopologicalRing.closure_map_le_topologicalNilradical`: the closure of the extension of an ideal
  of topologically nilpotent elements along a continuous ring map consists of topologically
  nilpotent elements.
* `TopologicalRing.continuous_add_of_hasBasis_addSubgroup`: addition is continuous when the
  translates of a family of additive subgroups form a neighbourhood basis at every point.
* `TopologicalRing.exists_isOpen_ideal_map_le`: every open ideal of the target of a continuous ring
  map contains the extension of an open ideal of the source.
* `TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition`: in a weakly admissible ring the
  weak ideals of definition form a basis of neighbourhoods of zero.

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AMW](https://stacks.math.columbia.edu/tag/0AMW)
* [Stacks Project, Tag 0AMR](https://stacks.math.columbia.edu/tag/0AMR)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
-/

@[expose] public section

namespace TopologicalRing

section

/-- Every element of an ideal of definition is topologically nilpotent. -/
@[ega "0 7.1.4" "(ii)"]
public lemma topologicallyNilpotent_of_mem_idealOfDefinition {R : Type*} [CommRing R]
    [TopologicalSpace R] (J : Ideal R) (hJ : TopologicalRing.IsIdealOfDefinition J) {x : R}
    (hx : x ∈ J) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨n, hn⟩ := hJ.2 U hU
  exact Filter.eventually_atTop.2
    ⟨n, fun m hm ↦ hn (Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m))⟩


add_to_stacks 0AMV "part (1)" IsTopologicallyNilpotent
add_to_sga "3 VIIB 0.1.2" IsTopologicallyNilpotent
add_to_ega "0 7.1.1" IsTopologicallyNilpotent

/-- A weak ideal of definition is an open ideal consisting entirely of
topologically nilpotent elements. -/
@[stacks 0AMV "part (2)"]
abbrev IsWeakIdealOfDefinition {R : Type*} [CommRing R] [TopologicalSpace R]
    (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧ ∀ x ∈ I, IsTopologicallyNilpotent x

/-- A topological ring is weakly pre-admissible if it has a weak ideal of
definition. -/
@[stacks 0AMV "part (3)"]
abbrev IsWeaklyPreAdmissible (R : Type*) [CommRing R] [TopologicalSpace R] : Prop :=
  ∃ I : Ideal R, IsWeakIdealOfDefinition I

/-- A linearly topologized ring is weakly admissible if it is weakly
pre-admissible, complete, and separated. Completeness uses the canonical
uniformity of its additive topological group. -/
@[stacks 0AMV "part (4)"]
abbrev IsWeaklyAdmissible (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  IsWeaklyPreAdmissible R ∧
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) ∧ T2Space R

end

section

open scoped Pointwise

add_to_stacks 0AMW "the ideal" topologicalNilradical
add_to_ega "0 7.1.3" topologicalNilradical
add_to_ega "0 7.1.6" topologicalNilradical

/-- In a linearly topologized ring, `x` is topologically nilpotent iff its powers eventually lie
in every ideal that is a neighbourhood of zero. -/
private theorem isTopologicallyNilpotent_iff_forall_ideal {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsLinearTopology B B] {x : B} :
    IsTopologicallyNilpotent x ↔
      ∀ J : Ideal B, (J : Set B) ∈ nhds (0 : B) → ∃ n, ∀ m ≥ n, x ^ m ∈ J := by
  simp [IsTopologicallyNilpotent, Filter.atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal]

/-- In a linearly topologized commutative ring, the ideal of topologically nilpotent
elements is closed. -/
@[stacks 0AMW "closedness"]
public lemma isClosed_topologicalNilradical {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] :
    IsClosed (topologicalNilradical B : Set B) := by
  rw [← closure_subset_iff_isClosed]
  intro g hg
  change IsTopologicallyNilpotent g
  rw [isTopologicallyNilpotent_iff_forall_ideal]
  intro J hJ
  obtain ⟨f, hf, h, hh, rfl⟩ := closure_subset_add_right_of_mem_nhds_zero _ hJ hg
  obtain ⟨m, hm⟩ :=
    (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hf).exists_pow_mem_of_mem_nhds hJ
  exact ⟨m + 1, fun n (hn : m + 1 ≤ n) ↦
    J.add_pow_mem_of_pow_mem_of_le (m := m) (n := 1) (k := n) hm
      (by simpa using hh) (by omega)⟩

/-- In a linearly topologized commutative ring, the ideal of topologically nilpotent
elements is radical. -/
@[stacks 0AMW "radicality"]
public lemma topologicalNilradical_isRadical {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsLinearTopology B B] :
    (topologicalNilradical B).IsRadical := by
  rw [Ideal.isRadical_iff_pow_one_lt 2 (by omega)]
  intro x hx
  simp only [IsTopologicallyNilpotent.mem_topologicalNilradical_iff,
    isTopologicallyNilpotent_iff_forall_ideal] at hx ⊢
  intro J hJ
  obtain ⟨n, hn⟩ := hx J hJ
  refine ⟨2 * n, fun m hm ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa [pow_add] using J.mul_mem_right _ (by simpa [pow_mul] using hn n (by simp))

add_to_stacks 0AMW "part (1)" IsTopologicallyNilpotent.map
add_to_sga "3 VIIB 0.1.3" "more general" IsTopologicallyNilpotent.map

/-- Extending an ideal consisting of topologically nilpotent elements along a continuous
ring homomorphism and taking its closure still gives an ideal consisting of topologically
nilpotent elements. -/
@[stacks 0AMW "part (2)", sga "3 VIIB 0.1.3" "r(A) ↦ r(B)"]
public lemma closure_map_le_topologicalNilradical
    {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    [IsLinearTopology A A] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ)
    (I : Ideal A) (hI : I ≤ topologicalNilradical A) :
    Ideal.closure (I.map φ) ≤ topologicalNilradical B := fun _ hx ↦
  (isClosed_topologicalNilradical (B := B)).closure_subset
    (closure_mono (show I.map φ ≤ topologicalNilradical B from
      Ideal.map_le_iff_le_comap.mpr fun _ hz ↦ IsTopologicallyNilpotent.map hφ (hI hz)) hx)

end

section

/-- Addition is continuous when translates of additive subgroups form a neighborhood basis. -/
@[stacks 0AMR "addition_continuous"]
public theorem continuous_add_of_hasBasis_addSubgroup
    {M ι : Type*} [AddCommGroup M] [TopologicalSpace M]
    (Mμ : ι → AddSubgroup M)
    (hbasis : ∀ x : M, (nhds x).HasBasis (fun _ : ι => True)
      (fun μ => (fun y : M => x + y) '' (Mμ μ : Set M))) :
    Continuous (fun p : M × M => p.1 + p.2) :=
  let hzero : (nhds (0 : M)).HasBasis (fun _ : ι => True) (fun μ => (Mμ μ : Set M)) :=
    by simpa only [zero_add, Set.image_id'] using hbasis (0 : M)
  let : IsTopologicalAddGroup M :=
    IsTopologicalAddGroup.of_comm_of_nhds_zero
      ((hzero.prod_self.tendsto_iff hzero).2
        (fun μ hμ => ⟨μ, hμ, fun p hp => AddSubgroup.add_mem (Mμ μ) hp.1 hp.2⟩))
      ((hzero.tendsto_iff hzero).2
        (fun μ hμ => ⟨μ, hμ, fun x hx => AddSubgroup.neg_mem (Mμ μ) hx⟩))
      (fun x => (hbasis x).eq_of_same_basis (hzero.map (x + ·)))
  continuous_add

end

section

/-- Every open ideal in the target of a continuous ring homomorphism contains the extension
of an open ideal from the source. -/
@[stacks 0AMR "continuous_ring_map_open_ideal",
  ega "0 19.0.3" "𝔍B ⊂ 𝔎 clause",
  ega "0 7.7.5" "existence of open J"]
public theorem exists_isOpen_ideal_map_le {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (f : R →+* S) (hf : Continuous f)
    (J : Ideal S) (hJ : IsOpen (J : Set S)) :
    ∃ I : Ideal R, IsOpen (I : Set R) ∧ Ideal.map f I ≤ J :=
  ⟨J.comap f, IsOpen.preimage hf hJ, Ideal.map_comap_le⟩

end

section

add_to_stacks 0AI3 "admissible_recall" TopologicalRing.IsAdmissible

end

section

add_to_stacks 0AI3 "weak_admissibility" TopologicalRing.IsWeakIdealOfDefinition
add_to_stacks 0AI3 "weak_admissibility" TopologicalRing.IsWeaklyAdmissible

end

section

/-- The intersection of a weak ideal of definition with an open ideal is a weak ideal of
definition. -/
@[stacks 0AI3 "intersection"]
public lemma isWeakIdealOfDefinition_inf_of_isOpen_right {A : Type*} [CommRing A]
    [TopologicalSpace A] {I J : Ideal A} (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : IsOpen (J : Set A)) : TopologicalRing.IsWeakIdealOfDefinition (I ⊓ J) :=
  ⟨hI.1.inter hJ, fun x hx ↦ hI.2 x hx.1⟩

end

section

open Filter


/-- In a weakly admissible linearly topologized ring, its weak ideals of definition form a
fundamental system of neighborhoods of zero. -/
@[stacks 0AI3 "weak_basis"]
public lemma hasBasis_nhds_zero_isWeakIdealOfDefinition
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A) :
    (nhds (0 : A)).HasBasis
      (fun I : Ideal A ↦ TopologicalRing.IsWeakIdealOfDefinition I)
      (fun I : Ideal A ↦ (I : Set A)) :=
  IsLinearTopology.hasBasis_open_ideal.to_hasBasis
    (fun J hJ ↦ ⟨hA.1.choose ⊓ J,
      isWeakIdealOfDefinition_inf_of_isOpen_right hA.1.choose_spec hJ, fun _ hx ↦ hx.2⟩)
    (fun I hI ↦ ⟨I, hI.1, subset_rfl⟩)

end

end TopologicalRing

end
