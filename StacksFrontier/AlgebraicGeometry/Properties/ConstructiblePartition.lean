module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Stratification.LocallyFiniteFamily
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Constructible.LocallyClosedQuasiCompact
public import StacksFrontier.Topology.Constructible.NormalForm
public import StacksFrontier.Topology.Spectral.AsDirectedInverseLimit
public import StacksFrontier.Topology.Stratification.Partition

/-!
# Locally finite partitions and locally constructible parts

A partition of a scheme into retrocompact parts is locally finite exactly when every part is
locally constructible.

## Main results

* `AlgebraicGeometry.locallyFinite_iff_parts_isLocallyConstructible` characterizes local
  finiteness of a partition with retrocompact parts.

## Implementation notes

The parts are indexed by the subtype of members of the collection defining the partition. This
removes irrelevant repetitions of parts while retaining the indexing needed to speak of local
finiteness, which is Mathlib's `LocallyFinite`.

## References

* [Stacks Project, Tag 0F2M](https://stacks.math.columbia.edu/tag/0F2M)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- A partition of a spectral space into constructible sets has only finitely many nonempty
parts. -/
private lemma finite_of_constructible_partition
    {Y I : Type*} [TopologicalSpace Y] [SpectralSpace Y]
    (E : I → Set Y) (hE : ∀ i, Topology.IsConstructible (E i))
    (hcover : ∀ y, ∃ i, y ∈ E i)
    (hdisjoint : ∀ i j y, y ∈ E i → y ∈ E j → i = j) :
    {i | (E i).Nonempty}.Finite := by
  let O : I → Set (WithConstructibleTopology Y) := fun i ↦ WithTopology.ofTopology ⁻¹' E i
  have hO : ∀ i, IsOpen (O i) := by
    intro i
    apply WithConstructibleTopology.isOpen_iff.mpr
    show @IsOpen Y (constructibleTopology Y) (E i)
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem (hE i)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO (by
    intro y _
    obtain ⟨i, hi⟩ := hcover (WithTopology.ofTopology y)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine t.finite_toSet.subset ?_
  rintro i ⟨y, hy⟩
  obtain ⟨j, hjt, hyj⟩ := Set.mem_iUnion₂.mp
    (ht (Set.mem_univ (WithTopology.toTopology (constructibleTopology Y) y)))
  simpa [hdisjoint i j y hy hyj] using hjt

/-- In a partition all of whose nonempty parts are listed by a finite set `t`, the complement
of one part is the union of the others. -/
private lemma compl_part_eq_biUnion_other_parts
    {Y I : Type*} [TopologicalSpace Y] [DecidableEq I] (E : I → Set Y)
    (hcover : ∀ y, ∃ i, y ∈ E i)
    (hdisjoint : ∀ i j y, y ∈ E i → y ∈ E j → i = j)
    (i : I) (t : Finset I) (ht : ∀ j, (E j).Nonempty → j ∈ t) :
    (E i)ᶜ = ⋃ j ∈ t.filter (· ≠ i), E j := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨j, hyj⟩ := hcover y
    have hji : j ≠ i := fun h ↦ hy (h ▸ hyj)
    exact Set.mem_iUnion₂.mpr ⟨j, by simp [ht j ⟨y, hyj⟩, hji], hyj⟩
  · intro hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
    exact fun hyi ↦ (Finset.mem_filter.mp hj).2 (hdisjoint j i y hyj hyi)

/-- The preimages of the parts of a topological partition under any map cover the domain and
are pairwise disjoint. -/
private lemma preimage_partition_cover_disjoint
    {X Y : Type*} [TopologicalSpace X] {P : Set (Set X)} (hP : IsTopologicalPartition P)
    (f : Y → X) :
    (∀ y, ∃ T : P, y ∈ f ⁻¹' (T : Set X)) ∧
      ∀ (T V : P) y, y ∈ f ⁻¹' (T : Set X) → y ∈ f ⁻¹' (V : Set X) → T = V := by
  refine ⟨fun y ↦ ?_, fun T V y hyT hyV ↦ ?_⟩
  · obtain ⟨T, ⟨hTP, hyT⟩, -⟩ := hP.1.2 (f y)
    exact ⟨⟨T, hTP⟩, hyT⟩
  · exact Subtype.ext ((hP.1.2 (f y)).unique ⟨T.2, hyT⟩ ⟨V.2, hyV⟩)

/-- In a locally finite partition of a scheme into retrocompact parts, every part is locally
constructible. -/
lemma isLocallyConstructible_of_locallyFinite
    {X : Scheme.{u}} {P : Set (Set X)} (hP : IsTopologicalPartition P)
    (hP_retrocompact : ∀ S ∈ P, IsRetrocompact S)
    (hlocal : LocallyFinite (fun S : P ↦ (S : Set X))) (S : Set X) (hSP : S ∈ P) :
    Topology.IsLocallyConstructible S := by
  classical
  rw [isLocallyConstructible_iff_forall_affineOpens]
  intro U
  have : SpectralSpace U := spectralSpace_affineOpen U
  have hF : {T : P | ((T : Set X) ∩ (U.1 : Set X)).Nonempty}.Finite :=
    hlocal.finite_nonempty_inter_compact U.2.isCompact
  let E : P → Set U := fun T ↦ Subtype.val ⁻¹' (T : Set X)
  obtain ⟨hcover, hdisjoint⟩ :=
    preimage_partition_cover_disjoint hP (Subtype.val : (U.1 : Set X) → X)
  have ht : ∀ T, (E T).Nonempty → T ∈ hF.toFinset := fun T ⟨x, hx⟩ ↦
    hF.mem_toFinset.mpr ⟨x.1, hx, x.2⟩
  have hcompRetro : IsRetrocompact (E ⟨S, hSP⟩)ᶜ := by
    rw [compl_part_eq_biUnion_other_parts E hcover hdisjoint _ _ ht]
    exact IsRetrocompact.biUnion (Set.toFinite _) fun T _ ↦
      IsRetrocompact.preimage_of_isOpenEmbedding U.1.ι.isOpenEmbedding
        (hP_retrocompact T T.2)
  exact Topology.isConstructible_iff_isConstructibleStratified.mpr <| main_theorem0F2K
    (B := {V | IsOpen V ∧ IsCompact V}) (T := E ⟨S, hSP⟩)
    PrespectralSpace.isTopologicalBasis (fun _ hV ↦ hV.2)
    (fun _ hV _ hW ↦ hV.2.inter_of_isOpen hW.2 hV.1 hW.1)
    ((hP.2 S hSP).preimage U.1.ι.isOpenEmbedding.continuous)
    (IsRetrocompact.preimage_of_isOpenEmbedding U.1.ι.isOpenEmbedding
      (hP_retrocompact S hSP)).isCompact
    hcompRetro

/-- A partition of a scheme into locally constructible parts is locally finite. -/
lemma locallyFinite_of_forall_isLocallyConstructible
    {X : Scheme.{u}} {P : Set (Set X)} (hP : IsTopologicalPartition P)
    (hparts : ∀ S ∈ P, Topology.IsLocallyConstructible S) :
    LocallyFinite (fun S : P ↦ (S : Set X)) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let AU : X.affineOpens := ⟨U, hU⟩
  refine ⟨U, U.2.mem_nhds hxU, ?_⟩
  have : SpectralSpace AU := spectralSpace_affineOpen AU
  let E : P → Set AU := fun T ↦ Subtype.val ⁻¹' (T : Set X)
  have hconstruct : ∀ T, Topology.IsConstructible (E T) := fun T ↦
    (isLocallyConstructible_iff_forall_affineOpens (T : Set X)).mp (hparts T T.2) AU
  obtain ⟨hcover, hdisjoint⟩ :=
    preimage_partition_cover_disjoint hP (Subtype.val : (AU.1 : Set X) → X)
  exact (finite_of_constructible_partition E hconstruct hcover hdisjoint).subset
    fun T ⟨y, hyT, hyU⟩ ↦ ⟨⟨y, hyU⟩, hyT⟩

/-- A partition of a scheme into retrocompact parts is locally finite if and only if all its
parts are locally constructible. -/
@[stacks 0F2M]
public lemma locallyFinite_iff_parts_isLocallyConstructible
    {X : Scheme.{u}} {P : Set (Set X)} (hP : IsTopologicalPartition P)
    (hP_retrocompact : ∀ S ∈ P, IsRetrocompact S) :
    LocallyFinite (fun S : P ↦ (S : Set X)) ↔
      ∀ S ∈ P, Topology.IsLocallyConstructible S :=
  ⟨isLocallyConstructible_of_locallyFinite hP hP_retrocompact,
    locallyFinite_of_forall_isLocallyConstructible hP⟩

end AlgebraicGeometry
