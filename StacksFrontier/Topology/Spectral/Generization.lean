module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Common generizations and separation in a spectral space (Stacks 0904)

Let `X` be a spectral space and `x y : X`. Then either some point `z` specializes to both `x`
and `y`, so that `x` and `y` both lie in `closure {z}`, or `x` and `y` admit disjoint open
neighbourhoods. Specialization is Mathlib's `Specializes` (notation `⤳`), and a spectral space
is Mathlib's `SpectralSpace`: Kolmogorov, quasi-compact, quasi-sober, quasi-separated, with a
basis of quasi-compact opens.

The proof is the standard compactness argument in the constructible topology. Consider the
family of sets `U ∩ V` indexed by the pairs consisting of a quasi-compact open neighbourhood
`U` of `x` and a quasi-compact open neighbourhood `V` of `y`. If some such pair is disjoint we
are in the second case. Otherwise every member of the family is nonempty; each is a
quasi-compact open, because a quasi-separated space has quasi-compact pairwise intersections
of quasi-compact opens, and hence is closed for the constructible topology; and the family is
directed downwards, since quasi-compact opens are stable under intersection. The constructible
topology on a spectral space is quasi-compact
(`compactSpace_withConstructibleTopology`, the quasi-compactness half of Stacks 0901), so a
directed family of nonempty constructible-closed sets has nonempty intersection. Any point `z`
of the intersection lies in every quasi-compact open neighbourhood of `x` and of `y`, and since
the quasi-compact opens form a basis this forces `z ⤳ x` and `z ⤳ y`.

The two alternatives are in fact mutually exclusive — a common generization lies in every open
neighbourhood of both points — but the source only asserts the disjunction, and that is what is
stated here. The second alternative is phrased with `Disjoint`, which for sets is `U ∩ V = ∅`.
-/

@[expose] public section

open Set Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- A quasi-compact open subset of `X` is closed for the constructible topology: it is closed
with quasi-compact complement *after* passing to complements, so `Uᶜ` is a subbasic
constructible open. -/
lemma isClosed_constructibleTopology_of_isCompact_of_isOpen {U : Set X}
    (hUc : IsCompact U) (hUo : IsOpen U) :
    IsClosed[constructibleTopology X] U :=
  (@isOpen_compl_iff X U (constructibleTopology X)).mp <|
    IsCompact.isOpen_constructibleTopology_of_isClosed (s := Uᶜ)
      (by rwa [compl_compl]) hUo.isClosed_compl

/-- If `z` belongs to every quasi-compact open neighbourhood of `x`, then `z` specializes to
`x`. Only the fact that the quasi-compact opens form a basis is used. -/
lemma specializes_of_forall_isOpen_isCompact [PrespectralSpace X] {x z : X}
    (h : ∀ U : Set X, IsOpen U → IsCompact U → x ∈ U → z ∈ U) : z ⤳ x := by
  rw [specializes_iff_forall_open]
  intro s hs hxs
  obtain ⟨U, ⟨hUo, hUc⟩, hxU, hUs⟩ :=
    PrespectralSpace.isTopologicalBasis.isOpen_iff.mp hs x hxs
  exact hUs (h U hUo hUc hxU)

/-- A spectral space is quasi-compact in its constructible topology. -/
alias compactSpace_constructibleTopology := _root_.compactSpace_constructibleTopology

/-- A downward-directed family of nonempty sets that are closed for the constructible topology
of a spectral space has nonempty intersection: the constructible topology is quasi-compact, so
these sets are constructible-compact. -/
lemma nonempty_iInter_of_directed_of_isClosed_constructibleTopology [SpectralSpace X]
    {ι : Type*} [Nonempty ι] (F : ι → Set X) (hne : ∀ i, (F i).Nonempty)
    (hclosed : ∀ i, IsClosed[constructibleTopology X] (F i))
    (hdir : Directed (· ⊇ ·) F) :
    (⋂ i, F i).Nonempty :=
  have hcs : @CompactSpace X (constructibleTopology X) := compactSpace_constructibleTopology X
  @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed X (constructibleTopology X)
    ι _ F hdir hne
    (fun i => @IsClosed.isCompact X (constructibleTopology X) (F i) hcs (hclosed i)) hclosed

/-- **Stacks 0904.** For any two points `x`, `y` of a spectral space, either there is a point
`z` specializing to both (equivalently, `x` and `y` both lie in `closure {z}`), or `x` and `y`
have disjoint open neighbourhoods. -/
@[stacks 0904]
theorem exists_specializes_or_exists_disjoint_nhds [SpectralSpace X] (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  by_cases h : ∃ U V : Set X, IsOpen U ∧ IsCompact U ∧ x ∈ U ∧
      IsOpen V ∧ IsCompact V ∧ y ∈ V ∧ Disjoint U V
  · obtain ⟨U, V, hUo, -, hxU, hVo, -, hyV, hUV⟩ := h
    exact Or.inr ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩
  -- Otherwise every pair of quasi-compact open neighbourhoods of `x` and `y` meets.
  push Not at h
  left
  -- Index the family by such pairs; its members are the intersections `U ∩ V`.
  set ι := { p : Set X × Set X // IsOpen p.1 ∧ IsCompact p.1 ∧ x ∈ p.1 ∧
    IsOpen p.2 ∧ IsCompact p.2 ∧ y ∈ p.2 }
  set F : ι → Set X := fun p => p.val.1 ∩ p.val.2
  have hne : Nonempty ι :=
    ⟨⟨(univ, univ), isOpen_univ, isCompact_univ, mem_univ x,
      isOpen_univ, isCompact_univ, mem_univ y⟩⟩
  have hFne : ∀ i : ι, (F i).Nonempty := by
    rintro ⟨⟨U, V⟩, hUo, hUc, hxU, hVo, hVc, hyV⟩
    exact not_disjoint_iff_nonempty_inter.mp (h U V hUo hUc hxU hVo hVc hyV)
  have hFclosed : ∀ i : ι, IsClosed[constructibleTopology X] (F i) := by
    rintro ⟨⟨U, V⟩, hUo, hUc, -, hVo, hVc, -⟩
    exact isClosed_constructibleTopology_of_isCompact_of_isOpen
      (QuasiSeparatedSpace.inter_isCompact U V hUo hUc hVo hVc) (hUo.inter hVo)
  have hFdir : Directed (· ⊇ ·) F := by
    rintro ⟨⟨U₁, V₁⟩, hU₁o, hU₁c, hxU₁, hV₁o, hV₁c, hyV₁⟩
      ⟨⟨U₂, V₂⟩, hU₂o, hU₂c, hxU₂, hV₂o, hV₂c, hyV₂⟩
    refine ⟨⟨(U₁ ∩ U₂, V₁ ∩ V₂), hU₁o.inter hU₂o,
      QuasiSeparatedSpace.inter_isCompact U₁ U₂ hU₁o hU₁c hU₂o hU₂c, mem_inter hxU₁ hxU₂,
      hV₁o.inter hV₂o,
      QuasiSeparatedSpace.inter_isCompact V₁ V₂ hV₁o hV₁c hV₂o hV₂c, mem_inter hyV₁ hyV₂⟩,
      ?_, ?_⟩
    · rintro z ⟨⟨hzU₁, -⟩, hzV₁, -⟩
      exact ⟨hzU₁, hzV₁⟩
    · rintro z ⟨⟨-, hzU₂⟩, -, hzV₂⟩
      exact ⟨hzU₂, hzV₂⟩
  obtain ⟨z, hz⟩ :=
    nonempty_iInter_of_directed_of_isClosed_constructibleTopology F hFne hFclosed hFdir
  refine ⟨z, specializes_of_forall_isOpen_isCompact ?_,
    specializes_of_forall_isOpen_isCompact ?_⟩
  · intro U hUo hUc hxU
    exact (mem_iInter.mp hz
      ⟨(U, univ), hUo, hUc, hxU, isOpen_univ, isCompact_univ, mem_univ y⟩).1
  · intro V hVo hVc hyV
    exact (mem_iInter.mp hz
      ⟨(univ, V), isOpen_univ, isCompact_univ, mem_univ x, hVo, hVc, hyV⟩).2

end Topology
