module

public import StacksFrontier.Topology.Spectral.InverseLimits
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Quasi-compact open neighbourhoods of a quasi-compact subset

Let `E` be a quasi-compact subset of a spectral space `X`. The quasi-compact open
neighbourhoods of `E` form a codirected poset, every member of it is a spectral space, and the
set of points which specialize to a point of `E` is its inverse limit.

## Main definitions

* `SpectralSubset.CompactOpenNeighborhood` is the poset of quasi-compact open neighbourhoods of
  a subset, ordered by inclusion.
* `SpectralSubset.neighborhoodDiagram` presents that poset as a cofiltered diagram of spectral
  spaces and spectral maps.

## Main results

* `SpectralSubset.CompactOpenNeighborhood.instSpectralSpace`: a quasi-compact open
  neighbourhood in a spectral space is itself spectral.
* `SpectralSubset.generalizationsOf_eq_iInter_compactOpenNeighborhood`: the points specializing
  to `E` are exactly the intersection of the quasi-compact open neighbourhoods of `E`.
* `SpectralSubset.exists_homeomorph_invLimit_compactOpenNeighborhood`: that intersection is the
  inverse limit of the neighbourhoods, by the canonical homeomorphism.

## Implementation notes

The index poset is a subtype of `Set X`, so it inherits its order and hence its
`SmallCategory` structure from `Set X`; a morphism `U ⟶ V` is an inclusion `U ⊆ V`, which makes
the diagram of inclusions covariant and the poset codirected rather than directed. The inverse
limit is the explicit compatible-family model `SpectralSubset.InvLimit`, and the stated
homeomorphism is canonical: each of its coordinates is the inclusion of the generalization set
into the corresponding neighbourhood. Spectrality of a member does not need the compactness
of `E`.

## References

* [Stacks Project, Lemma 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Lemma 0902](https://stacks.math.columbia.edu/tag/0902)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace SpectralSubset

variable {X : Type u} [TopologicalSpace X]

/-- The quasi-compact open neighbourhoods of a subset `E`, ordered by inclusion. -/
abbrev CompactOpenNeighborhood (E : Set X) :=
  { U : Set X // IsOpen U ∧ IsCompact U ∧ E ⊆ U }

namespace CompactOpenNeighborhood

variable (E : Set X)

/-- The whole space is a quasi-compact open neighbourhood of any subset. -/
instance [CompactSpace X] : Nonempty (CompactOpenNeighborhood E) :=
  ⟨⟨Set.univ, isOpen_univ, isCompact_univ, Set.subset_univ E⟩⟩

/-- The quasi-compact open neighbourhoods of `E` are codirected: the intersection of two of
them is again one, using that a spectral space is quasi-separated. -/
instance [QuasiSeparatedSpace X] : IsCodirectedOrder (CompactOpenNeighborhood E) :=
  ⟨fun U V ↦
    ⟨⟨(U : Set X) ∩ (V : Set X), U.2.1.inter V.2.1,
        QuasiSeparatedSpace.inter_isCompact _ _ U.2.1 U.2.2.1 V.2.1 V.2.2.1,
        fun _ hx ↦ ⟨U.2.2.2 hx, V.2.2.2 hx⟩⟩,
      Set.inter_subset_left, Set.inter_subset_right⟩⟩

/-- **Stacks 0902 for a quasi-compact open.** A quasi-compact open neighbourhood in a spectral
space is itself a spectral space. This does not use compactness of `E`. -/
instance instSpectralSpace [SpectralSpace X] (U : CompactOpenNeighborhood E) :
    SpectralSpace (U : Set X) :=
  letI : CompactSpace (U : Set X) := isCompact_iff_compactSpace.mp U.2.2.1
  Topology.IsOpenEmbedding.spectralSpace U.2.1.isOpenEmbedding_subtypeVal

end CompactOpenNeighborhood

/-- The points which specialize to a point of a quasi-compact set `E` are exactly the
intersection of the quasi-compact open neighbourhoods of `E`. -/
theorem generalizationsOf_eq_iInter_compactOpenNeighborhood [SpectralSpace X]
    (E : Set X) (hE : IsCompact E) :
    generalizationsOf E =
      ⋂ U : CompactOpenNeighborhood E, (U : Set X) := by
  obtain ⟨S, hWS, hS⟩ :=
    isInterCompactOpen_of_isGeneralizationsOfCompact (generalizationsOf E) ⟨E, hE, rfl⟩
  ext x
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ Set.mem_iInter.mpr fun U ↦ hxy.mem_open U.2.1 (U.2.2.2 hy),
    fun hx ↦ ?_⟩
  rw [hWS]
  exact Set.mem_sInter.mpr fun s hs ↦ Set.mem_iInter.mp hx ⟨s, (hS s hs).1, (hS s hs).2,
    fun y hy ↦ Set.mem_sInter.mp (hWS ▸ ⟨y, hy, specializes_refl y⟩) s hs⟩

/-- **Stacks 0A31 for the neighbourhood system.** The points specializing to a quasi-compact
subset `E` of a spectral space form the inverse limit of the quasi-compact open neighbourhoods
of `E`. The coordinate condition characterizes the homeomorphism as the canonical one. -/
theorem exists_homeomorph_invLimit_compactOpenNeighborhood [SpectralSpace X]
    (E : Set X) (hE : IsCompact E) :
    ∃ φ : generalizationsOf E ≃ₜ
        InvLimit (fun U : CompactOpenNeighborhood E ↦ (U : Set X)),
      ∀ (w : generalizationsOf E) (U : CompactOpenNeighborhood E),
        (((φ w).1 U : X)) = (w : X) :=
  exists_homeomorph_invLimit (fun U : CompactOpenNeighborhood E ↦ (U : Set X))
    (fun U V ↦ (directed_of (· ≥ ·) U V).imp
      fun _ h ↦ Set.subset_inter h.1 h.2)
    (generalizationsOf E) (generalizationsOf_eq_iInter_compactOpenNeighborhood E hE)

/-- On a quasi-separated space, the inclusion of a quasi-compact open subset into a larger open
subset is a spectral map. -/
theorem isSpectralMap_inclusion [QuasiSeparatedSpace X] {U V : Set X}
    (hU : IsOpen U) (hUc : IsCompact U) (hV : IsOpen V) (hUV : U ⊆ V) :
    IsSpectralMap (fun x : U ↦ (⟨x.1, hUV x.2⟩ : V)) := by
  refine ⟨Continuous.subtype_mk continuous_subtype_val fun x ↦ hUV x.2, fun W hWo hWc ↦ ?_⟩
  rw [hU.isOpenEmbedding_subtypeVal.isEmbedding.isCompact_iff]
  convert QuasiSeparatedSpace.inter_isCompact _ _ hU hUc (hV.isOpenMap_subtype_val W hWo)
    (hWc.image continuous_subtype_val) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, _, hy, rfl⟩
  · rintro ⟨hxU, w, hw, rfl⟩
    exact ⟨⟨w.1, hxU⟩, by simpa using hw, rfl⟩

/-- The quasi-compact open neighbourhoods of a quasi-compact subset of a spectral space, as a
cofiltered diagram of spectral spaces and spectral maps. A morphism `U ⟶ V` of the index poset
is an inclusion `U ⊆ V`, and the diagram sends it to that inclusion of subspaces. -/
def neighborhoodDiagram [SpectralSpace X] (E : Set X) :
    SpectralDiagram.{u, u} (CompactOpenNeighborhood E) where
  F :=
    { obj := fun U ↦ TopCat.of (U : Set X)
      map := fun {U V} f ↦ TopCat.ofHom
        ⟨fun x ↦ (⟨x.1, (leOfHom f) x.2⟩ : (V : Set X)),
          Continuous.subtype_mk continuous_subtype_val fun x ↦ (leOfHom f) x.2⟩
      map_id := fun _ ↦ by apply TopCat.hom_ext; ext x; rfl
      map_comp := fun _ _ ↦ by apply TopCat.hom_ext; ext x; rfl }
  isSpectralSpace := fun U ↦ CompactOpenNeighborhood.instSpectralSpace E U
  isSpectralMap := fun {U V} f ↦
    isSpectralMap_inclusion U.2.1 U.2.2.1 V.2.1 (leOfHom f)

end SpectralSubset

end
