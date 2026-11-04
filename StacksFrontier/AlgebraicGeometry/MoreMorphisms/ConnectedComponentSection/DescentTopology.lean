module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructible

/-!
# Topological inputs to Stacks Tag 057I

Tag 057I produces a quasi-compact open of the source by descending an open subset of a
multisection pullback along a finite locally free map. The purely topological content of that
descent is collected here, away from the algebraic geometry: that a saturated open descends
along an open map, that a closed map separates a fibre from the complement of an open
neighbourhood of it, that a constructible subset of a compact prespectral quasi-separated space
is compact, and that a space embedding onto a connected range is connected.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.open_image_eq_of_descent_relation` descends an open
  subset compatible with a relation along the map the relation covers.
* `AlgebraicGeometry.ConnectedComponentSection.exists_open_neighborhood_preimage_subset` is the
  standard consequence of properness: a fibre contained in an open set is so on a neighbourhood.
* `AlgebraicGeometry.ConnectedComponentSection.isCompact_of_isConstructible` and
  `isCompact_inter_compact_open_of_isLocallyConstructible` turn constructibility into compactness.
* `AlgebraicGeometry.ConnectedComponentSection.connectedSpace_of_isEmbedding_range_connected`
  transfers connectedness along an embedding.

## Implementation notes

`AlgebraicGeometry.ConnectedComponentSection.isCompact_of_isConstructible` is proved by the
induction principle `IsConstructible.induction_of_isTopologicalBasis` over the basis of compact
opens supplied by `PrespectralSpace`. That basis is indexed by the subtype of compact opens
rather than by a set of sets, so the hypothesis of the induction principle is met after rewriting
the range of the coercion.

## References

* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open Topology TopologicalSpace

namespace AlgebraicGeometry.ConnectedComponentSection

/-- An open subset `A` of `E` whose membership is invariant under a relation `R` covering the
fibres of `p` has open image, and is the full preimage of that image. -/
theorem open_image_eq_of_descent_relation
    {E B R : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace R]
    (p : E → B) (r₀ r₁ : R → E) (A : Set E)
    (hp : IsOpenMap p) (hA : IsOpen A)
    (hcompat : ∀ r, r₀ r ∈ A ↔ r₁ r ∈ A)
    (hrel : ∀ e₀ e₁, p e₀ = p e₁ → ∃ r, r₀ r = e₀ ∧ r₁ r = e₁) :
    IsOpen (p '' A) ∧ p ⁻¹' (p '' A) = A := by
  refine ⟨hp A hA, Set.ext fun e => ⟨?_, fun he => ⟨e, he, rfl⟩⟩⟩
  rintro ⟨e₀, he₀, heq⟩
  obtain ⟨r, hr₀, hr₁⟩ := hrel e₀ e heq
  exact hr₁ ▸ (hcompat r).mp (hr₀ ▸ he₀)

/-- If `p` is a closed map and the fibre of `p` over `y` is contained in an open set `W`, then
already the preimage of a neighbourhood of `y` is contained in `W`. -/
theorem exists_open_neighborhood_preimage_subset
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsClosedMap p) (y : B) (W : Set E) (hW : IsOpen W)
    (hy : ∀ e, p e = y → e ∈ W) :
    ∃ V : Set B, IsOpen V ∧ y ∈ V ∧ p ⁻¹' V ⊆ W := by
  refine ⟨(p '' Wᶜ)ᶜ, (hp Wᶜ hW.isClosed_compl).isOpen_compl, ?_,
    fun e he => Classical.byContradiction fun heW => he ⟨e, heW, rfl⟩⟩
  rintro ⟨e, he, hepy⟩
  exact he (hy e hepy)

/-- A constructible subset of a compact, prespectral, quasi-separated space is compact. -/
theorem isCompact_of_isConstructible
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [PrespectralSpace T] [QuasiSeparatedSpace T]
    {A : Set T} (hA : IsConstructible A) : IsCompact A := by
  let I := {U : Set T // IsOpen U ∧ IsCompact U}
  have : Nonempty I := ⟨⟨∅, isOpen_empty, isCompact_empty⟩⟩
  have hb : IsTopologicalBasis (Set.range (fun U : I => (U : Set T))) := by
    rw [Subtype.range_coe_subtype]
    exact PrespectralSpace.isTopologicalBasis
  exact IsConstructible.induction_of_isTopologicalBasis
    (P := fun s _ => IsCompact s) (fun U : I => (U : Set T)) hb
    (fun U => U.property.2)
    (fun i s _ => i.property.2.diff (isOpen_biUnion fun j _ => j.property.1))
    (fun _ _ _ _ hs ht => hs.union ht) A hA

/-- The intersection of a locally constructible subset with a quasi-separated compact open is
compact. -/
theorem isCompact_inter_compact_open_of_isLocallyConstructible
    {T : Type*} [TopologicalSpace T] [PrespectralSpace T]
    (A W : Set T) (hA : IsLocallyConstructible A)
    (hWopen : IsOpen W) (hWcompact : IsCompact W)
    (hWqs : QuasiSeparatedSpace W) : IsCompact (A ∩ W) := by
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWcompact
  have : PrespectralSpace W := hWopen.isOpenEmbedding_subtypeVal.prespectralSpace
  simpa only [Subtype.image_preimage_coe, Set.inter_comm] using
    (isCompact_of_isConstructible
      (hA.preimage_of_isOpenEmbedding hWopen.isOpenEmbedding_subtypeVal).isConstructible).image
      continuous_subtype_val

/-- A space which embeds onto a connected subset of another space is connected. -/
theorem connectedSpace_of_isEmbedding_range_connected
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (i : S → T) (hi : IsEmbedding i)
    (h : IsConnected (Set.range i)) : ConnectedSpace S := by
  obtain ⟨_, s, rfl⟩ := h.1
  exact connectedSpace_iff_univ.mpr ⟨⟨s, trivial⟩,
    (hi.isInducing.isPreconnected_image (s := Set.univ)).mp
      (by simpa only [Set.image_univ] using h.2)⟩

end AlgebraicGeometry.ConnectedComponentSection

end
