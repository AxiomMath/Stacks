module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCoveringAxioms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcSite

/-!
# The quasi-compact topology on Hausdorff, locally quasi-compact spaces

Let `LC` be the category of Hausdorff, locally quasi-compact topological spaces and continuous
maps. A family `{fᵢ : Xᵢ → X}` of morphisms of `LC` is a *qc covering* if every point of `X` has
a neighbourhood of the form `⋃ⱼ fᵢⱼ(Eⱼ)` for finitely many indices `iⱼ` and quasi-compact subsets
`Eⱼ ⊆ Xᵢⱼ`. The three axioms of a site for these coverings — isomorphisms cover, coverings
compose, coverings are stable under base change — hold, so `LC` with its qc coverings is a site.
This topology is stronger than the usual topology of open coverings: since `X` is locally
quasi-compact, every point of `X` has a quasi-compact neighbourhood inside a member of a given
open covering, so every open covering is a qc covering.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactHausdorff.qcPrecoverage`: the qc coverings of `LC`, as a
  precoverage.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.qcPretopology`: `LC` with its qc coverings,
  as a site.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.qcTopology`: the Grothendieck topology it
  generates.

## Main results

* `Stacks.Topology.LocallyQuasiCompactHausdorff.ofArrows_mem_qcPrecoverage_iff`: a family of
  morphisms of `LC` belongs to `qcPrecoverage` exactly when it is a qc covering in the sense of
  `IsQcCovering`.
* `IsQcCovering.of_isOpenEmbedding`: a jointly surjective family of open embeddings into a
  locally quasi-compact space is a qc covering, and `IsQcCovering.of_iSup_eq_top`: in particular
  an open covering `X = ⋃ Uᵢ` gives a qc covering `{Uᵢ → X}`.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.comap_precoverage_le_qcPrecoverage` and
  `toGrothendieck_comap_precoverage_le_qcTopology`: the open-covering topology of `LC` is
  coarser than the qc topology.

## Implementation notes

The category `LC` has a proper class of objects. Here this is expressed by universes: the
objects of `LocallyQuasiCompactHausdorff.{u}` form a type in `Type (u + 1)` while its morphisms
form types in `Type u`, so a precoverage and a Grothendieck topology on it make sense without
any cutoff. The cutoff of Stacks 09X2 is needed only once sheaves are to be sheafified; it is
carried out in `Stacks.Topology.LocallyQuasiCompactQcSite`.

A covering presieve is described through the *images* `g '' E` of quasi-compact sets under its
arrows, rather than through an indexing of its arrows. That description does not depend on how
the arrows of a presieve are indexed, and `ofArrows_mem_qcPrecoverage_iff` identifies it with the
indexed condition `IsQcCovering` of Stacks 09X0.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 09X0](https://stacks.math.columbia.edu/tag/09X0)
* [Stacks Project, Tag 09X1](https://stacks.math.columbia.edu/tag/09X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

/-- **An open covering is a qc covering.** A jointly surjective family of open embeddings into a
locally quasi-compact space is a qc covering: a point `x` lies in the image of some `fᵢ`, which
is open, so `x` has a quasi-compact neighbourhood `K` inside that image, and `K` is the image of
the quasi-compact set `fᵢ⁻¹(K)`. -/
@[stacks 09WY "an open covering of an object of LC is a qc covering"]
theorem IsQcCovering.of_isOpenEmbedding {ι : Type*} {X : ι → Type*} {Y : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] [LocallyCompactSpace Y]
    {f : ∀ i, X i → Y} (hf : ∀ i, IsOpenEmbedding (f i))
    (hsurj : ∀ y, ∃ i, y ∈ Set.range (f i)) : IsQcCovering f := by
  classical
  intro y
  obtain ⟨i, hi⟩ := hsurj y
  obtain ⟨K, hK, hKU, hKc⟩ :=
    local_compact_nhds ((hf i).isOpen_range.mem_nhds hi)
  refine ⟨{i}, fun j => if j = i then f j ⁻¹' K else ∅, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton.mp hj]
    simp only [↓reduceIte]
    exact ((hf i).isInducing.isCompact_preimage_iff hKU).2 hKc
  · simpa [Set.image_preimage_eq_of_subset hKU] using hK

/-- **An open covering `X = ⋃ Uᵢ` gives a qc covering `{Uᵢ → X}`**, for a locally quasi-compact
space `X`. -/
@[stacks 09WY "an open covering of an object of LC is a qc covering"]
theorem IsQcCovering.of_iSup_eq_top {ι : Type*} {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] (U : ι → TopologicalSpace.Opens X) (hU : iSup U = ⊤) :
    IsQcCovering (fun i => (Subtype.val : U i → X)) :=
  IsQcCovering.of_isOpenEmbedding (fun i => (U i).isOpen.isOpenEmbedding_subtypeVal)
    fun x => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.symm ▸ trivial : x ∈ iSup U)
      exact ⟨i, ⟨x, hi⟩, rfl⟩

namespace Stacks.Topology.LocallyQuasiCompactHausdorff

/-- The qc coverings of `LC`, as a precoverage. A presieve `R` on `X` is covering when every
point of `X` has a neighbourhood which is a finite union of images `g '' E` of quasi-compact
sets `E` under arrows `g` of `R`. -/
def qcPrecoverage : Precoverage LocallyQuasiCompactHausdorff.{u} where
  coverings X := {R | ∀ x : X, ∃ s : Set (Set X), s.Finite ∧
    (∀ K ∈ s, ∃ (Y : LocallyQuasiCompactHausdorff.{u}) (g : Y ⟶ X), R g ∧
      ∃ E : Set Y, IsCompact E ∧ g.hom '' E = K) ∧ ⋃₀ s ∈ nhds x}

/-- A family of morphisms of `LC` whose presieve is a qc covering in the sense of
`qcPrecoverage` is a qc covering in the sense of Stacks 09X0. -/
theorem isQcCovering_of_ofArrows_mem_qcPrecoverage {ι : Type*}
    {X : LocallyQuasiCompactHausdorff.{u}} {Y : ι → LocallyQuasiCompactHausdorff.{u}}
    (f : ∀ i, Y i ⟶ X) (h : Presieve.ofArrows Y f ∈ qcPrecoverage X) :
    IsQcCovering (fun i => (f i).hom) := by
  classical
  intro x
  obtain ⟨s, hs, hK, hx⟩ := h x
  have hK' : ∀ K ∈ s, ∃ (i : ι) (E : Set (Y i)), IsCompact E ∧ (f i).hom '' E = K := by
    intro K hKs
    obtain ⟨Z, g, hg, E, hE, rfl⟩ := hK K hKs
    obtain ⟨i⟩ := hg
    exact ⟨i, E, hE, rfl⟩
  choose idx E hE himg using hK'
  let F (i : ι) : Set (Y i) :=
    ⋃ K ∈ hs.toFinset, if h : ∃ E : Set (Y i), IsCompact E ∧ (f i).hom '' E = K then
      h.choose else ∅
  refine ⟨hs.toFinset.attach.image (fun K => idx K.1 (hs.mem_toFinset.1 K.2)), F, ?_, ?_⟩
  · intro i _
    refine hs.toFinset.isCompact_biUnion fun K _ => ?_
    split_ifs with h
    · exact h.choose_spec.1
    · exact isCompact_empty
  · refine Filter.mem_of_superset hx ?_
    rintro z ⟨K, hKs, hzK⟩
    have hex : ∃ E' : Set (Y (idx K hKs)), IsCompact E' ∧ (f (idx K hKs)).hom '' E' = K :=
      ⟨E K hKs, hE K hKs, himg K hKs⟩
    rw [← hex.choose_spec.2] at hzK
    obtain ⟨w, hw, rfl⟩ := hzK
    simp only [Set.mem_iUnion]
    refine ⟨idx K hKs, Finset.mem_image.2 ⟨⟨K, hs.mem_toFinset.2 hKs⟩, Finset.mem_attach _ _,
      rfl⟩, w, ?_, rfl⟩
    simp only [F, Set.mem_iUnion]
    exact ⟨K, hs.mem_toFinset.2 hKs, by rwa [dite_eq_left hex]⟩

/-- A qc covering in the sense of Stacks 09X0 gives a presieve belonging to `qcPrecoverage`. -/
theorem ofArrows_mem_qcPrecoverage_of_isQcCovering {ι : Type*}
    {X : LocallyQuasiCompactHausdorff.{u}} {Y : ι → LocallyQuasiCompactHausdorff.{u}}
    (f : ∀ i, Y i ⟶ X) (h : IsQcCovering (fun i => (f i).hom)) :
    Presieve.ofArrows Y f ∈ qcPrecoverage X := by
  intro x
  obtain ⟨s, E, hE, hx⟩ := h x
  refine ⟨(fun i => (f i).hom '' E i) '' (s : Set ι), s.finite_toSet.image _, ?_, ?_⟩
  · rintro K ⟨i, hi, rfl⟩
    exact ⟨Y i, f i, Presieve.ofArrows.mk i, E i, hE i hi, rfl⟩
  · simpa [Set.sUnion_image] using hx

/-- A family of morphisms of `LC` belongs to `qcPrecoverage` exactly when it is a qc covering in
the sense of Stacks 09X0. -/
theorem ofArrows_mem_qcPrecoverage_iff {ι : Type*} {X : LocallyQuasiCompactHausdorff.{u}}
    {Y : ι → LocallyQuasiCompactHausdorff.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ qcPrecoverage X ↔ IsQcCovering (fun i => (f i).hom) :=
  ⟨isQcCovering_of_ofArrows_mem_qcPrecoverage f, ofArrows_mem_qcPrecoverage_of_isQcCovering f⟩

/-- The qc coverings of `LC` contain the isomorphisms: an isomorphism of `LC` is a
homeomorphism, so it is a qc covering by Stacks 09X1 (1). -/
instance qcPrecoverage_hasIsos : qcPrecoverage.{u}.HasIsos where
  mem_coverings_of_isIso {S T} f _ := by
    rw [← Presieve.ofArrows_pUnit.{0}, ofArrows_mem_qcPrecoverage_iff]
    exact isQcCovering_of_homeomorph
      (TopCat.homeoOfIso (asIso (locallyQuasiCompactHausdorffToTop.map f) : S.obj ≅ T.obj))

/-- The qc coverings of `LC` are stable under composition, by Stacks 09X1 (2). -/
instance qcPrecoverage_isStableUnderComposition :
    qcPrecoverage.{u}.IsStableUnderComposition where
  comp_mem_coverings {ι S X} f hf {σ Y} g hg := by
    simp only [ofArrows_mem_qcPrecoverage_iff] at hf hg ⊢
    exact isQcCovering_comp (fun i => (f i).hom) (fun i => (f i).hom.hom.continuous)
      (fun i j => (g i j).hom) hf hg

/-- The qc coverings of `LC` are stable under base change, by Stacks 09X1 (3): the fibre
products of `LC` are the topological fibre products. -/
instance qcPrecoverage_isStableUnderBaseChange :
    qcPrecoverage.{u}.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι S X} f hf Y g P p₁ p₂ h := by
    rw [ofArrows_mem_qcPrecoverage_iff] at hf ⊢
    have hTop := isQcCovering_base_change (fun i => (f i).hom)
      (fun i => (f i).hom.hom.continuous) g.hom g.hom.hom.continuous hf
    let U := locallyQuasiCompactHausdorffToTop.{u}
    let e (i : ι) : FiberProd g.hom (f i).hom ≃ₜ (P i).obj :=
      (TopCat.homeoOfIso (((h i).map U).isoPullback ≪≫
        TopCat.pullbackIsoProdSubtype (U.map g) (U.map (f i)))).symm
    refine qcCovering_of_homeomorphic_reindex _ _ id e (fun i x => ?_) hTop
    have hfst := ConcreteCategory.congr_hom
      (show ((((h i).map U).isoPullback ≪≫
          TopCat.pullbackIsoProdSubtype (U.map g) (U.map (f i))).hom ≫
          TopCat.pullbackFst (U.map g) (U.map (f i))) = U.map (p₁ i) by
        simp only [Iso.trans_hom, Category.assoc, TopCat.pullbackIsoProdSubtype_hom_fst,
          IsPullback.isoPullback_hom_fst]) (e i x)
    change (U.map (p₁ i)).hom (e i x) = _
    rw [← hfst]
    change ((e i).symm (e i x)).val.1 = x.val.1
    rw [Homeomorph.symm_apply_apply]

/-- **`LC` with its qc coverings is a site.** The qc coverings of Stacks 09X0 form a
pretopology on `LC`, by Stacks 09X1. -/
@[stacks 09WY "LC with the collection of qc coverings forms a site"]
noncomputable def qcPretopology : Pretopology LocallyQuasiCompactHausdorff.{u} :=
  qcPrecoverage.toPretopology

/-- The qc topology on `LC`: the Grothendieck topology generated by the qc coverings. -/
@[stacks 09WY "the qc topology on LC"]
def qcTopology : GrothendieckTopology LocallyQuasiCompactHausdorff.{u} :=
  qcPrecoverage.toGrothendieck

/-- The qc topology is generated by the pretopology of qc coverings. -/
theorem qcPretopology_toGrothendieck :
    qcPretopology.{u}.toGrothendieck = qcTopology :=
  qcPrecoverage.toGrothendieck_toPretopology_eq_toGrothendieck

/-- **The qc topology is stronger than the usual one.** Every open covering of an object of
`LC`, i.e. every jointly surjective family of open embeddings, is a qc covering, because the
objects of `LC` are locally quasi-compact. -/
@[stacks 09WY "the qc topology is stronger than the usual one"]
theorem comap_precoverage_le_qcPrecoverage :
    TopCat.precoverage.comap locallyQuasiCompactHausdorffToTop.{u} ≤ qcPrecoverage := by
  intro X R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  change _ ∧ _ at hR
  have hsurj : ∀ x : X, ∃ i, x ∈ Set.range (E.f i).hom := by
    simpa [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      PreZeroHypercover.presieve₀] using! hR.1
  have hopen : ∀ i, IsOpenEmbedding (E.f i).hom := by
    simpa [Presieve.map_ofArrows, PreZeroHypercover.presieve₀,
      TopCat.isOpenEmbedding] using! hR.2
  rw [PreZeroHypercover.presieve₀, ofArrows_mem_qcPrecoverage_iff]
  exact IsQcCovering.of_isOpenEmbedding hopen hsurj

/-- The topology of open coverings of `LC` is coarser than the qc topology. -/
@[stacks 09WY "the qc topology is stronger than the usual one, as topologies"]
theorem toGrothendieck_comap_precoverage_le_qcTopology :
    (TopCat.precoverage.comap locallyQuasiCompactHausdorffToTop.{u}).toGrothendieck ≤
      qcTopology :=
  Precoverage.toGrothendieck_mono comap_precoverage_le_qcPrecoverage

end Stacks.Topology.LocallyQuasiCompactHausdorff
