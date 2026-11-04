module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ImageSections

/-!
# Zariski covering sieves are refined by open immersions

Let `S` be a locally quasi-compact Zariski situation, with site `LC_Zar` of Hausdorff, locally
quasi-compact spaces and Zariski coverings the jointly surjective families of open embeddings. A
*covering sieve* in the resulting Grothendieck topology is far more than such a family: the
topology is the saturation of the precoverage, so a covering sieve is produced by the four
constructors of `CategoryTheory.Precoverage.Saturate` and its arrows need be neither open nor
surjective. This file proves that a covering sieve is nevertheless always refined by an open cover:
every `S.zariskiTopology`-covering sieve of an object `T` contains, around each point of `T`, the
open immersion of an open neighbourhood of that point. This is strictly stronger than joint
surjectivity of the arrows of a covering sieve.

## Main results

* `exists_hom_comp_eq_of_range_subset`: a morphism of the site whose image is contained in the
  image of an open immersion factors through that open immersion.
* `opens_hom_mem_of_subset_range`: a sieve containing an open immersion contains the open immersion
  of every open subset of its image.
* `opens_comap_hom_comp_mem`: the open immersions in a sieve pull back along an arbitrary morphism.
* `opens_image_hom_mem`: the opens of an open subobject descend to opens of the ambient object.
* `exists_opens_hom_mem_of_mem_zariskiTopology`: a Zariski covering sieve of `T` contains, around
  each point of `T`, the open immersion of an open neighbourhood.
* `exists_opens_hom_mem_of_mem_zariskiTopology_over`: the same statement on the localized site
  `LC_Zar/X`.
* `exists_opens_comparison_section_eq`: sections of `π_X^{-1}F` are, on an open neighbourhood of
  every point, pulled back from sections of `F` on open subsets of `X`.

## Implementation notes

Everything is stated with the coercion of a morphism of the site to its underlying continuous map,
and the factorization is produced from the full faithfulness of
`S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop`, so no universe is constrained: the
statements hold for the three independent universes of Stacks 0DCU.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The underlying continuous map of a composite of morphisms of the site is the composite of the
underlying continuous maps. -/
private theorem coe_comp_site {A B T : S.category} (c : A ⟶ B) (b : B ⟶ T) :
    ((c ≫ b : A ⟶ T) : A.obj → T.obj) = (b : B.obj → T.obj) ∘ (c : A.obj → B.obj) := rfl

/-- **Factorization through an open immersion.** A morphism `a : A ⟶ T` of the site whose image is
contained in the image of an open embedding `b : B ⟶ T` factors through `b`. -/
theorem exists_hom_comp_eq_of_range_subset {A B T : S.category}
    (a : A ⟶ T) (b : B ⟶ T) (hb : Topology.IsOpenEmbedding (b : B.obj → T.obj))
    (hab : Set.range (a : A.obj → T.obj) ⊆ Set.range (b : B.obj → T.obj)) :
    ∃ ψ : A ⟶ B, ψ ≫ b = a := by
  let I := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let hI : I.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  let e : B.obj ≃ₜ Set.range (b : B.obj → T.obj) := hb.isEmbedding.toHomeomorph
  let φ : I.obj A ⟶ I.obj B :=
    TopCat.ofHom ⟨fun p => e.symm ⟨(a : A.obj → T.obj) p, hab ⟨p, rfl⟩⟩,
      e.symm.continuous.comp (by fun_prop)⟩
  refine ⟨hI.preimage φ, hI.faithful.map_injective (TopCat.Hom.ext ?_)⟩
  ext p
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- A sieve containing an open immersion `a` contains every morphism whose image lies in that of
`a`. -/
private theorem arrows_of_range_subset {A B T : S.category} {R : Sieve T} (a : A ⟶ T)
    (ha : R.arrows a) (hae : Topology.IsOpenEmbedding (a : A.obj → T.obj)) (b : B ⟶ T)
    (hb : Set.range (b : B.obj → T.obj) ⊆ Set.range (a : A.obj → T.obj)) : R.arrows b := by
  obtain ⟨ψ, rfl⟩ := exists_hom_comp_eq_of_range_subset S b a hae hb
  exact R.downward_closed ha ψ

/-- A sieve containing an open immersion `a : A ⟶ T` contains the open immersion of every open
subset of `T` whose points lie in the image of `a`. -/
theorem opens_hom_mem_of_subset_range {A T : S.category} {R : Sieve T} (a : A ⟶ T)
    (ha : R.arrows a) (hae : Topology.IsOpenEmbedding (a : A.obj → T.obj))
    (V : Opens T.obj) (hV : (V : Set T.obj) ⊆ Set.range (a : A.obj → T.obj)) :
    R.arrows ((S.opensToSlice T).1.obj V).hom := by
  exact arrows_of_range_subset S a ha hae _ (by rw [((S.opensToSlice T).2 V).2]; exact hV)

/-- **Open immersions in a sieve pull back.** If a sieve on `T` contains the open immersion of an
open subset `V₀` of `T`, it contains the composite with `f : Y ⟶ T` of the open immersion of the
preimage of `V₀` under `f`. -/
theorem opens_comap_hom_comp_mem {T Y : S.category} {R : Sieve T} (f : Y ⟶ T) (V₀ : Opens T.obj)
    (hmem : R.arrows ((S.opensToSlice T).1.obj V₀).hom) :
    R.arrows (((S.opensToSlice Y).1.obj
      ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj
        V₀)).hom ≫ f) := by
  have hsub : Set.range ((((S.opensToSlice Y).1.obj
      ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj
        V₀)).hom ≫ f : _ ⟶ T) : _ → T.obj) ⊆
      Set.range ((((S.opensToSlice T).1.obj V₀).hom) : _ → T.obj) := by
    rw [coe_comp_site, Set.range_comp, ((S.opensToSlice T).2 V₀).2,
      ((S.opensToSlice Y).2 _).2]
    rintro z ⟨q, hq, rfl⟩
    exact hq
  exact arrows_of_range_subset S _ hmem ((S.opensToSlice T).2 V₀).1 _ hsub

/-- **Opens of an open subobject descend.** If `V₁` is open in the source of the open immersion of
an open subset `V₀` of `T`, the open immersion of the image of `V₁` in `T` belongs to every sieve
containing the composite of the two open immersions. -/
theorem opens_image_hom_mem {T : S.category} {R : Sieve T} (V₀ : Opens T.obj)
    (V₁ : Opens ((S.opensToSlice T).1.obj V₀).left.obj)
    (hmem : R.arrows (((S.opensToSlice _).1.obj V₁).hom ≫
      ((S.opensToSlice T).1.obj V₀).hom)) :
    R.arrows ((S.opensToSlice T).1.obj
      ⟨(((S.opensToSlice T).1.obj V₀).hom : _ → T.obj) '' V₁,
        ((S.opensToSlice T).2 V₀).1.isOpenMap _ V₁.isOpen⟩).hom := by
  refine opens_hom_mem_of_subset_range S _ hmem ?_ _ ?_
  · rw [coe_comp_site]
    exact ((S.opensToSlice T).2 V₀).1.comp ((S.opensToSlice _).2 V₁).1
  · rw [coe_comp_site, Set.range_comp, ((S.opensToSlice _).2 V₁).2]
    exact subset_rfl

/-- **A Zariski covering sieve is refined by an open cover.** For every point `x` of an object `T`
of the site and every covering sieve `R` of `T`, there is an open neighbourhood `V` of `x` in `T`
whose open immersion into `T` belongs to `R`. -/
theorem exists_opens_hom_mem_of_mem_zariskiTopology {T : S.category}
    {R : Sieve T} (hR : R ∈ S.zariskiTopology T) (x : T.obj) :
    ∃ V : Opens T.obj, x ∈ V ∧ R.arrows ((S.opensToSlice T).1.obj V).hom := by
  rw [zariskiTopology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of T P hP =>
    obtain ⟨h1, h2⟩ := hP
    rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at h1
    obtain ⟨T', g, hg, hx⟩ := h1 x
    obtain ⟨hPu⟩ := hg
    rename_i Z u
    have hoe : Topology.IsOpenEmbedding (u : Z.obj → T.obj) := h2 ⟨hPu⟩
    exact ⟨⟨Set.range (u : Z.obj → T.obj), hoe.isOpen_range⟩, hx,
      opens_hom_mem_of_subset_range S u (Sieve.le_generate P _ _ hPu) hoe _ subset_rfl⟩
  | top T => exact ⟨⊤, trivial, trivial⟩
  | pullback T S' hS' Y f ih =>
    obtain ⟨V₀, hxV₀, hmem⟩ := ih ((f : Y.obj → T.obj) x)
    exact ⟨(Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj V₀,
      hxV₀, opens_comap_hom_comp_mem S f V₀ hmem⟩
  | transitive T S' R' hS' hR' ih1 ih2 =>
    obtain ⟨V₀, hxV₀, hmem⟩ := ih1 x
    obtain ⟨p, hp⟩ : ∃ p, (((S.opensToSlice T).1.obj V₀).hom : _ → T.obj) p = x := by
      rw [← Set.mem_range, ((S.opensToSlice T).2 V₀).2]
      exact hxV₀
    obtain ⟨V₁, hpV₁, hmem₁⟩ := ih2 hmem p
    exact ⟨⟨(((S.opensToSlice T).1.obj V₀).hom : _ → T.obj) '' V₁,
      ((S.opensToSlice T).2 V₀).1.isOpenMap _ V₁.isOpen⟩, ⟨p, hpV₁, hp⟩,
      opens_image_hom_mem S V₀ V₁ hmem₁⟩

/-- **A covering sieve of the localized site is refined by an open cover.** For every point `x` of
the source of an object `Z` of `LC_Zar/X` and every covering sieve `R` of `Z` for the localized
topology, there is an open neighbourhood `V` of `x` whose open immersion, as a morphism over `X`,
belongs to `R`. -/
theorem exists_opens_hom_mem_of_mem_zariskiTopology_over {X : S.category} {Z : Over X}
    {R : Sieve Z} (hR : R ∈ (S.zariskiTopology.over X) Z) (x : Z.left.obj) :
    ∃ V : Opens Z.left.obj, x ∈ V ∧
      R.arrows (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
        Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z) := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨V, hxV, hmem⟩ := exists_opens_hom_mem_of_mem_zariskiTopology S hR x
  exact ⟨V, hxV, (Sieve.overEquiv_iff _ _).1 hmem⟩

/-- **Sections of the Zariski comparison inverse image are pulled back from opens of `X` on an open
neighbourhood of every point.** For a sheaf `F` on the small Zariski site of `X`, an object `Z` of
`LC_Zar/X`, a section `a` of `π_X^{-1}F` over `Z` and a point `x` of `Z`, there are an open
neighbourhood `V` of `x` in `Z`, an open subset `W` of `X` through which `V` maps, and a section
`b` of `π_X^{-1}F` over `W`, such that the restriction of `a` to `V` is the pullback of `b`. -/
theorem exists_opens_comparison_section_eq (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) {Z : Over X}
    (a : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj (op Z))
    (x : Z.left.obj) :
    ∃ (V : Opens Z.left.obj) (_ : x ∈ V) (W : Opens X.obj)
      (c : Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶
        (S.opensToSlice X).1.obj W)
      (b : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
        (op ((S.opensToSlice X).1.obj W))),
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
          (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
            Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a =
        ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map c.op b := by
  obtain ⟨V, hxV, hmem⟩ := exists_opens_hom_mem_of_mem_zariskiTopology_over S
    (sieveOfSection_imageSections_comparison_mem.{u, w, max (u + 1) v} S X F a) x
  exact ⟨V, hxV, hmem⟩

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
