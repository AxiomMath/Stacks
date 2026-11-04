module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import StacksFrontier.Topology.Limits.Defs
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Cofiltered limits of spectral spaces and the constructible topology

Let `J` be a small cofiltered category and `F : J ⥤ TopCat` a diagram of spectral spaces whose
transition maps are all spectral. Write `X = lim F` with projections `π i = limit.π F i`. Fix an
index `i`, a subset `E ⊆ F.obj i` closed in the constructible topology of `F.obj i` and a subset
`G ⊆ F.obj i` open in it. Then

  `π i ⁻¹' E ⊆ π i ⁻¹' G  ↔  ∃ (j) (a : j ⟶ i), F.map a ⁻¹' E ⊆ F.map a ⁻¹' G`,

i.e. an inclusion between a constructibly closed and a constructibly open set can always be
detected at a finite stage.

## Main results

* `CategoryTheory.IsCofiltered.exists_equalizer_finset`: in a cofiltered category finitely many
  pairs of parallel morphisms out of one object can be equalized simultaneously.
* `SpectralLimits.nonempty_preimage_limit_π`: if every stagewise preimage of a constructibly
  closed `C ⊆ F.obj i` is nonempty, then so is `π i ⁻¹' C`.
* `SpectralLimits.preimage_limit_π_subset_iff_exists_map_preimage_subset`: the equivalence above.

## References

* [Stacks Project, Tag 0A2X](https://stacks.math.columbia.edu/tag/0A2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u

namespace CategoryTheory.IsCofiltered

/-- In a cofiltered category, finitely many pairs of parallel morphisms out of a single source
can be equalized simultaneously: there is a morphism `e : w' ⟶ w` with `e ≫ f a = e ≫ g a` for
every `a` in a given finite set. -/
theorem exists_equalizer_finset
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    {ι : Type u} (w : J) (targets : ι → J)
    (f g : (a : ι) → (w ⟶ targets a))
    (S : Finset ι) :
    ∃ (w' : J) (e : w' ⟶ w), ∀ a ∈ S, e ≫ f a = e ≫ g a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨w, 𝟙 w, by simp⟩
  | @insert a S' _ IH =>
    obtain ⟨ww, ee, hh⟩ := IH
    obtain ⟨ww', ee', hee'⟩ := IsCofilteredOrEmpty.cone_maps (ee ≫ f a) (ee ≫ g a)
    refine ⟨ww', ee' ≫ ee, fun b hb => ?_⟩
    simp only [Finset.mem_insert] at hb
    rcases hb with rfl | hb'
    · simpa using hee'
    · rw [Category.assoc, Category.assoc, hh b hb']

end CategoryTheory.IsCofiltered

namespace SpectralLimits

/-- Finitely many compatibility constraints can be met at once: given a finite set `S` of
morphisms of `J` and a subset `C ⊆ F.obj i` all of whose stagewise preimages are nonempty, there
is a family `x` with `x i ∈ C` that is compatible along every morphism in `S`. -/
theorem exists_compatible_point_of_finite_constraints
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (i : J) (C : Set (F.obj i))
    (hC_nonempty : ∀ (j : J) (a : j ⟶ i), ((F.map a) ⁻¹' C).Nonempty)
    (S : Finset (Σ (p : J × J), p.1 ⟶ p.2)) :
    ∃ (x : (j : J) → F.obj j),
      (x i ∈ C) ∧
      (∀ σ ∈ S, (ConcreteCategory.hom (F.map σ.2)) (x σ.1.1) = x σ.1.2) := by
  classical
  let objs : Finset J := S.image (fun σ => σ.1.1) ∪ S.image (fun σ => σ.1.2) ∪ {i}
  obtain ⟨w, hw⟩ := IsCofiltered.inf_objs_exists objs
  have hi_mem : i ∈ objs := Finset.mem_union_right _ (Finset.mem_singleton_self i)
  have hσ1_mem : ∀ σ ∈ S, σ.1.1 ∈ objs := fun σ hσ =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hσ))
  have hσ2_mem : ∀ σ ∈ S, σ.1.2 ∈ objs := fun σ hσ =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hσ))
  let mor : (j : J) → (j ∈ objs) → (w ⟶ j) := fun j hj => (hw hj).some
  let ι : Type u := { σ : (Σ (p : J × J), p.1 ⟶ p.2) // σ ∈ S }
  let tgts : ι → J := fun σ => σ.1.1.2
  let f_fun : (a : ι) → (w ⟶ tgts a) := fun σ => mor σ.1.1.1 (hσ1_mem σ.1 σ.2) ≫ σ.1.2
  let g_fun : (a : ι) → (w ⟶ tgts a) := fun σ => mor σ.1.1.2 (hσ2_mem σ.1 σ.2)
  obtain ⟨w', e, heq⟩ := IsCofiltered.exists_equalizer_finset w tgts f_fun g_fun Finset.univ
  obtain ⟨z, hz⟩ := hC_nonempty w' (e ≫ mor i hi_mem)
  have hFobj_nonempty : ∀ j : J, Nonempty (F.obj j) := by
    intro j
    obtain ⟨k, f1, f2, _⟩ := IsCofilteredOrEmpty.cone_objs j i
    obtain ⟨pt, _⟩ := hC_nonempty k f2
    exact ⟨(ConcreteCategory.hom (F.map f1)) pt⟩
  let x : (j : J) → F.obj j := fun j =>
    if hj : j ∈ objs then (ConcreteCategory.hom (F.map (e ≫ mor j hj))) z
    else (hFobj_nonempty j).some
  refine ⟨x, by simp only [x, dite_eq_left hi_mem]; exact hz, fun σ hσ => ?_⟩
  have h1_mem := hσ1_mem σ hσ
  have h2_mem := hσ2_mem σ hσ
  simp only [x, dite_eq_left h1_mem, dite_eq_left h2_mem]
  have hmor_eq : (e ≫ mor σ.1.1 h1_mem) ≫ σ.2 = e ≫ mor σ.1.2 h2_mem := by
    rw [Category.assoc]
    exact heq ⟨σ, hσ⟩ (Finset.mem_univ _)
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, hmor_eq]

/-- There is a globally compatible family lying in a constructibly closed `C ⊆ F.obj i` as soon
as every stagewise preimage of `C` is nonempty. -/
theorem exists_compatible_family_mem
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (hF_spec : ∀ j, SpectralSpace (F.obj j))
    (hF_map : ∀ {i j : J} (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : J) (C : Set (F.obj i))
    (hC_closed : @IsClosed _ (constructibleTopology (F.obj i)) C)
    (hC_nonempty : ∀ (j : J) (a : j ⟶ i), ((F.map a) ⁻¹' C).Nonempty) :
    ∃ (x : (j : J) → F.obj j),
      (∀ {j k : J} (f : j ⟶ k), (ConcreteCategory.hom (F.map f)) (x j) = x k) ∧
      (x i ∈ C) := by
  have hCompactJ : ∀ j, @CompactSpace (↥(F.obj j)) (constructibleTopology (↥(F.obj j))) := fun j =>
    @compactSpace_constructibleTopology _ _ (hF_spec j)
  have hT2J : ∀ j, @T2Space (↥(F.obj j)) (constructibleTopology (↥(F.obj j))) := fun j =>
    @t2Space_constructibleTopology _ _ (hF_spec j)
  let prodTop :=
    @Pi.topologicalSpace J (fun j => ↥(F.obj j)) (fun j => constructibleTopology (↥(F.obj j)))
  have hProdCompact : @CompactSpace ((j : J) → ↥(F.obj j)) prodTop :=
    @Pi.compactSpace J (fun j => ↥(F.obj j)) (fun j => constructibleTopology (↥(F.obj j))) hCompactJ
  have hcont : ∀ j, @Continuous _ _ prodTop (constructibleTopology (↥(F.obj j))) (fun x => x j) :=
    fun j => @continuous_apply J (fun j => ↥(F.obj j))
      (fun j => constructibleTopology (↥(F.obj j))) j
  have hs_closed : @IsClosed _ prodTop {x : (j : J) → ↥(F.obj j) | x i ∈ C} :=
    @IsClosed.preimage _ _ prodTop (constructibleTopology (↥(F.obj i))) (fun x => x i)
      (hcont i) C hC_closed
  have hs_compact : @IsCompact _ prodTop {x : (j : J) → ↥(F.obj j) | x i ∈ C} :=
    @IsClosed.isCompact _ prodTop _ hProdCompact hs_closed
  let ι := Σ (p : J × J), p.1 ⟶ p.2
  let T : ι → Set ((j : J) → ↥(F.obj j)) := fun σ =>
    {x | (ConcreteCategory.hom (F.map σ.2)) (x σ.1.1) = x σ.1.2}
  have hT_closed : ∀ σ : ι, @IsClosed _ prodTop (T σ) := fun σ =>
    @isClosed_eq (↥(F.obj σ.1.2)) ((j : J) → ↥(F.obj j))
      (constructibleTopology (↥(F.obj σ.1.2))) prodTop (hT2J σ.1.2)
      (fun x => (ConcreteCategory.hom (F.map σ.2)) (x σ.1.1))
      (fun x => x σ.1.2)
      (@Continuous.comp _ _ _ prodTop (constructibleTopology (↥(F.obj σ.1.1)))
        (constructibleTopology (↥(F.obj σ.1.2))) _ _
        (hF_map σ.2).continuous_constructibleTopology (hcont σ.1.1))
      (hcont σ.1.2)
  have hFIP : ∀ (u : Finset ι),
      (({x : (j : J) → ↥(F.obj j) | x i ∈ C}) ∩ ⋂ σ ∈ u, T σ).Nonempty := by
    intro u
    obtain ⟨x, hxC, hxT⟩ :=
      exists_compatible_point_of_finite_constraints F i C hC_nonempty u
    exact ⟨x, hxC, mem_iInter₂.mpr (fun σ hσ => hxT σ hσ)⟩
  obtain ⟨x, hxs, hxT⟩ :=
    @IsCompact.inter_iInter_nonempty _ prodTop _ ι hs_compact T hT_closed hFIP
  exact ⟨x, fun {j k} f => mem_iInter.mp hxT ⟨(j, k), f⟩, hxs⟩

/-- A compatible family in the product determines a point of the categorical limit with the
prescribed `i`-th coordinate. -/
theorem exists_limit_point_apply_eq
    {J : Type u} [SmallCategory J]
    (F : J ⥤ TopCat.{u})
    (x : (j : J) → F.obj j)
    (hcompat : ∀ {j k : J} (f : j ⟶ k), (ConcreteCategory.hom (F.map f)) (x j) = x k)
    (i : J) :
    ∃ (p : ↑(limit F)), (ConcreteCategory.hom (limit.π F i)) p = x i := by
  have hx_compat : x ∈ {u : (j : J) → F.obj j |
      ∀ {i j : J} (f : i ⟶ j), (ConcreteCategory.hom (F.map f)) (u i) = u j} :=
    fun f => hcompat f
  let p_cone : (TopCat.limitCone F).pt := ⟨x, hx_compat⟩
  let iso := (TopCat.limitConeIsLimit F).conePointUniqueUpToIso (limit.isLimit F)
  refine ⟨(ConcreteCategory.hom iso.hom) p_cone, ?_⟩
  have h : iso.hom ≫ limit.π F i = (TopCat.limitCone F).π.app i :=
    (TopCat.limitConeIsLimit F).conePointUniqueUpToIso_hom_comp (limit.isLimit F) i
  rw [← TopCat.comp_app iso.hom (limit.π F i) p_cone, h]
  exact TopCat.limitCone_π_app_apply F i p_cone

/-- If every stagewise preimage of a constructibly closed `C ⊆ F.obj i` is nonempty, then so is
`π i ⁻¹' C`. -/
theorem nonempty_preimage_limit_π
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (hF_spec : ∀ j, SpectralSpace (F.obj j))
    (hF_map : ∀ {i j : J} (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : J) (C : Set (F.obj i))
    (hC_closed : @IsClosed _ (constructibleTopology (F.obj i)) C)
    (hC_nonempty : ∀ (j : J) (a : j ⟶ i),
      ((F.map a) ⁻¹' C).Nonempty) :
    ((limit.π F i) ⁻¹' C).Nonempty := by
  obtain ⟨x, hcompat, hxC⟩ := exists_compatible_family_mem F hF_spec hF_map i C hC_closed
      hC_nonempty
  obtain ⟨p, hp⟩ := exists_limit_point_apply_eq F x hcompat i
  exact ⟨p, show (ConcreteCategory.hom (limit.π F i)) p ∈ C from hp ▸ hxC⟩

/-- If `F.map a ⁻¹' E ⊆ F.map a ⁻¹' G` at some stage `a : j ⟶ i`, then
`limit.π F i ⁻¹' E ⊆ limit.π F i ⁻¹' G`. -/
theorem preimage_limit_π_subset_of_exists_map_preimage_subset
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (i : J) (E G : Set (F.obj i))
    (h : ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' E ⊆ (F.map a) ⁻¹' G) :
    (limit.π F i) ⁻¹' E ⊆ (limit.π F i) ⁻¹' G := by
  obtain ⟨j, a, ha⟩ := h
  rw [← limit.w F a]
  exact preimage_mono (f := ConcreteCategory.hom (limit.π F j)) ha

/-- If `E ⊆ F.obj i` is constructibly closed, `G ⊆ F.obj i` is constructibly open and
`limit.π F i ⁻¹' E ⊆ limit.π F i ⁻¹' G`, then `F.map a ⁻¹' E ⊆ F.map a ⁻¹' G` at some stage
`a : j ⟶ i`. -/
theorem exists_map_preimage_subset_of_preimage_limit_π_subset
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (hF_spec : ∀ j, SpectralSpace (F.obj j))
    (hF_map : ∀ {i j : J} (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : J) (E G : Set (F.obj i))
    (hE : @IsClosed _ (constructibleTopology (F.obj i)) E)
    (hG : @IsOpen _ (constructibleTopology (F.obj i)) G)
    (h : (limit.π F i) ⁻¹' E ⊆ (limit.π F i) ⁻¹' G) :
    ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' E ⊆ (F.map a) ⁻¹' G := by
  have hC_closed : @IsClosed _ (constructibleTopology (F.obj i)) (E ∩ Gᶜ) :=
    @IsClosed.inter _ _ _ (constructibleTopology (F.obj i)) hE
      (@IsOpen.isClosed_compl _ (constructibleTopology (F.obj i)) _ hG)
  have hC_empty : (limit.π F i) ⁻¹' (E ∩ Gᶜ) = ∅ := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun hx hng => hng (h hx)
  have hex : ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' (E ∩ Gᶜ) = ∅ := by
    by_contra h_all
    push Not at h_all
    exact (nonempty_preimage_limit_π F hF_spec hF_map i (E ∩ Gᶜ) hC_closed h_all).ne_empty
      hC_empty
  obtain ⟨j, a, ha⟩ := hex
  refine ⟨j, a, fun x hx => ?_⟩
  by_contra hxG
  exact ha.subset (show x ∈ (F.map a) ⁻¹' (E ∩ Gᶜ) from ⟨hx, hxG⟩)

/-- Let `J` be a small cofiltered category and let `F : J ⥤ TopCat` be a diagram of spectral
spaces such that, for every morphism `a : j ⟶ i` in `J`, the underlying map
`F.map a : F.obj j → F.obj i` is a spectral map. Let `X := limit F` with projections
`π_i := limit.π F i : X → F.obj i`. For every object `i : J` and any subsets `E, G ⊂ F.obj i`
where `E` is closed in the constructible topology and `G` is open in the constructible topology,
we have
`π_i ⁻¹' E ⊆ π_i ⁻¹' G ↔ ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' E ⊆ (F.map a) ⁻¹' G`. -/
@[stacks 0A2X]
theorem preimage_limit_π_subset_iff_exists_map_preimage_subset
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{u})
    (hF_spec : ∀ j, SpectralSpace (F.obj j))
    (hF_map : ∀ {i j : J} (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : J) (E G : Set (F.obj i))
    (hE : @IsClosed _ (constructibleTopology (F.obj i)) E)
    (hG : @IsOpen _ (constructibleTopology (F.obj i)) G) :
    ((limit.π F i) ⁻¹' E ⊆ (limit.π F i) ⁻¹' G) ↔
      (∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' E ⊆ (F.map a) ⁻¹' G) :=
  ⟨exists_map_preimage_subset_of_preimage_limit_π_subset F hF_spec hF_map i E G hE hG,
    preimage_limit_π_subset_of_exists_map_preimage_subset F i E G⟩

end SpectralLimits
