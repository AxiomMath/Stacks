module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import StacksFrontier.Topology.Limits.Defs
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Descent of quasi-compact opens along cofiltered limits of spectral spaces

Let `J` be a cofiltered index category and `F : J ⥤ TopCat` a diagram of spectral spaces whose
transition maps are all spectral. Write `X = lim F` with projections `p i = limit.π F i`. Then:

1. every quasi-compact open `U ⊆ X` is `p i ⁻¹' U i` for some stage `i` and some quasi-compact
   open `U i ⊆ F.obj i`;
2. an inclusion `p i ⁻¹' U i ⊆ p j ⁻¹' U j` between preimages of quasi-compact opens is already
   witnessed by a span `a : k ⟶ i`, `b : k ⟶ j` with `F.map a ⁻¹' U i ⊆ F.map b ⁻¹' U j`;
3. an equality `p i ⁻¹' U i = ⋃ s, p i ⁻¹' U s` of a quasi-compact open with a finite union of
   quasi-compact opens at the *same* stage descends along some `a : j ⟶ i`;
4. likewise for a finite intersection.

## Main results

* `SpectralLimits.descent_of_quasiCompact_opens`: every quasi-compact open of the limit is the
  preimage of a quasi-compact open of some stage.
* `SpectralLimits.descent_of_inclusions`: an inclusion between preimages of quasi-compact opens in
  the limit already holds along some span.
* `SpectralLimits.descent_of_finite_unions`: an equality in the limit of a quasi-compact open with
  a finite union of quasi-compact opens of the same stage already holds along some morphism.
* `SpectralLimits.descent_of_finite_intersections`: the same for a finite intersection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v
universe v'

namespace SpectralLimits

variable {J : Type v} [Category.{v'} J] [IsCofiltered J]
variable (F : J ⥤ TopCat.{max v u})

/-- The preimages of the stagewise quasi-compact opens form a topological basis of the limit. -/
private lemma limit_preimage_compact_open_basis
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a)) :
    TopologicalSpace.IsTopologicalBasis
      {S : Set ((limit F : TopCat)) |
        ∃ (i : J) (V : Set (F.obj i)), IsOpen V ∧ IsCompact V ∧ S = (limit.π F i) ⁻¹' V} := by
  classical
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro S ⟨i, V, hVo, _, rfl⟩
    exact (ConcreteCategory.hom (limit.π F i)).continuous.isOpen_preimage V hVo
  · intro x U hxU hUo
    set tc : LimitCone F := ⟨TopCat.limitCone F, TopCat.limitConeIsLimit F⟩
    set e : (limit F : TopCat) ≃ₜ (TopCat.limitCone F).pt :=
      TopCat.homeoOfIso (limit.isoLimitCone tc)
    have hproj (y : (limit F : TopCat)) (i : J) :
        (e y).val i = (ConcreteCategory.hom (limit.π F i)) y := by
      rw [← limit.isoLimitCone_hom_π tc i, ConcreteCategory.comp_apply,
        TopCat.limitCone_π_app_apply, TopCat.homeoOfIso_apply]
    obtain ⟨W, hWo, hWU'⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp (e.isOpenMap U hUo)
    have hxW : (e x).val ∈ W := by
      show e x ∈ Subtype.val ⁻¹' W
      rw [hWU']
      exact Set.mem_image_of_mem e hxU
    obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hWo _ hxW
    have hrefine : ∀ i ∈ I, ∃ V : Set (F.obj i), IsOpen V ∧ IsCompact V ∧
        (e x).val i ∈ V ∧ V ⊆ u i := by
      intro i hi
      obtain ⟨huo, hxu⟩ := hu i hi
      obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVu⟩ :=
        (PrespectralSpace.isTopologicalBasis (X := F.obj i)).exists_subset_of_mem_open hxu huo
      exact ⟨V, hVo, hVc, hxV, hVu⟩
    choose V hVo hVc hxV hVu using hrefine
    set k := IsCofiltered.inf I (∅ : Finset _)
    have hWk_pieces : ∀ i (hi : i ∈ I),
        IsOpen ((ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) ⁻¹' (V i hi)) ∧
        IsCompact ((ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) ⁻¹' (V i hi)) :=
      fun i hi ↦ ⟨(hF (IsCofiltered.infTo I ∅ hi)).toContinuous.isOpen_preimage _ (hVo i hi),
        (hF (IsCofiltered.infTo I ∅ hi)).isCompact_preimage_of_isOpen (hVo i hi) (hVc i hi)⟩
    suffices h : ∃ (Wk : Set (F.obj k)), IsOpen Wk ∧ IsCompact Wk ∧
        (∀ i (hi : i ∈ I),
          Wk ⊆ (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) ⁻¹' (V i hi)) ∧
        (∀ y : F.obj k, (∀ i (hi : i ∈ I),
          (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) y ∈ V i hi) → y ∈ Wk) by
      obtain ⟨Wk, hWk_open, hWk_compact, hWk_sub, hWk_sup⟩ := h
      refine ⟨(ConcreteCategory.hom (limit.π F k)) ⁻¹' Wk,
             ⟨k, Wk, hWk_open, hWk_compact, rfl⟩, ?_, ?_⟩
      · rw [Set.mem_preimage]
        apply hWk_sup
        intro i hi
        have : (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi)))
               ((ConcreteCategory.hom (limit.π F k)) x) = (e x).val i := by
          conv_rhs => rw [hproj x i]
          exact limit.w_apply F _ x
        rw [this]
        exact hxV i hi
      · intro y hy
        rw [Set.mem_preimage] at hy
        have hey_in_pi : (e y).val ∈ Set.pi (↑I) u := by
          intro i hi
          have hyw := hWk_sub i hi hy
          rw [Set.mem_preimage] at hyw
          have heq : (e y).val i = (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi)))
                 ((ConcreteCategory.hom (limit.π F k)) y) := by
            rw [hproj y i]
            exact (limit.w_apply F _ y).symm
          rw [heq]
          exact hVu i hi hyw
        have hey_in_U' : e y ∈ e '' U := by
          rw [← hWU']
          exact hpi hey_in_pi
        exact e.injective.mem_set_image.mp hey_in_U'
    let piece : J → Set (F.obj k) := fun i ↦
      if hi : i ∈ I then (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) ⁻¹' (V i hi)
      else Set.univ
    have hpiece_eq : ∀ i (hi : i ∈ I),
        piece i = (ConcreteCategory.hom (F.map (IsCofiltered.infTo I ∅ hi))) ⁻¹' (V i hi) :=
      fun i hi ↦ by simp [piece, hi]
    have hpiece_open : ∀ i ∈ I, IsOpen (piece i) := fun i hi ↦ by
      rw [hpiece_eq i hi]
      exact (hWk_pieces i hi).1
    have hpiece_compact : ∀ i ∈ I, IsCompact (piece i) := fun i hi ↦ by
      rw [hpiece_eq i hi]
      exact (hWk_pieces i hi).2
    have hWk_compact : IsCompact (⋂ i ∈ I, piece i) := by
      suffices h : ∀ (s : Finset J), s ⊆ I → IsCompact (⋂ i ∈ s, piece i) from h I
          (Finset.Subset.refl I)
      intro s hs
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
        exact isCompact_univ
      | insert ha ih =>
        rename_i a s0
        rw [Finset.set_biInter_insert]
        exact QuasiSeparatedSpace.inter_isCompact _ _
          (hpiece_open _ (hs (Finset.mem_insert_self _ _)))
          (hpiece_compact _ (hs (Finset.mem_insert_self _ _)))
          (isOpen_biInter_finset fun i hi ↦ hpiece_open i (hs (Finset.mem_insert_of_mem hi)))
          (s0 (fun x hx ↦ hs (Finset.mem_insert_of_mem hx)))
    refine ⟨⋂ i ∈ I, piece i, isOpen_biInter_finset hpiece_open, hWk_compact, ?_, ?_⟩
    · intro i hi
      calc ⋂ j ∈ I, piece j ⊆ piece i := Set.biInter_subset_of_mem hi
        _ = _ := hpiece_eq i hi
    · intro y hy
      exact Set.mem_biInter fun i hi ↦ (hpiece_eq i hi ▸ Set.mem_preimage.mpr (hy i hi))

/-- A finite union of preimages of quasi-compact opens of various stages is the preimage of a
single quasi-compact open of one stage. -/
private lemma pull_to_common_stage
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (n : ℕ) (idx : Fin n → J) (V : ∀ m : Fin n, Set (F.obj (idx m)))
    (hV : ∀ m, IsOpen (V m) ∧ IsCompact (V m)) :
    ∃ (k : J) (W : Set (F.obj k)), IsOpen W ∧ IsCompact W ∧
      (limit.π F k) ⁻¹' W = ⋃ m, (limit.π F (idx m)) ⁻¹' (V m) := by
  classical
  set objs := Finset.image idx Finset.univ
  set k := IsCofiltered.inf objs ∅
  let a : ∀ m : Fin n, k ⟶ idx m := fun m ↦
    IsCofiltered.infTo objs ∅ (Finset.mem_image_of_mem idx (Finset.mem_univ m))
  refine ⟨k, ⋃ m, (F.map (a m)) ⁻¹' (V m),
    isOpen_iUnion fun m ↦ (hF (a m)).toContinuous.isOpen_preimage _ (hV m).1,
    isCompact_iUnion fun m ↦ (hF (a m)).isCompact_preimage_of_isOpen (hV m).1 (hV m).2, ?_⟩
  simp only [Set.preimage_iUnion]
  congr 1
  ext m x
  simp only [Set.mem_preimage]
  rw [← ConcreteCategory.comp_apply, limit.w F (a m)]

/-- For every quasi-compact open `U` of the limit `lim F`, there exist an index `i` and a
quasi-compact open `Ui` of `F.obj i` whose preimage under the projection equals `U`. -/
@[stacks 0A30 "part (1): descent of quasi-compact opens"]
theorem descent_of_quasiCompact_opens
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (U : Set ((limit F : TopCat))) (hUopen : IsOpen U) (hUcpt : IsCompact U) :
    ∃ (i : J) (Ui : Set (F.obj i)), IsOpen Ui ∧ IsCompact Ui ∧
      (limit.π F i) ⁻¹' Ui = U := by
  have hU_basis : ∀ x ∈ U, ∃ (j : J) (V : Set (F.obj j)),
      IsOpen V ∧ IsCompact V ∧ x ∈ (limit.π F j) ⁻¹' V ∧ (limit.π F j) ⁻¹' V ⊆ U := by
    intro x hxU
    obtain ⟨S, ⟨j, V, hVo, hVc, rfl⟩, hxS, hSU⟩ :=
      (limit_preimage_compact_open_basis F hF).isOpen_iff.mp hUopen x hxU
    exact ⟨j, V, hVo, hVc, hxS, hSU⟩
  choose jx Vx hVxo hVxc hxVx hVxU using hU_basis
  obtain ⟨fin_cover, hfin_sub⟩ := hUcpt.elim_finite_subcover
    (fun (x : U) ↦ (limit.π F (jx x x.2)) ⁻¹' (Vx x x.2))
    (fun x ↦ (ConcreteCategory.hom (limit.π F (jx x x.2))).continuous.isOpen_preimage _
      (hVxo x x.2))
    fun x hxU ↦ Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hxVx x hxU⟩
  let enum := fin_cover.equivFin.symm
  obtain ⟨k, W, hWo, hWc, hWeq⟩ := pull_to_common_stage F hF fin_cover.card
    (fun m ↦ jx (enum m) (enum m).1.2)
    (fun m ↦ Vx (enum m) (enum m).1.2)
    (fun m ↦ ⟨hVxo (enum m) (enum m).1.2, hVxc (enum m) (enum m).1.2⟩)
  refine ⟨k, W, hWo, hWc, ?_⟩
  apply Set.Subset.antisymm
  · rw [hWeq]
    exact Set.iUnion_subset fun m ↦ hVxU (enum m) (enum m).1.2
  · intro x hxU
    rw [hWeq, Set.mem_iUnion]
    obtain ⟨p, hp_mem, hxp⟩ := Set.mem_iUnion₂.mp (hfin_sub hxU)
    refine ⟨fin_cover.equivFin ⟨p, hp_mem⟩, ?_⟩
    have heq : enum (fin_cover.equivFin ⟨p, hp_mem⟩) = ⟨p, hp_mem⟩ :=
      fin_cover.equivFin.symm_apply_apply ⟨p, hp_mem⟩
    simp only [enum] at heq ⊢
    rw [show (↑(fin_cover.equivFin.symm (fin_cover.equivFin ⟨p, hp_mem⟩)) : U) =
            (↑(⟨p, hp_mem⟩ : ↥fin_cover) : U) from
      congr_arg Subtype.val heq]
    exact hxp

/-- If every span `a : k ⟶ i`, `b : k ⟶ j` has a point of `F.obj k` sent into `Ui` by `a` and
outside `Uj` by `b`, then for every finite set `S` of morphisms of `J` there is a family of points
compatible along `S` whose `i`-th coordinate lies in `Ui` and whose `j`-th coordinate does not lie
in `Uj`. -/
private lemma fip_for_descent
    [∀ i, SpectralSpace (F.obj i)]
    (i j : J) (Ui : Set (F.obj i)) (Uj : Set (F.obj j))
    (hcon : ∀ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      ∃ x : F.obj k, (F.map a) x ∈ Ui ∧ (F.map b) x ∉ Uj)
    (S : Finset (Σ (p : J × J), p.1 ⟶ p.2)) :
    ∃ (σ : ∀ t : J, F.obj t),
      (∀ e ∈ S, (F.map e.2) (σ e.1.1) = σ e.1.2) ∧
      σ i ∈ Ui ∧ σ j ∉ Uj := by
  classical
  have hne : ∀ t : J, Nonempty (F.obj t) := by
    intro t
    let m := IsCofiltered.min (IsCofiltered.min t i) j
    let f1 : m ⟶ t := IsCofiltered.minToLeft _ j ≫ IsCofiltered.minToLeft t i
    let f2 : m ⟶ i := IsCofiltered.minToLeft _ j ≫ IsCofiltered.minToRight t i
    let f3 : m ⟶ j := IsCofiltered.minToRight _ j
    obtain ⟨x, _, _⟩ := hcon m f2 f3
    exact ⟨F.map f1 x⟩
  let objs : Finset J := S.image (fun e ↦ e.1.1) ∪ S.image (fun e ↦ e.1.2) ∪ {i, j}
  let H : Finset ((X : J) ×' (Y : J) ×' (_ : X ∈ objs) ×' (_ : Y ∈ objs) ×' (X ⟶ Y)) :=
    S.attach.image (fun ⟨e, he⟩ ↦ ⟨e.1.1, e.1.2,
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)),
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)),
      e.2⟩)
  let k₀ : J := IsCofiltered.inf objs H
  have hi_mem : i ∈ objs := Finset.mem_union_right _ (Finset.mem_insert_self i {j})
  have hj_mem : j ∈ objs :=
    Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j)))
  let ai : k₀ ⟶ i := IsCofiltered.infTo objs H hi_mem
  let aj : k₀ ⟶ j := IsCofiltered.infTo objs H hj_mem
  obtain ⟨x, hxi, hxj⟩ := hcon k₀ ai aj
  refine ⟨fun t ↦ if ht : t ∈ objs then F.map (IsCofiltered.infTo objs H ht) x
    else (hne t).some, ?_, ?_, ?_⟩
  · intro e he
    have he1_mem : e.1.1 ∈ objs :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))
    have he2_mem : e.1.2 ∈ objs :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
    simp only [dite_eq_left he1_mem, dite_eq_left he2_mem]
    have hcomm : IsCofiltered.infTo objs H he1_mem ≫ e.2 =
        IsCofiltered.infTo objs H he2_mem := by
      apply IsCofiltered.infTo_commutes
      simp only [H, Finset.mem_image]
      exact ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩
    rw [← hcomm]
    simp [Functor.map_comp]
  · simp only [dite_eq_left hi_mem]
    exact hxi
  · simp only [dite_eq_left hj_mem]
    exact hxj

/-- For quasi-compact opens `Ui ⊆ F.obj i` and `Uj ⊆ F.obj j` such that every span `a : k ⟶ i`,
`b : k ⟶ j` has a point of `F.obj k` sent into `Ui` by `a` and outside `Uj` by `b`, there is a
point of the limit whose `i`-th coordinate lies in `Ui` and whose `j`-th coordinate does not lie in
`Uj`. -/
private lemma exists_section_in_Ui_not_Uj
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (i j : J) (Ui : Set (F.obj i)) (Uj : Set (F.obj j))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui)
    (hUj_open : IsOpen Uj) (hUj_cpt : IsCompact Uj)
    (hcon : ∀ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      ∃ x : F.obj k, (F.map a) x ∈ Ui ∧ (F.map b) x ∉ Uj) :
    ∃ x : (TopCat.limitCone F).pt, x.val i ∈ Ui ∧ x.val j ∉ Uj := by
  have hcpt_all : ∀ t : J, @CompactSpace (F.obj t) (constructibleTopology (F.obj t)) :=
    fun t ↦ compactSpace_constructibleTopology (F.obj t)
  have ht2_all : ∀ t : J, @T2Space (F.obj t) (constructibleTopology (F.obj t)) :=
    fun t ↦ t2Space_constructibleTopology (F.obj t)
  have hcont_all : ∀ ⦃s t : J⦄ (f : s ⟶ t),
      @Continuous (F.obj s) (F.obj t) (constructibleTopology (F.obj s))
        (constructibleTopology (F.obj t)) (F.map f) :=
    fun {_ _} f ↦ (hF f).continuous_constructibleTopology
  have hUi_clopen := hUi_cpt.isClopen_constructibleTopology hUi_open
  have hUj_clopen := hUj_cpt.isClopen_constructibleTopology hUj_open
  let : ∀ t : J, TopologicalSpace (F.obj t) := fun t ↦ constructibleTopology (F.obj t)
  have hcpt : ∀ t : J, CompactSpace (F.obj t) := hcpt_all
  have ht2 : ∀ t : J, T2Space (F.obj t) := ht2_all
  have : CompactSpace (∀ t : J, F.obj t) := Pi.compactSpace
  let ι := Σ (p : J × J), p.1 ⟶ p.2
  let C : ι → Set (∀ t : J, F.obj t) :=
    fun e ↦ {σ | (F.map e.2) (σ e.1.1) = σ e.1.2}
  have hC_closed : ∀ e : ι, IsClosed (C e) := fun ⟨⟨s, t⟩, f⟩ ↦
    isClosed_eq ((hcont_all f).comp (continuous_apply s)) (continuous_apply t)
  let M : Set (∀ t : J, F.obj t) := {σ | σ i ∈ Ui}
  let N : Set (∀ t : J, F.obj t) := {σ | σ j ∉ Uj}
  have hM_closed : IsClosed M :=
    (hUi_clopen.preimage (continuous_apply i)).isClosed
  have hN_closed : IsClosed N := by
    have : N = (fun σ : ∀ t : J, F.obj t ↦ σ j) ⁻¹' Ujᶜ := by
      ext σ; simp [N, Set.mem_compl_iff]
    rw [this]
    exact (hUj_clopen.compl.preimage (continuous_apply j)).isClosed
  have hfip : ∀ (u : Finset ι), ((M ∩ N) ∩ ⋂ e ∈ u, C e).Nonempty := by
    intro u
    obtain ⟨σ, hcompat, hσi, hσj⟩ := fip_for_descent F i j Ui Uj hcon u
    exact ⟨σ, ⟨hσi, hσj⟩, Set.mem_iInter₂.mpr hcompat⟩
  obtain ⟨σ, ⟨hσM, hσN⟩, hσC⟩ :=
    (hM_closed.inter hN_closed).isCompact.inter_iInter_nonempty C hC_closed hfip
  exact ⟨⟨σ, fun {s t} f ↦ Set.mem_iInter.mp hσC ⟨(s, t), f⟩⟩, hσM, hσN⟩

/-- If two quasi-compact opens `Ui ⊆ F.obj i` and `Uj ⊆ F.obj j` have nested preimages in the
limit, the inclusion already holds after pulling back along a span `a : k ⟶ i`, `b : k ⟶ j`. -/
@[stacks 0A30 "part (2): descent of inclusions"]
theorem descent_of_inclusions
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (i j : J) (Ui : Set (F.obj i)) (Uj : Set (F.obj j))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui)
    (hUj_open : IsOpen Uj) (hUj_cpt : IsCompact Uj)
    (h : (limit.π F i) ⁻¹' Ui ⊆ (limit.π F j) ⁻¹' Uj) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' Ui ⊆ (F.map b) ⁻¹' Uj := by
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨x, hxi, hxj⟩ := exists_section_in_Ui_not_Uj F hF i j Ui Uj
    hUi_open hUi_cpt hUj_open hUj_cpt fun k a b ↦ Set.not_subset.mp (hcon k a b)
  let t : LimitCone F := ⟨TopCat.limitCone F, TopCat.limitConeIsLimit F⟩
  let y : (limit F : TopCat) := (limit.isoLimitCone t).inv x
  have hπi : (limit.π F i) y = x.val i := by
    rw [← ConcreteCategory.comp_apply, limit.isoLimitCone_inv_π]
    exact TopCat.limitCone_π_app_apply F i x
  have hπj : (limit.π F j) y = x.val j := by
    rw [← ConcreteCategory.comp_apply, limit.isoLimitCone_inv_π]
    exact TopCat.limitCone_π_app_apply F j x
  have hy := h (show y ∈ (limit.π F i) ⁻¹' Ui by rw [Set.mem_preimage, hπi]; exact hxi)
  rw [Set.mem_preimage, hπj] at hy
  exact hxj hy

/-- If two quasi-compact opens of `F.obj i` have equal preimages in the limit, their preimages
already agree along some `a : j ⟶ i`. -/
private lemma exists_preimage_eq_of_limit_preimage_eq
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (i : J) (Ui V : Set (F.obj i))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui) (hV_open : IsOpen V) (hV_cpt : IsCompact V)
    (h' : (limit.π F i) ⁻¹' Ui = (limit.π F i) ⁻¹' V) :
    ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' Ui = (F.map a) ⁻¹' V := by
  obtain ⟨k₁, a₁, b₁, hab₁⟩ := descent_of_inclusions F hF i i Ui V
    hUi_open hUi_cpt hV_open hV_cpt h'.le
  obtain ⟨k₂, a₂, b₂, hab₂⟩ := descent_of_inclusions F hF i i V Ui
    hV_open hV_cpt hUi_open hUi_cpt h'.ge
  let c₁ := IsCofiltered.eqHom a₁ b₁
  have hc₁ : c₁ ≫ a₁ = c₁ ≫ b₁ := IsCofiltered.eq_condition a₁ b₁
  let c₂ := IsCofiltered.eqHom a₂ b₂
  have hc₂ : c₂ ≫ a₂ = c₂ ≫ b₂ := IsCofiltered.eq_condition a₂ b₂
  let g₁ := IsCofiltered.minToLeft (IsCofiltered.eq a₁ b₁) (IsCofiltered.eq a₂ b₂)
  let g₂ := IsCofiltered.minToRight (IsCofiltered.eq a₁ b₁) (IsCofiltered.eq a₂ b₂)
  let e := IsCofiltered.eqHom (g₁ ≫ c₁ ≫ a₁) (g₂ ≫ c₂ ≫ a₂)
  have he : e ≫ (g₁ ≫ c₁ ≫ a₁) = e ≫ (g₂ ≫ c₂ ≫ a₂) :=
    IsCofiltered.eq_condition (g₁ ≫ c₁ ≫ a₁) (g₂ ≫ c₂ ≫ a₂)
  refine ⟨_, e ≫ g₁ ≫ c₁ ≫ a₁, Set.Subset.antisymm ?_ ?_⟩
  · nth_rw 2 [show e ≫ g₁ ≫ c₁ ≫ a₁ = e ≫ g₁ ≫ c₁ ≫ b₁ by rw [← hc₁]]
    intro x hx
    simp only [Set.mem_preimage, Functor.map_comp, TopCat.comp_app] at *
    exact hab₁ hx
  · rw [he]
    nth_rw 2 [show e ≫ g₂ ≫ c₂ ≫ a₂ = e ≫ g₂ ≫ c₂ ≫ b₂ by rw [← hc₂]]
    intro x hx
    simp only [Set.mem_preimage, Functor.map_comp, TopCat.comp_app] at *
    exact hab₂ hx

/-- If, in the limit, the preimage of a quasi-compact open `Ui` equals the union of the preimages
of finitely many quasi-compact opens `U s` (`s : Fin n`), then this equality already holds after
pulling back along some `j ⟶ i`. -/
@[stacks 0A30 "part (3): descent of finite unions"]
theorem descent_of_finite_unions
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (i : J) (n : ℕ) (Ui : Set (F.obj i)) (U : Fin n → Set (F.obj i))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui)
    (hU : ∀ s, IsOpen (U s) ∧ IsCompact (U s))
    (h : (limit.π F i) ⁻¹' Ui = ⋃ s, (limit.π F i) ⁻¹' (U s)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' Ui = ⋃ s, (F.map a) ⁻¹' (U s) := by
  obtain ⟨j, a, ha⟩ := exists_preimage_eq_of_limit_preimage_eq F hF i Ui (⋃ s, U s)
    hUi_open hUi_cpt (isOpen_iUnion fun s ↦ (hU s).1) (isCompact_iUnion fun s ↦ (hU s).2)
    (h.trans Set.preimage_iUnion.symm)
  exact ⟨j, a, ha.trans Set.preimage_iUnion⟩

/-- A finite intersection of quasi-compact opens in a spectral space is quasi-compact. -/
private lemma isCompact_iInter_fin_of_spectral {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (n : ℕ) (U : Fin n → Set X) (hU : ∀ s, IsOpen (U s) ∧ IsCompact (U s)) :
    IsCompact (⋂ s, U s) := by
  induction n with
  | zero => simp [isCompact_univ]
  | succ m ih =>
    have heq : (⋂ s : Fin (m + 1), U s) = U 0 ∩ ⋂ s : Fin m, U (Fin.succ s) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h ↦ ⟨h 0, fun s ↦ h (Fin.succ s)⟩, fun ⟨h0, hs⟩ s ↦ Fin.cases h0 hs s⟩
    rw [heq]
    exact IsCompact.inter_of_isOpen (hU 0).2 (ih (fun s ↦ U (Fin.succ s)) fun s ↦ hU (Fin.succ s))
      (hU 0).1 (isOpen_iInter_of_finite fun s ↦ (hU (Fin.succ s)).1)

/-- If, in the limit, the preimage of a quasi-compact open `Ui` equals the intersection of the
preimages of finitely many quasi-compact opens `U s` (`s : Fin n`), then this equality already
holds after pulling back along some `j ⟶ i`. -/
@[stacks 0A30 "part (4): descent of finite intersections"]
theorem descent_of_finite_intersections
    [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (i : J) (n : ℕ) (Ui : Set (F.obj i)) (U : Fin n → Set (F.obj i))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui)
    (hU : ∀ s, IsOpen (U s) ∧ IsCompact (U s))
    (h : (limit.π F i) ⁻¹' Ui = ⋂ s, (limit.π F i) ⁻¹' (U s)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' Ui = ⋂ s, (F.map a) ⁻¹' (U s) := by
  obtain ⟨j, a, ha⟩ := exists_preimage_eq_of_limit_preimage_eq F hF i Ui (⋂ s, U s)
    hUi_open hUi_cpt (isOpen_iInter_of_finite fun s ↦ (hU s).1)
    (isCompact_iInter_fin_of_spectral n U hU) (h.trans Set.preimage_iInter.symm)
  exact ⟨j, a, ha.trans Set.preimage_iInter⟩

end SpectralLimits
