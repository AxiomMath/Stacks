module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage

/-!
# A scheme limit of a system bounded by the cutoff has a scheme stage

Let `X = lim Xᵢ` be the limit of a cofiltered inverse system of quasi-compact algebraic spaces
with affine transition morphisms. This file proves, for a system whose base changes are bounded by
the cutoff of the site, that a quasi-compact open subspace of `X` is the inverse image of a
quasi-compact open subspace of some stage, and that if `X` is a scheme then so is some `Xᵢ`, over
a terminal base and so over the integers.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_baseChangeSizeBounded`: a
  quasi-compact open subspace of the limit is the inverse image of a quasi-compact open subspace
  of a stage.
* `exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_baseChangeSizeBounded`: if the
  schematic loci of the stages see every point of the limit, then some stage is a scheme.
* `DescentSituation.exists_isRepresentable_system_obj_of_isTerminal_of_isCutoffBoundedSystem`:
  in the situation of Stacks 084R over a terminal base, with the system bounded by the cutoff, if
  the limit is a scheme then some stage is a scheme.
* `DescentSituation.exists_isRepresentable_system_obj_of_isCutoffBoundedSystem`: the same over
  the integers.

## References

* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Covering

attribute [local instance] pointTopology

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Let `X = limit D` be the limit of a cofiltered inverse system of quasi-compact algebraic
spaces over `S` with affine transition morphisms. If an open subset `V` of the point space of a
stage `D i₀` has inverse image the whole of `|X|`, then there is a later stage `j` at which the
inverse image of `V` is the whole of `|D j|`.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_stage_preimage_eq_univ_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I <
    B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {V : Set (points B S hS (D.obj i₀))} (hV : IsOpen V)
    (hlim : pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀), pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V = Set.univ := by
  classical
  obtain ⟨V₀, f₀, hV₀, hf₀surj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i₀)
      (hD i₀)).mp (hCompact i₀)
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V₀) f₀) :=
    (surjective_iff_surjective_pointsMap B S hS (D.obj i₀) (hD i₀) V₀ f₀).mp hf₀surj
  set C := affineChartSystem B S hS i₀ D ⟨V₀, hV₀⟩ f₀ hAffine
  set L := C.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB
  have hstage : ∀ j : Over i₀,
      Function.Surjective
        (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j)) := by
    intro j x
    obtain ⟨y, hy⟩ := hsurj (pointsMap B S hS (D.obj j.left) (D.map j.hom) x)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (C.isPullback j) x y hy.symm
    exact ⟨w, hw⟩
  have _ : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have _ : ∀ j, CompactSpace (C.schemeDiagram.obj j) := fun j ↦ inferInstance
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  let o₀ : Over i₀ := Over.mk (𝟙 i₀)
  let Vo : Set (points B S hS (yoneda.obj (C.siteDiagram.obj o₀))) :=
    pointsMap B S hS _ (C.stageMap o₀) ⁻¹' V
  have hVo : IsOpen Vo := hV.preimage (continuous_pointsMap B S hS (C.stageMap o₀))
  let W : (C.schemeDiagram.obj o₀).Opens :=
    ⟨(schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm ⁻¹' Vo,
      hVo.preimage (schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm.continuous⟩
  have hW : ((BigFppfOver.toScheme B S hS).mapCone L.cone).π.app o₀ ⁻¹ᵁ W = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y ↦ ?_)
    show (schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app o₀) y) ∈ Vo
    rw [schemePointsHomeomorph_symm_toScheme_map]
    show (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj o₀)) (C.stageMap o₀) ∘
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app o₀)))
      ((schemePointsHomeomorph B S hS L.cone.pt).symm y) ∈ V
    rw [← pointsMap_comp, ← L.toLimit_comp_limitπ o₀, pointsMap_comp]
    exact Set.eq_univ_iff_forall.mp hlim _
  obtain ⟨j, g, hj⟩ := exists_map_eq_top' C.schemeDiagram
    ((BigFppfOver.toScheme B S hS).mapCone L.cone) L.schemeIsLimit W hW
  refine ⟨j.left, g.left, ?_⟩
  have hchart : ∀ x : points B S hS (yoneda.obj (C.siteDiagram.obj j)),
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j))
        (yoneda.map (C.siteDiagram.map g)) x ∈ Vo := by
    intro x
    have hy : (schemePointsHomeomorph B S hS (C.siteDiagram.obj j)) x ∈
        C.schemeDiagram.map g ⁻¹ᵁ W := by rw [hj]; trivial
    have hy' : (schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm
        ((BigFppfOver.toScheme B S hS).map (C.siteDiagram.map g)
          ((schemePointsHomeomorph B S hS (C.siteDiagram.obj j)) x)) ∈ Vo := hy
    rw [schemePointsHomeomorph_symm_toScheme_map] at hy'
    simpa only [Homeomorph.symm_apply_apply] using hy'
  have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.stageMap o₀ =
      C.stageMap j ≫ D.map g.left := by
    have hiso : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app o₀ =
        C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D ⟨V₀, hV₀⟩ f₀).map g :=
      C.iso.hom.naturality g
    simp only [AffineChartSystem.stageMap, ← Category.assoc, hiso]
    rw [Category.assoc, Category.assoc,
      stageBaseChangeDiagram_map_comp_fst B S hS i₀ D ⟨V₀, hV₀⟩ f₀ g]
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨w, hw⟩ := hstage j x
  have hV' : (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj o₀)) (C.stageMap o₀) ∘
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j))
        (yoneda.map (C.siteDiagram.map g))) w ∈ V := hchart w
  rw [← pointsMap_comp, hnat, pointsMap_comp] at hV'
  simpa only [Set.mem_preimage, Function.comp_apply, hw] using hV'

/-- The limit of a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms is quasi-compact.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem isQuasiCompactSpace_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I <
    B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsQuasiCompactSpace B S hS (limit D) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB
  have hqc : IsQuasiCompact B S hS (limit.π D i₀) :=
    isQuasiCompact_of_isAffineHom' B S hS (limit.π D i₀) hlim (hD i₀)
      (isAffineHom_limitπ_of_isAffineHom_map_of_baseChangeSizeBounded B S hS D hSize hν hHomSize
        hAffine hB i₀)
  exact isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.snd (𝟙 (D.obj i₀)) (limit.π D i₀)))
    (hqc (D.obj i₀) (hD i₀) (hCompact i₀) (𝟙 (D.obj i₀)))

/-- **A monotone family of open subspaces which covers the limit is everything at a stage.**
Let `X = limit D` be the limit of a cofiltered inverse system of quasi-compact algebraic
spaces over `S` with affine transition morphisms, and let `K i` be open subspaces of the
stages whose inverse images grow: the inverse image of `K i` in `D j` lies in `K j` for every
`f : j ⟶ i`. If every point of `X` lies in the inverse image of some `K i`, then `K i = ⊤`
for some `i`.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_eq_top_of_covering_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I <
    B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (K : ∀ i, Subfunctor (D.obj i)) (hK : ∀ i, IsOpenSubspace B S hS (K i))
    (hmon : ∀ {i j : I} (f : j ⟶ i), (K i).preimage (D.map f) ≤ K j)
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB
  set R : ∀ i, Set (points B S hS (D.obj i)) :=
    fun i ↦ Set.range (pointsMap B S hS (K i).toFunctor (K i).ι)
  have hRopen : ∀ i, IsOpen (R i) := fun i ↦
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι (hK i).2
  set W : I → Set (points B S hS (limit D)) :=
    fun i ↦ pointsMap B S hS (limit D) (limit.π D i) ⁻¹' R i
  have hWopen : ∀ i, IsOpen (W i) := fun i ↦
    (hRopen i).preimage (continuous_pointsMap B S hS (limit.π D i))
  have hsub : ∀ {i j : I} (f : j ⟶ i),
      Set.range (pointsMap B S hS ((K i).preimage (D.map f)).toFunctor
        ((K i).preimage (D.map f)).ι) ⊆ Set.range (pointsMap B S hS (K j).toFunctor (K j).ι) := by
    intro i j f
    rw [← Subfunctor.homOfLe_ι (hmon f), pointsMap_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  have hstep : ∀ {i j : I} (f : j ⟶ i), W i ⊆ W j := by
    intro i j f x hx
    have hfac : pointsMap B S hS (limit D) (limit.π D i) x =
        pointsMap B S hS (D.obj j) (D.map f)
          (pointsMap B S hS (limit D) (limit.π D j) x) := by
      rw [← Function.comp_apply (f := pointsMap B S hS (D.obj j) (D.map f)), ← pointsMap_comp,
        limit.w]
    have hmem : pointsMap B S hS (limit D) (limit.π D j) x ∈
        Set.range (pointsMap B S hS ((K i).preimage (D.map f)).toFunctor
          ((K i).preimage (D.map f)).ι) := by
      rwa [range_pointsMap_preimage_ι, Set.mem_preimage, ← hfac]
    exact hsub f hmem
  have hdir : Directed (· ⊆ ·) W := fun i i' ↦
    ⟨IsCofiltered.min i i', hstep (IsCofiltered.minToLeft i i'),
      hstep (IsCofiltered.minToRight i i')⟩
  have hcover : (Set.univ : Set (points B S hS (limit D))) ⊆ ⋃ i, W i :=
    fun x _ ↦ Set.mem_iUnion.mpr (hpoint x)
  have _ : CompactSpace (points B S hS (limit D)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (limit D) hlim).mp
      (isQuasiCompactSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hB hD hAffine
          hCompact)
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover W hWopen hcover hdir
  obtain ⟨k, g, hk⟩ := exists_stage_preimage_eq_univ_of_baseChangeSizeBounded B S hS D hSize hν
    hHomSize hB hD hAffine hCompact j (V := R j) (hRopen j) (Set.univ_subset_iff.mp hj)
  refine ⟨k, eq_top_of_range_pointsMap_eq_univ B S hS (hD k) (K k) (hK k)
    (Set.univ_subset_iff.mp ?_)⟩
  rw [← hk, ← range_pointsMap_preimage_ι]
  exact hsub g

/-- Around any one of its points, an open subset of the point space of the limit of a cofiltered
inverse system of algebraic spaces over `S` with affine transition morphisms contains the
preimage of an open neighbourhood at a single stage.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_stage_nbhd_of_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I <
    B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hW : IsOpen W) (x : points B S hS (limit D))
    (hx : x ∈ W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) x ∈ V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V ⊆ W := by
  have _ : Nonempty I := IsCofiltered.nonempty
  have hmem : W ∈ nhds x := hW.mem_nhds hx
  rw [pointTopology_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB] at hmem
  simp only [nhds_iInf, nhds_induced] at hmem
  obtain ⟨i, hi⟩ :=
    (Filter.mem_iInf_of_directed (directedGE_comap_nhds_limitπ B S hS D x) W).1 hmem
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hi
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
  exact ⟨i, V', hV'open, hxV', fun y hy ↦ hVW (hV'V hy)⟩

/-- An open subset of the point space of the limit of a cofiltered inverse system of algebraic
spaces over `S` with affine transition morphisms which is compact is the preimage of a single
open subset of the point space of a single stage.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_stage_isOpen_preimage_eq_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I <
    B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  choose! stage nbhd hOpen hMem hSub using
    exists_stage_nbhd_of_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hB hD hAffine
        hWopen
  obtain ⟨t, htW, htcover⟩ := hWcompact.elim_nhds_subcover
    (fun x ↦ pointsMap B S hS (limit D) (limit.π D (stage x)) ⁻¹' nbhd x)
    fun x hx ↦ ((hOpen x hx).preimage
      (continuous_pointsMap B S hS (limit.π D (stage x)))).mem_nhds (hMem x hx)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (t.image stage)
  let trans : ∀ x : {y // y ∈ t}, j ⟶ stage x.1 := fun x ↦
    (hj (Finset.mem_image_of_mem stage x.2)).some
  refine ⟨j, ⋃ x : {y // y ∈ t},
    pointsMap B S hS (D.obj j) (D.map (trans x)) ⁻¹' nbhd x.1,
    isOpen_iUnion fun x ↦ (hOpen x.1 (htW x.1 x.2)).preimage
      (continuous_pointsMap B S hS (D.map (trans x))), ?_⟩
  have hfactor : ∀ x : {y // y ∈ t},
      pointsMap B S hS (limit D) (limit.π D j) ⁻¹'
          (pointsMap B S hS (D.obj j) (D.map (trans x)) ⁻¹' nbhd x.1) =
        pointsMap B S hS (limit D) (limit.π D (stage x.1)) ⁻¹' nbhd x.1 := by
    intro x
    rw [← Set.preimage_comp, ← pointsMap_comp, limit.w]
  rw [Set.preimage_iUnion]
  refine Set.Subset.antisymm (Set.iUnion_subset fun x ↦ ?_) ?_
  · rw [hfactor x]
    exact hSub x.1 (htW x.1 x.2)
  · simp only [hfactor]
    exact htcover.trans (by rw [Set.iUnion_subtype])

/-! ### Descent of a quasi-compact open set of points -/

/-- A quasi-compact open subset of the point space of the limit of a cofiltered inverse system
of algebraic spaces over `S` with affine transition morphisms is the preimage of a
quasi-compact open subset of the point space of one of the stages.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_stage_isCompact_isOpen_preimage_eq_of_baseChangeSizeBounded {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  obtain ⟨j, V', hV'open, hV'pre⟩ := exists_stage_isOpen_preimage_eq_of_baseChangeSizeBounded B S
    hS D hSize hν hHomSize hB hD hAffine hWopen hWcompact
  have hshrink : ∀ y ∈ W, ∃ K : Set (points B S hS (D.obj j)),
      (IsOpen K ∧ IsCompact K ∧ pointsMap B S hS (limit D) (limit.π D j) y ∈ K) ∧ K ⊆ V' :=
    fun y hy ↦ (hasBasis_nhds_isOpen_isCompact B S hS (D.obj j) (hD j)
      (pointsMap B S hS (limit D) (limit.π D j) y)).mem_iff.mp
      (hV'open.mem_nhds (by rwa [← hV'pre] at hy))
  choose! K hK hKsub using hshrink
  obtain ⟨t, htW, htcover⟩ := hWcompact.elim_nhds_subcover
    (fun y ↦ pointsMap B S hS (limit D) (limit.π D j) ⁻¹' K y)
    fun y hy ↦ ((hK y hy).1.preimage
      (continuous_pointsMap B S hS (limit.π D j))).mem_nhds (hK y hy).2.2
  refine ⟨j, ⋃ y : {z // z ∈ t}, K y.1,
    isOpen_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).1,
    isCompact_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).2.1, ?_⟩
  rw [Set.preimage_iUnion]
  refine Set.Subset.antisymm (Set.iUnion_subset fun y ↦ ?_) ?_
  · rw [← hV'pre]
    exact Set.preimage_mono (hKsub y.1 (htW y.1 y.2))
  · exact htcover.trans (by rw [Set.iUnion_subtype])

/-! ### Descent of a quasi-compact open subspace -/

/-- Let `X = limit D` be the limit of a cofiltered inverse system `D` of algebraic spaces over
`S` with affine transition morphisms. Then for every quasi-compact open subspace `U ⊆ X` there
is a stage `i` and a quasi-compact open subspace of `D i` whose inverse image in `X` is `U`.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_baseChangeSizeBounded {ν :
    Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U := by
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB
  have hWopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hUcompact : CompactSpace (points B S hS U.toFunctor) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS U.toFunctor hU.1).mp hUqc
  have hWcompact : IsCompact (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isCompact_range (continuous_pointsMap B S hS U.ι)
  obtain ⟨i, V, hVopen, hVcompact, hVpre⟩ :=
      exists_stage_isCompact_isOpen_preimage_eq_of_baseChangeSizeBounded
    B S hS D hSize hν hHomSize hB hD hAffine hWopen hWcompact
  have hVsub : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (D.obj i) V) :=
    isOpenSubspace_openSubspaceOfPoints B S hS (hD i) V hVopen
  refine ⟨i, openSubspaceOfPoints B S hS (D.obj i) V, hVsub, ?_, ?_⟩
  · refine isQuasiCompactSpace_of_isCompact_range B S hS (hD i) hVsub ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact hVcompact
  · rw [preimage_openSubspaceOfPoints, hVpre,
      ← eq_openSubspaceOfPoints_range_pointsMap B S hS hlim U hU]

/-- **A stage of a limit is a scheme as soon as the stages' schematic loci see every point of
the limit.** For a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms, if every point of `limit D` lies in the inverse image of the
schematic locus of some stage, then some stage is representable by a scheme.

Here `I` has fewer than `B.cutoff` objects, its hom-sets have cardinality at most some
`ν < B.cutoff`, and the base changes of `D` are bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
theorem exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_baseChangeSizeBounded
    {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.obj i)).toFunctor
          (schematicLocus B S hS (D.obj i)).ι)) :
    ∃ i, (D.obj i).IsRepresentable := by
  obtain ⟨i, hi⟩ := exists_eq_top_of_covering_limit_of_baseChangeSizeBounded B S hS D hSize hν
      hHomSize hB hD hAffine hCompact
    (fun i ↦ schematicLocus B S hS (D.obj i))
    (fun i ↦
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).1)
    (fun {i j} f ↦ preimage_schematicLocus_le B S hS (D.map f) (hD j) (hD i) (hAffine f))
    hpoint
  have _ : (schematicLocus B S hS (D.obj i)).toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).2
  have _ : IsIso (schematicLocus B S hS (D.obj i)).ι :=
    (Subfunctor.eq_top_iff_isIso _).mp hi
  exact ⟨i, isRepresentable_of_natIso (schematicLocus B S hS (D.obj i)).toFunctor
    (asIso (schematicLocus B S hS (D.obj i)).ι)⟩

end Covering

section AffineStage

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Descending an affine open subspace of the limit -/

/-- **An open subspace of a stage with affine inverse image in the limit is affine at some
later stage.** Let `D` be a directed inverse system of quasi-separated algebraic spaces over a
terminal `S` with affine transition morphisms, bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`). Let `V` be a quasi-compact open subspace of
the stage `i₀`, and suppose the inverse image of `V` in `limit D` is an affine algebraic space.
Then the inverse image of `V` in the stage `j` is affine for some `j ≥ i₀`. -/
theorem exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_isCutoffBoundedSystem
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hterminal : IsTerminal S) (hDc : IsCutoffBoundedSystem B S hS D) (i₀ : I) (V : Subfunctor
        (D.obj (op i₀)))
    (hV : IsOpenSubspace B S hS V) (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hW : IsAffineSpace B S hS (V.preimage (limit.π D (op i₀))).toFunctor) :
    ∃ (j : I) (hj : i₀ ≤ j),
      IsAffineSpace B S hS (V.preimage (D.map (homOfLE hj).op)).toFunctor := by
  classical
  have _ : Nonempty I := ⟨i₀⟩
  have _ : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have _ : IsDirected (LimitTail I i₀) (· ≤ ·) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)
  have _ : G.Initial := by dsimp only [G]; infer_instance
  let cg : Cone (G ⋙ D) := (limit.cone D).whisker G
  have hcg : IsLimit cg :=
    (Functor.Initial.isLimitWhiskerEquiv G (limit.cone D)).symm (limit.isLimit D)
  let τ : (G ⋙ D) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (D.obj (op i₀)) :=
    { app := fun j ↦ D.map (homOfLE j.unop.2).op
      naturality := fun j k φ ↦
        ((D.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ ↦ D.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, cg.π.app j ≫ τ.app j = limit.π D (op i₀) := fun j ↦
    limit.w D (homOfLE j.unop.2).op
  have hpre : ∀ j, IsOpenSubspace B S hS (V.preimage (τ.app j)) := fun j ↦
    isOpenSubspace_preimage B S hS (τ.app j) V (hD (op i₀)) (hD (G.obj j)) hV
  have hfrom : ∀ j, IsAffineHom B S hS (V.fromPreimage (τ.app j)) := fun j ↦
    isAffineHom_of_isPullback' B S hS (Subfunctor.isPullback_fromPreimage V (τ.app j)).flip
      (hAffine (homOfLE j.unop.2).op)
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV.1 (hQs (op i₀))
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hV.2)))
  let E : DescentSituation B S hS hZ (LimitTail I i₀) :=
    { system := Subfunctor.preimageDiagram τ V
      algebraicSpace := fun j ↦ (hpre (op j)).1
      transition_affine := fun {_ _} φ ↦
        isAffineHom_of_isPullback' B S hS
          (Subfunctor.isPullback_preimageDiagram_map τ V φ).flip (hAffine (G.map φ))
      quasiCompact := fun j ↦
        isQuasiCompactSpace_source_of_isQuasiCompact B S hS hV.1 hVqc
          (isQuasiCompact_of_isAffineHom' B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      quasiSeparated := fun j ↦
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hpre (op j)).1 hVqs
          (isQuasiSeparated_of_isAffineHom B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      limitCone := Subfunctor.preimageCone τ V hσ
      isLimit := Subfunctor.isLimitPreimageCone τ V hσ hcg
      limitAlgebraicSpace := hW.isAlgebraicSpace
      base := ⟨i₀, le_rfl⟩ }
  have hEc : IsCutoffBoundedSystem B S hS E.system :=
    isCutoffBoundedSystem_of_preorder B S hS ((Cardinal.mk_subtype_le _).trans_lt hDc.mk_lt)
      (baseChangeSizeBounded_of_natTrans_mono B S hS (D := G ⋙ D)
        { app := fun j ↦ (V.preimage (τ.app j)).ι
          naturality := fun j k φ ↦ (Subfunctor.isPullback_preimageDiagram_map τ V φ).w }
        (fun j ↦ show Mono (V.preimage (τ.app j)).ι from
          (NatTrans.mono_iff_mono_app _).2 fun _ ↦ (mono_iff_injective _).2 Subtype.val_injective)
        (fun j ↦ hD _) (fun φ ↦ hAffine _)
        (baseChangeSizeBounded_comp B S hS G hDc.2.2))
  obtain ⟨j, -, hj⟩ :=
    E.exists_isAffineSpace_system_obj_of_isTerminal_of_isCutoffBoundedSystem hterminal hEc hW
  exact ⟨j.1, j.2, hj⟩

end AffineStage

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- In the situation of Stacks 084R — a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms, together with a
chosen limit `X` — if `S` is terminal, the system is bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`) and `X` is a scheme, then some stage `X_i` is
a scheme. -/
theorem exists_isRepresentable_system_obj_of_isTerminal_of_isCutoffBoundedSystem {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hterminal : IsTerminal S)
    (hDc : IsCutoffBoundedSystem B S hS D.system)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, (D.system.obj (op i)).IsRepresentable := by
  classical
  have _ : Nonempty I := ⟨D.base⟩
  have ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hDc
  have hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.system.obj a) := fun a ↦
    D.algebraicSpace a.unop
  have hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.system.map f) := fun f ↦
    D.transition_affine f
  have hQc : ∀ a : Iᵒᵖ, IsQuasiCompactSpace B S hS (D.system.obj a) := fun a ↦
    D.quasiCompact a.unop
  have hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.system.obj a) := fun a ↦
    D.quasiSeparated a.unop
  let e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  have _ : (limit D.system).IsRepresentable := isRepresentable_of_natIso _ e
  have key : ∀ x : points B S hS (limit D.system), ∃ a : Iᵒᵖ,
      pointsMap B S hS (limit D.system) (limit.π D.system a) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.system.obj a)).toFunctor
          (schematicLocus B S hS (D.system.obj a)).ι) := by
    intro x
    obtain ⟨U, hU⟩ := exists_affineOpen_mem_openSubspaceOfRepr B S hS x
    set W : Subfunctor (limit D.system) :=
      openSubspaceOfRepr B S hS (limit D.system) U.1
    have hWopen : IsOpenSubspace B S hS W := isOpenSubspace_openSubspaceOfRepr B S hS U.1
    have hWaff : IsAffineSpace B S hS W.toFunctor := isAffineSpace_openSubspaceOfRepr B S hS U
    obtain ⟨b, V, hV, hVqc, hVpre⟩ :=
        exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_baseChangeSizeBounded
      B S hS D.system hSize hν hHomSize hB hD hAffine W hWopen hWaff.isQuasiCompactSpace
    obtain ⟨j, hj, hjaff⟩ :=
        exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_isCutoffBoundedSystem
      B S hS hZ D.system hD hAffine hQs hterminal hDc b.unop V hV hVqc (by rwa [hVpre])
    set P : Subfunctor (D.system.obj (op j)) :=
      V.preimage (D.system.map (homOfLE hj).op) with hPdef
    have hjrep : P.toFunctor.IsRepresentable := by
      obtain ⟨T, -, ⟨eT⟩⟩ := hjaff
      exact isRepresentable_of_natIso (yoneda.obj T) eT.symm
    refine ⟨op j, range_pointsMap_ι_le_schematicLocus B S hS P
      (isOpenSubspace_preimage B S hS _ V (hD _) (hD _) hV) hjrep ?_⟩
    have hcomp : P.preimage (limit.π D.system (op j)) = W := by
      rw [hPdef, ← Subfunctor.preimage_comp, limit.w D.system (homOfLE hj).op, hVpre]
    have hx : x ∈ Set.range (pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
        (P.preimage (limit.π D.system (op j))).ι) := by
      rwa [hcomp]
    obtain ⟨y, rfl⟩ := hx
    refine ⟨pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j))) y, ?_⟩
    show (pointsMap B S hS P.toFunctor P.ι ∘
        pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j)))) y =
      (pointsMap B S hS (limit D.system) (limit.π D.system (op j)) ∘
        pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
          (P.preimage (limit.π D.system (op j))).ι) y
    rw [← pointsMap_comp, ← pointsMap_comp, Subfunctor.fromPreimage_ι]
  obtain ⟨a, ha⟩ :=
    exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_baseChangeSizeBounded B S hS
    D.system hSize hν hHomSize hB hD hAffine hQc key
  exact ⟨a.unop, ha⟩

/-- In the situation of Stacks 084R over the terminal scheme `Spec ℤ`, if the system is bounded
by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`) and the limit is a scheme, then
some stage is a scheme. -/
theorem exists_isRepresentable_system_obj_of_isCutoffBoundedSystem {B : BigFppfSite.{u}}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I)
    (hDc : IsCutoffBoundedSystem B _ hZ D.system) (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, (D.system.obj (op i)).IsRepresentable :=
  D.exists_isRepresentable_system_obj_of_isTerminal_of_isCutoffBoundedSystem terminalIsTerminal
    hDc hX

end DescentSituation

end AlgebraicGeometry.Space

end
