module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NonemptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Descending a covering by opens along a limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system `D` of quasi-compact algebraic
spaces over a scheme `S` with affine transition morphisms, as in Situation 084R. If an open
subset of the point space of a stage `D i₀` has inverse image the whole of `|X|`, then its
inverse image in some later stage is the whole of that stage.

This is the algebraic-space form of part (3) of [Stacks, Tag 01Z4], whose scheme-level form is
`AlgebraicGeometry.exists_iSup_map_preimage_eq_top`.

## Main results

* `AlgebraicGeometry.Space.exists_stage_preimage_eq_univ`: the point-set statement, for a
  single open.
* `AlgebraicGeometry.Space.exists_stage_iUnion_preimage_eq_univ`: the same for a family of
  opens, in the form "the inverse images cover".

## Implementation notes

The statement is reduced to its scheme-level form `AlgebraicGeometry.exists_map_eq_top'` through
the affine chart system of an affine surjective étale chart of the stage `D i₀`
([Stacks, Tag 03H6]), each chart of which is surjective onto its stage.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points -/

/-- The map on points induced by the identity is the identity. -/
theorem pointsMap_id' (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (x : points B S hS F) :
    pointsMap B S hS F (𝟙 F) x = x := by
  induction x using Quot.inductionOn with
  | h p => rfl

/-! ### Transporting an open along the point-space homeomorphism -/

/-- The preimage of an open of a represented presheaf, carried to the representing scheme by
the homeomorphism of Stacks 03BX (1), is the image under that homeomorphism of the preimage
taken on points. -/
theorem preimage_toScheme_map_preimage_schemePointsHomeomorph_symm
    {U U' : BigFppfOver B S hS} (φ : U ⟶ U')
    (A : Set (points B S hS (yoneda.obj U'))) :
    (BigFppfOver.toScheme B S hS).map φ ⁻¹'
        ((schemePointsHomeomorph B S hS U').symm ⁻¹' A) =
      (schemePointsHomeomorph B S hS U).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj U) (yoneda.map φ) ⁻¹' A) := by
  ext y
  obtain ⟨x, rfl⟩ := (schemePointsHomeomorph B S hS U).surjective y
  have hnat : (BigFppfOver.toScheme B S hS).map φ (schemePointsHomeomorph B S hS U x) =
      schemePointsHomeomorph B S hS U'
        (pointsMap B S hS (yoneda.obj U) (yoneda.map φ) x) :=
    (pointsToScheme_pointsMap B S hS φ x).symm
  simp only [Set.mem_preimage, hnat, Homeomorph.symm_apply_apply]

/-- The point of a represented presheaf underlying the image of a scheme point under a
morphism of the site is the image of the underlying point under the induced map on points. -/
theorem schemePointsHomeomorph_symm_toScheme_map {U U' : BigFppfOver B S hS} (φ : U ⟶ U')
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    (schemePointsHomeomorph B S hS U').symm ((BigFppfOver.toScheme B S hS).map φ y) =
      pointsMap B S hS (yoneda.obj U) (yoneda.map φ)
        ((schemePointsHomeomorph B S hS U).symm y) := by
  rw [Homeomorph.symm_apply_eq]
  simp only [schemePointsHomeomorph_apply]
  rw [pointsToScheme_pointsMap B S hS φ]
  congr 1
  exact ((schemePointsHomeomorph B S hS U).apply_symm_apply y).symm

/-- A scheme-level preimage of an open of points is everything iff the preimage on points is. -/
private theorem preimage_toScheme_map_eq_univ_iff {U U' : BigFppfOver B S hS} (φ : U ⟶ U')
    (A : Set (points B S hS (yoneda.obj U'))) :
    (BigFppfOver.toScheme B S hS).map φ ⁻¹' ((schemePointsHomeomorph B S hS U').symm ⁻¹' A) =
        Set.univ ↔
      pointsMap B S hS (yoneda.obj U) (yoneda.map φ) ⁻¹' A = Set.univ := by
  rw [preimage_toScheme_map_preimage_schemePointsHomeomorph_symm, Set.preimage_eq_univ_iff,
    (schemePointsHomeomorph B S hS U).symm.surjective.range_eq, Set.univ_subset_iff]

/-! ### Descending a covering -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Part (3) of Stacks 01Z4 for algebraic spaces.** Let `X = limit D` be the limit of a
cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine transition
morphisms, the index category being small enough for the site. If an open subset `V` of the
point space of a stage `D i₀` has inverse image the whole of `|X|`, then there is a later
stage `j` at which the inverse image of `V` is the whole of `|D j|`. -/
theorem exists_stage_preimage_eq_univ (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
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
  set L := C.limitBridge hSize hHomSize
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
    refine TopologicalSpace.Opens.ext
      ((preimage_toScheme_map_eq_univ_iff B S hS (L.cone.π.app o₀) Vo).mpr ?_)
    refine Set.eq_univ_of_forall fun p ↦ ?_
    change (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj o₀)) (C.stageMap o₀) ∘
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app o₀))) p ∈ V
    rw [← pointsMap_comp, ← L.toLimit_comp_limitπ o₀, pointsMap_comp]
    exact Set.eq_univ_iff_forall.mp hlim _
  obtain ⟨j, g, hj⟩ := exists_map_eq_top' C.schemeDiagram
    ((BigFppfOver.toScheme B S hS).mapCone L.cone) L.schemeIsLimit W hW
  refine ⟨j.left, g.left, ?_⟩
  have hchart := (preimage_toScheme_map_eq_univ_iff B S hS (C.siteDiagram.map g) Vo).mp
    (congrArg SetLike.coe hj)
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
        (yoneda.map (C.siteDiagram.map g))) w ∈ V := Set.eq_univ_iff_forall.mp hchart w
  rw [← pointsMap_comp, hnat, pointsMap_comp] at hV'
  simpa only [Set.mem_preimage, Function.comp_apply, hw] using hV'

/-- **Part (3) of Stacks 01Z4 for algebraic spaces, for a family.** If the inverse images in
the limit of a family of open subsets of the point space of a stage cover the limit, then
their inverse images in some later stage cover that stage. -/
theorem exists_stage_iUnion_preimage_eq_univ (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {ι : Type*} (V : ι → Set (points B S hS (D.obj i₀)))
    (hV : ∀ k, IsOpen (V k))
    (hlim : ⋃ k, pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V k = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀),
      ⋃ k, pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V k = Set.univ := by
  obtain ⟨j, g, hj⟩ := exists_stage_preimage_eq_univ B S hS D hSize hHomSize hD hAffine
    hCompact i₀ (V := ⋃ k, V k) (isOpen_iUnion hV) (by rwa [Set.preimage_iUnion])
  exact ⟨j, g, by rwa [← Set.preimage_iUnion]⟩

end AlgebraicGeometry.Space

end
