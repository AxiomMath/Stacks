module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendCoverings
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NonemptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Descending coverings by open subspaces, under the site-containment hypothesis

The covering statements of `StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendCoverings.lean`
under `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

* `AlgebraicGeometry.Space.exists_stage_preimage_eq_univ_of_siteContainsBaseChangeLimits`
* `AlgebraicGeometry.Space.exists_stage_preimage_eq_univ_of_isSiteSmall`
* `AlgebraicGeometry.Space.exists_stage_iUnion_preimage_eq_univ_of_siteContainsBaseChangeLimits`
* `AlgebraicGeometry.Space.exists_stage_iUnion_preimage_eq_univ_of_isSiteSmall`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points -/

/-! ### Transporting an open along the point-space homeomorphism -/

/-! ### Descending a covering -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Part (3) of Stacks 01Z4 for algebraic spaces, under the chapter's standing convention.**
If an open subset `V` of the point space of a stage `D i₀` has inverse image the whole of `|X|`,
where `X = limit D`, then there is a later stage at which the inverse image of `V` is everything.

This is `AlgebraicGeometry.Space.exists_stage_preimage_eq_univ_of_isSiteSmall` with its smallness
hypothesis replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: smallness entered only to place the limit
of one chart system in the site, which is what the convention grants. Nothing is asked of the
index. -/
theorem exists_stage_preimage_eq_univ_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {V : Set (points B S hS (D.obj i₀))} (hV : IsOpen V)
    (hlim : pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀), pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V = Set.univ := by
  classical
  -- An affine surjective étale chart of the stage `i₀`, by Stacks 03H6.
  obtain ⟨V₀, f₀, hV₀, hf₀surj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i₀)
      (hD i₀)).mp (hCompact i₀)
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V₀) f₀) :=
    (surjective_iff_surjective_pointsMap B S hS (D.obj i₀) (hD i₀) V₀ f₀).mp hf₀surj
  set C := affineChartSystem B S hS i₀ D ⟨V₀, hV₀⟩ f₀ hAffine with hC
  set L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)
    with hL
  -- Each chart is surjective onto its own stage, being a base change of `f₀`.
  have hstage : ∀ j : Over i₀,
      Function.Surjective
        (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j)) := by
    intro j x
    obtain ⟨y, hy⟩ := hsurj (pointsMap B S hS (D.obj j.left) (D.map j.hom) x)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (C.isPullback j) x y hy.symm
    exact ⟨w, hw⟩
  -- The chart system is a cofiltered system of quasi-compact schemes with affine transitions.
  have _ : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have _ : ∀ j, CompactSpace (C.schemeDiagram.obj j) := fun j ↦ inferInstance
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  -- The open of the chart at the terminal stage of the slice.
  let o₀ : Over i₀ := Over.mk (𝟙 i₀)
  let Vo : Set (points B S hS (yoneda.obj (C.siteDiagram.obj o₀))) :=
    pointsMap B S hS _ (C.stageMap o₀) ⁻¹' V
  have hVo : IsOpen Vo := hV.preimage (continuous_pointsMap B S hS (C.stageMap o₀))
  let W : (C.schemeDiagram.obj o₀).Opens :=
    ⟨(schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm ⁻¹' Vo,
      hVo.preimage (schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm.continuous⟩
  -- Its inverse image in the limit of the chart system is everything.
  have hW : ((BigFppfOver.toScheme B S hS).mapCone L.cone).π.app o₀ ⁻¹ᵁ W = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y ↦ ?_)
    change (schemePointsHomeomorph B S hS (C.siteDiagram.obj o₀)).symm
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app o₀) y) ∈ Vo
    rw [schemePointsHomeomorph_symm_toScheme_map]
    change (pointsMap B S hS (yoneda.obj (C.siteDiagram.obj o₀)) (C.stageMap o₀) ∘
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app o₀)))
      ((schemePointsHomeomorph B S hS L.cone.pt).symm y) ∈ V
    rw [← pointsMap_comp, ← L.toLimit_comp_limitπ o₀, pointsMap_comp]
    have hmem : pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit
        ((schemePointsHomeomorph B S hS L.cone.pt).symm y) ∈
        pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V := by
      rw [hlim]; trivial
    exact hmem
  -- The scheme-level statement, part (3) of Stacks 01Z4.
  obtain ⟨j, g, hj⟩ := exists_map_eq_top' C.schemeDiagram
    ((BigFppfOver.toScheme B S hS).mapCone L.cone) L.schemeIsLimit W hW
  -- Transport back: the open is everything on the chart at `j`, hence on the stage `j.left`.
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
  -- Naturality of the chart projections against the transition morphisms.
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

/-- **Part (3) of Stacks 01Z4 for algebraic spaces.** Let `X = limit D` be the limit of a
cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine transition
morphisms, the index category being small enough for the site. If an open subset `V` of the
point space of a stage `D i₀` has inverse image the whole of `|X|`, then there is a later
stage `j` at which the inverse image of `V` is the whole of `|D j|`.

Quasi-separatedness of the stages, which Situation 084R also assumes, is not needed.

This is the algebraic-space analogue of part (3) of Stacks 01Z4, not that part itself: the
tag is stated for a limit of schemes and their opens, and part (3) of it is already carried by
`AlgebraicGeometry.exists_iSup_map_preimage_eq_top`. So this declaration carries no tag. -/
theorem exists_stage_preimage_eq_univ_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {V : Set (points B S hS (D.obj i₀))} (hV : IsOpen V)
    (hlim : pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀), pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V = Set.univ :=
  exists_stage_preimage_eq_univ_of_siteContainsBaseChangeLimits B S hS D
      (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hD hAffine
    hCompact i₀ hV hlim

/-- **Part (3) of Stacks 01Z4 for algebraic spaces, for a family, under the chapter's standing
convention.** This is
`AlgebraicGeometry.Space.exists_stage_iUnion_preimage_eq_univ_of_isSiteSmall` with its smallness
hypothesis replaced by `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. -/
theorem exists_stage_iUnion_preimage_eq_univ_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {ι : Type*} (V : ι → Set (points B S hS (D.obj i₀)))
    (hV : ∀ k, IsOpen (V k))
    (hlim : ⋃ k, pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V k = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀),
      ⋃ k, pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V k = Set.univ := by
  obtain ⟨j, g, hj⟩ :=
    exists_stage_preimage_eq_univ_of_siteContainsBaseChangeLimits B S hS D hconv hD
    hAffine
    hCompact i₀ (V := ⋃ k, V k) (isOpen_iUnion hV) (by rwa [Set.preimage_iUnion])
  exact ⟨j, g, by rwa [← Set.preimage_iUnion]⟩

/-- **Part (3) of Stacks 01Z4 for algebraic spaces, for a family.** If the inverse images in
the limit of a family of open subsets of the point space of a stage cover the limit, then
their inverse images in some later stage cover that stage.

As at the scheme level, neither finiteness of the family nor quasi-compactness of its members
is needed: a preimage commutes with unions, so the statement for the family is the statement
for its union.

As above, this is the algebraic-space analogue of part (3) of Stacks 01Z4 rather than that
part itself, so it carries no tag. -/
theorem exists_stage_iUnion_preimage_eq_univ_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (i₀ : I) {ι : Type*} (V : ι → Set (points B S hS (D.obj i₀)))
    (hV : ∀ k, IsOpen (V k))
    (hlim : ⋃ k, pointsMap B S hS (limit D) (limit.π D i₀) ⁻¹' V k = Set.univ) :
    ∃ (j : I) (g : j ⟶ i₀),
      ⋃ k, pointsMap B S hS (D.obj j) (D.map g) ⁻¹' V k = Set.univ :=
  exists_stage_iUnion_preimage_eq_univ_of_siteContainsBaseChangeLimits B S hS D
      (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hD
    hAffine hCompact i₀ V hV hlim

end AlgebraicGeometry.Space

end
