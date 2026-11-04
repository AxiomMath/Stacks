module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Reasonableness is Zariski local

Stacks 03KE says that each of the properties `(α)` to `(θ)` of Stacks 03JX is local for the
Zariski topology: a presheaf on the big fppf site of `S` covered by open subspaces each
having the property has the property itself. This file proves the case `(δ)`,
reasonableness.

Property `(δ)` is spelled by `AlgebraicGeometry.Space.IsReasonableSpace` as condition (2) of
Stacks 03JT: every étale chart by an affine scheme has universally bounded fibres. So let
`φ : h_U ⟶ X` be such a chart. The point sets of the members of the covering are open and
cover `|X|`, so their preimages cover the affine — hence quasi-compact — scheme `U`, which
therefore has a finite cover by affine opens each mapping into a single member. Each of those
affine opens is an affine étale chart of the member it maps into, so reasonableness there
bounds its fibres over that member; the member is an open subspace, so Stacks 03JO carries
the bound over to `X`. Finally the bounds over the finitely many affine opens add up to a
bound for `φ` itself.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_isZariskiCover`: the case `(δ)` of
  Stacks 03KE.

## Implementation notes

Transferring a bound from a member `Xᵢ` of the covering to `X` is Stacks 03JO applied to the
inclusion `Xᵢ ⟶ X`: the chart `h_V ⟶ X` factors through `Xᵢ`, so its image on points lies in
that of `Xᵢ`, and the square with identity top edge is cartesian because the inclusion of an
open subspace is a monomorphism. The last step is
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_finite_openCover`, for which the
chosen affine opens must cover the points of the scheme underlying `U`, not merely its
subspace of classes.

## References

* [Stacks Project, Tag 03JO](https://stacks.math.columbia.edu/tag/03JO)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03KE, the case `(δ)`.** An algebraic space with a Zariski open covering by
reasonable open subspaces is reasonable.

Given an affine étale chart `φ : h_U ⟶ X`, the point sets of the members of the covering pull
back to an open cover of the affine scheme `U`, which therefore has a finite refinement by
affine opens each of which maps into a single member. Each of those affine opens is an affine
étale chart of the member it maps into, so reasonableness there bounds its fibres, and
Stacks 03JO carries the bound along the inclusion of the member; the finitely many bounds
then assemble to one for `φ`. -/
@[stacks 03KE "the case (delta)"]
theorem isReasonableSpace_of_isZariskiCover
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (I : Type u) (Xᵢ : I → Subfunctor X) (hcover : IsZariskiCover B S hS I Xᵢ)
    (hδ : ∀ i : I, IsReasonableSpace B S hS (Xᵢ i).toFunctor) :
    IsReasonableSpace B S hS X := by
  classical
  intro U hUaff φ hφ
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hφrep : yoneda.relativelyRepresentable φ :=
    Functor.relativelyRepresentable.diag_iff.1 hX.diagonal_representable φ
  set T := (BigFppfOver.toScheme B S hS).obj U with hT
  set e := schemePointsHomeomorph B S hS U with he
  -- the point set of each member of the covering is open, and together they cover `|X|`
  have hopen : ∀ i, IsOpen (Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι)) :=
    fun i ↦ isOpen_range_pointsMap_of_isEtale B S hS (Xᵢ i).ι (hcover.1 i).1 hX
      (isEtale_ι_of_isOpenSubspace (hcover.1 i))
  -- their preimages in the chart, read as open subsets of the scheme `T`
  set W : I → Set T := fun i ↦ e.symm ⁻¹' (pointsMap B S hS (yoneda.obj U) φ ⁻¹'
    Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι)) with hW
  have hWopen : ∀ i, IsOpen (W i) := fun i ↦
    ((hopen i).preimage (continuous_pointsMap B S hS φ)).preimage e.symm.continuous
  have hWmem : ∀ (i : I) (z : points B S hS (yoneda.obj U)),
      pointsToScheme B S hS U z ∈ W i ↔ pointsMap B S hS (yoneda.obj U) φ z ∈
        Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι) := by
    intro i z
    rw [hW]
    simp only [Set.mem_preimage]
    rw [show e.symm (pointsToScheme B S hS U z) = z from e.symm_apply_apply z]
  have hWcover : ∀ t : T, ∃ i, t ∈ W i := by
    intro t
    have hmem : pointsMap B S hS (yoneda.obj U) φ (e.symm t) ∈
        ⋃ i, Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι) := by
      rw [(isZariskiCover_iff_iUnion_points B S hS X hX I Xᵢ hcover.1).mp hcover]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact ⟨i, hi⟩
  -- a finite family of affine opens of the chart, each inside one of the `W i`
  set J := {p : Σ _ : I, T.affineOpens // ((p.2 : T.Opens) : Set T) ⊆ W p.1} with hJ
  have hJcover : (Set.univ : Set T) ⊆ ⋃ j : J, ((j.1.2 : T.Opens) : Set T) := by
    rintro t -
    obtain ⟨i, hi⟩ := hWcover t
    obtain ⟨-, ⟨V₀, hV₀, rfl⟩, htV, hVsub⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hi (hWopen i)
    exact Set.mem_iUnion.mpr ⟨⟨⟨i, ⟨V₀, hV₀⟩⟩, hVsub⟩, htV⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun j : J ↦ ((j.1.2 : T.Opens) : Set T)) (fun j ↦ (j.1.2 : T.Opens).isOpen) hJcover
  -- each affine open of the family, as an object of the site
  choose V inc hincOpen hincRange hVaff using fun j : J ↦
    BigFppfOver.exists_affineOpen_restrict B S hS U j.1.2
  have hincEtale : ∀ j : J, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map (inc j) ≫ φ) := by
    intro j
    have _ : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inc j)) := hincOpen j
    exact etale_comp_of_scheme B S hS (inc j) φ inferInstance hφ
  -- each of them factors through the member of the covering it was chosen inside
  have hfactor : ∀ j : J, ∃ g : yoneda.obj (V j) ⟶ (Xᵢ j.1.1).toFunctor,
      g ≫ (Xᵢ j.1.1).ι = yoneda.map (inc j) ≫ φ := by
    intro j
    refine (factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS (V j)) (Xᵢ j.1.1) (hcover.1 j.1.1) _).2 ?_
    rintro - ⟨w, rfl⟩
    set z := pointsMap B S hS (yoneda.obj (V j)) (yoneda.map (inc j)) w with hz
    have hmem : pointsToScheme B S hS U z ∈ ((j.1.2 : T.Opens) : Set T) := by
      rw [hz, pointsToScheme_pointsMap, ← hincRange j]
      exact Set.mem_range_self _
    rw [pointsMap_comp, Function.comp_apply]
    exact (hWmem j.1.1 z).1 (j.2 hmem)
  -- reasonableness of the member bounds its fibres, and Stacks 03JO carries that to `X`
  have hbnd : ∀ j : J, HasUniversallyBoundedFibers B S hS (V j) (yoneda.map (inc j) ≫ φ) := by
    intro j
    obtain ⟨g, hg⟩ := hfactor j
    have hgEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g :=
      MorphismProperty.presheaf_of_comp_mono _ (by rw [hg]; exact hincEtale j)
    refine hasUniversallyBoundedFibers_of_baseChange_of_range_subset B S hS hX
      (hcover.1 j.1.1).1 (Xᵢ j.1.1).ι (yoneda.map (inc j) ≫ φ) ?_
      (i := 𝟙 (yoneda.obj (V j))) (p := g) ?_ (hδ j.1.1 (V j) (hVaff j) g hgEtale)
    · rintro - ⟨w, rfl⟩
      rw [← hg, pointsMap_comp, Function.comp_apply]
      exact Set.mem_range_self _
    · rw [← hg]
      exact IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩
  -- the finitely many bounds assemble to one for the chart
  refine hasUniversallyBoundedFibers_of_finite_openCover B S hS φ hφrep
    (fun l : {j : J // j ∈ s} ↦ V l.1) (fun l ↦ inc l.1) (fun l ↦ hincOpen l.1) ?_
    fun l ↦ hbnd l.1
  intro w
  obtain ⟨j, hjs, hjmem⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ w))
  obtain ⟨z, hz⟩ : w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (inc j)) := by
    rw [hincRange j]; exact hjmem
  exact ⟨⟨j, hjs⟩, z, hz⟩

end AlgebraicGeometry.Space

end
