module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject

/-!
# An étale chart with exactly one point above a quasi-compact field-valued point

Let `Y` be an algebraic space over a scheme `S` and let `p` be a field-valued point of `Y`
whose presenting morphism `Spec k ⟶ Y` is quasi-compact. Then `Y` has an étale scheme chart
with *exactly one* point above the point `y` presented by `p`.

This is the shrinking step of the argument of **Stacks 0AC8**: that argument starts from an
affine étale chart with finitely many points above `y` and replaces it by one with a single
point there, which is what makes the point set of a base change along the chart meet the fibre
over `y` in a recognisable way.

## Main results

* `AlgebraicGeometry.Space.exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism`:
  an étale chart whose fibre above `y` is a singleton.

## Implementation notes

Quasi-compactness of `Spec k ⟶ Y` makes the fibre above `y` of every étale chart with
quasi-compact underlying scheme finite, which is
`AlgebraicGeometry.Space.finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism`. Taking an
affine chart through `y` gives a finite fibre `F` containing a chosen point `a` above `y`.

By Stacks 03IM no point of `F` other than `a` has `a` in its closure: two points of a chart
above the same point of the space, one a specialization of the other, are equal. Since `F` is
finite, the union of the closures of the other points of `F` is therefore a closed set missing
`a`, and its complement `W` is an open neighbourhood of `a` meeting `F` exactly in `{a}`.
Finiteness is used only here, to know that the union is closed.

Restricting the chart to `W` — transported to an open subscheme along the comparison
homeomorphism of Stacks 03BX — gives the required chart. The restriction is again étale, the
open inclusion being étale, and its map on points is injective with image `W`, the open
inclusion being an embedding. So its fibre above `y` is the preimage of `F ∩ W = {a}` under an
injection whose image contains `a`, namely a single point.

The conclusion does not assert that the shrunk chart is affine, and it need not be: affineness
is used only to obtain the finite fibre, before shrinking. Nor is the presenting morphism
required to be a monomorphism, which the consumers of this lemma need for other reasons.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03IM](https://stacks.math.columbia.edu/tag/03IM)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The shrinking step of Stacks 0AC8. If the morphism presenting a field-valued point `p` of
an algebraic space `Y` over `S` is quasi-compact, then `Y` has an étale scheme chart whose
fibre above the point presented by `p` is a single point. -/
theorem exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism
    (hY : IsAlgebraicSpace B S hS Y) (p : FieldValuedPoint B S hS Y)
    (hp : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    ∃ (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ Y) (v : points B S hS (yoneda.obj V)),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ψ ∧
      pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS Y} = {v} := by
  classical
  -- Every étale chart by an affine scheme has a finite fibre above the point `p` presents.
  have hfin : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ χ : yoneda.obj V ⟶ Y, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf χ →
      (pointsMap B S hS (yoneda.obj V) χ ⁻¹' {p.class B S hS Y}).Finite := by
    intro V hV χ hχ
    have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := by
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
      infer_instance
    exact finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism B S hS p hp hcpt χ hχ
  -- An affine étale chart through that point.
  obtain ⟨U, φ, a, hUaff, hφ, ha⟩ :=
    exists_affine_etale_chart_of_point B S hS Y hY (p.class B S hS Y)
  -- An open neighbourhood of `a` in the chart meeting the fibre only in `a`: by Stacks 03IM
  -- no other point of the fibre has `a` in its closure, and the fibre is finite, so the union
  -- of the closures of the others is closed and misses `a`.
  obtain ⟨W, hWopen, haW, hFW⟩ :
      ∃ W : Set (points B S hS (yoneda.obj U)), IsOpen W ∧ a ∈ W ∧
        (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {p.class B S hS Y}) ∩ W = {a} := by
    have hFfin : (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {p.class B S hS Y}).Finite :=
      hfin U hUaff φ hφ
    have haW : a ∈ (⋃ u ∈ (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {p.class B S hS Y}) \ {a},
        closure ({u} : Set (points B S hS (yoneda.obj U))))ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop, not_exists, not_and]
      rintro u ⟨huF, hua⟩ hmem
      exact (by simpa using hua : u ≠ a)
        (eq_of_specializes_of_pointsMap_eq B S hS hY (p.class B S hS Y) hfin U φ hφ a u ha huF
          (specializes_iff_mem_closure.mpr hmem)).symm
    refine ⟨_, (Set.Finite.isClosed_biUnion (hFfin.subset Set.sdiff_subset)
      fun u _ ↦ isClosed_closure).isOpen_compl, haW, ?_⟩
    refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ⟨ha, haW⟩)
    rintro z ⟨hzF, hzW⟩
    by_contra hza
    exact hzW (Set.mem_biUnion ⟨hzF, by simpa using hza⟩ (subset_closure rfl))
  -- Transport `W` to an open subscheme of the chart.
  obtain ⟨Wop, hWcoe⟩ : ∃ O : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      (O : Set ((BigFppfOver.toScheme B S hS).obj U)) = pointsToScheme B S hS U '' W :=
    ⟨⟨_, (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U W).mp hWopen⟩, rfl⟩
  have hWpre : pointsToScheme B S hS U ⁻¹' (Wop : Set _) = W := by
    rw [hWcoe]
    exact Set.preimage_image_eq W (injective_pointsToScheme B S hS U)
  -- The restriction of the chart to it is again étale.
  have hjetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (openSiteObjectHom B S hS U Wop)) :=
    presheaf_etale_yonedaMap_openSiteObjectHom B S hS U Wop
  have hQEc := inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hQEpc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  -- Its map on points is injective with image `W`.
  have hjemb : Topology.IsEmbedding
      ⇑((BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U Wop)) := by
    rw [map_openSiteObjectHom]
    exact Wop.ι.isEmbedding
  have hjinj : Function.Injective (pointsMap B S hS (yoneda.obj _)
      (yoneda.map (openSiteObjectHom B S hS U Wop))) :=
    (isEmbedding_pointsMap_yoneda B S hS (openSiteObjectHom B S hS U Wop) hjemb).injective
  have hjrange : Set.range (pointsMap B S hS (yoneda.obj _)
      (yoneda.map (openSiteObjectHom B S hS U Wop))) = W := by
    rw [← hWpre, range_pointsMap_yoneda_eq_preimage B S hS (openSiteObjectHom B S hS U Wop)]
    rw [map_openSiteObjectHom]
    exact congrArg (pointsToScheme B S hS U ⁻¹' ·) Wop.range_ι
  obtain ⟨v, hv⟩ : a ∈ Set.range (pointsMap B S hS (yoneda.obj _)
      (yoneda.map (openSiteObjectHom B S hS U Wop))) := by
    rw [hjrange]; exact haW
  -- Hence its fibre is the single preimage of `a`.
  refine ⟨openSiteObject B S hS U Wop, yoneda.map (openSiteObjectHom B S hS U Wop) ≫ φ, v,
    MorphismProperty.comp_mem _ _ φ hjetale hφ, ?_⟩
  have hcomp : ∀ w, pointsMap B S hS (yoneda.obj (openSiteObject B S hS U Wop))
      (yoneda.map (openSiteObjectHom B S hS U Wop) ≫ φ) w =
      pointsMap B S hS (yoneda.obj U) φ (pointsMap B S hS (yoneda.obj _)
        (yoneda.map (openSiteObjectHom B S hS U Wop)) w) := fun w ↦
    pointsMap_comp_apply B S hS (yoneda.map (openSiteObjectHom B S hS U Wop)) φ w
  refine Set.Subset.antisymm (fun w hw ↦ ?_) (fun w hw ↦ ?_)
  · have hwF : pointsMap B S hS (yoneda.obj _)
        (yoneda.map (openSiteObjectHom B S hS U Wop)) w ∈
        pointsMap B S hS (yoneda.obj U) φ ⁻¹' {p.class B S hS Y} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hcomp w] at hw
      exact hw
    have hwW : pointsMap B S hS (yoneda.obj _)
        (yoneda.map (openSiteObjectHom B S hS U Wop)) w ∈ W := by
      rw [← hjrange]; exact ⟨w, rfl⟩
    have hwa : pointsMap B S hS (yoneda.obj _)
        (yoneda.map (openSiteObjectHom B S hS U Wop)) w = a := by
      rw [← Set.mem_singleton_iff, ← hFW]; exact ⟨hwF, hwW⟩
    exact hjinj (hwa.trans hv.symm)
  · rw [Set.mem_singleton_iff] at hw
    rw [hw, Set.mem_preimage, Set.mem_singleton_iff, hcomp v, hv]
    exact ha

end AlgebraicGeometry.Space

end
