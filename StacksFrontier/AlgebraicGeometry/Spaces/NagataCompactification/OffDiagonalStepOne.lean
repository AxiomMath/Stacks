module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The self-intersection of a proper extension inside `X ×_Y X`

Let `π : X ⟶ Y` be separated, `V ⊆ X` open and `ψ : V ⟶ U` proper over `Y`, with `U ⟶ Y`
separated. The points of `X ×_Y X` with first coordinate in `V` form the open subspace
`V ×_Y X`, and inside it the image of `V ×_U V` is closed, because `V ×_U V ⟶ V ×_Y X` is proper.
This is Lemma 1 of the repaired proof of Stacks 0F4B: a point of `X ×_Y X` in the closure of a
subset of the image of `V ×_U V` whose first coordinate lies in `V` lies in that image.

## Main results

* `AlgebraicGeometry.Space.isPullback_pullbackMap_ι_fst`: `V ×_Y X` is the inverse image of `V`
  under the first projection of `X ×_Y X`.
* `AlgebraicGeometry.Space.isProper_pullbackMap_of_isProper`: `V ×_U V ⟶ V ×_Y X` is proper.
* `AlgebraicGeometry.Space.mem_range_of_mem_closure_of_fst_mem`: Lemma 1.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_OffDiagonalStepOne
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **`V ×_Y X` is the inverse image of `V` in `X ×_Y X`.** For a morphism `ι : V ⟶ X`, the
comparison `V ×_Y X ⟶ X ×_Y X` is the base change of `ι` along the first projection. -/
theorem isPullback_pullbackMap_ι_fst {V X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : V ⟶ X)
    (π : X ⟶ Y) :
    IsPullback (pullback.map (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp))
      (pullback.fst (ι ≫ π) π) (pullback.fst π π) ι :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (ι ≫ π) π).flip)
    (by simp) (IsPullback.of_hasPullback π π).flip

/-- **The self-intersection of a proper extension is proper over `V ×_Y X`.** If `ψ : V ⟶ U` is
proper, `ι : V ⟶ X`, `ψ ≫ q = ι ≫ π` and `π` is separated, then `V ×_U V ⟶ V ×_Y X`,
`(v, v') ↦ (v, ι v')`, is proper: its composite with the first projection is the base change of
`ψ`, and that projection is separated (Stacks 04NX). -/
theorem isProper_pullbackMap_of_isProper {V U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {ψ : V ⟶ U} {ι : V ⟶ X} {q : U ⟶ Y} {π : X ⟶ Y} (hψ : IsProper B S hS ψ)
    (hπ : IsSeparated B S hS π) (h : ψ ≫ q = ι ≫ π) :
    IsProper B S hS (pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h) := by
  have hfst : IsSeparated B S hS (pullback.fst (ι ≫ π) π) :=
    isSeparated_pullback_fst_of_snd B S hS π (ι ≫ π) (isSeparated_pullback B S hS π (ι ≫ π) hπ)
  refine isProper_of_comp_of_isSeparated B S hS
    (isAlgebraicSpace_pullback B S hS ψ ψ hV hV hU)
    (isAlgebraicSpace_pullback B S hS (ι ≫ π) π hV hX hY) hV _ _ ?_ hfst
  rw [pullback.lift_fst, Category.comp_id]
  exact isProper_pullback_fst B S hS hV hU hV ψ ψ hψ

section PointTopology

attribute [local instance] pointTopology

/-- **Lemma 1 of the repaired proof of Stacks 0F4B.** In the situation of
`AlgebraicGeometry.Space.isProper_pullbackMap_of_isProper`, with `ι` an open immersion, let `O`
be a set of points of `X ×_Y X` lying in the image of `V ×_U V`. Then every point of the closure
of `O` whose first coordinate lies in `V` lies in the image of `V ×_U V`. -/
theorem mem_range_of_mem_closure_of_fst_mem {V U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {ψ : V ⟶ U} {ι : V ⟶ X} {q : U ⟶ Y} {π : X ⟶ Y} (hψ : IsProper B S hS ψ)
    (hπ : IsSeparated B S hS π) (hι : IsOpenImmersion B S hS ι) (h : ψ ≫ q = ι ≫ π)
    {O : Set (points B S hS (pullback π π))}
    (hO : O ⊆ Set.range (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp))))
    {w : points B S hS (pullback π π)} (hw : w ∈ closure O)
    (hw₁ : pointsMap B S hS _ (pullback.fst π π) w ∈ Set.range (pointsMap B S hS V ι)) :
    w ∈ Set.range (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp))) := by
  set a := pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h
  set j := pullback.map (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp)
  have sq := isPullback_pullbackMap_ι_fst B S hS ι π
  have hj : IsOpenImmersion B S hS j :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback sq.flip hι
  have hjmono : Mono j := mono_of_presheaf_isOpenImmersion hj
  have hrange : Set.range (pointsMap B S hS _ j) =
      pointsMap B S hS _ (pullback.fst π π) ⁻¹' Set.range (pointsMap B S hS V ι) := by
    have := preimage_image_pointsMap_of_isPullback B S hS sq.flip Set.univ
    simpa [Set.image_univ] using this.symm
  have hemb : Topology.IsOpenEmbedding (pointsMap B S hS _ j) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hj)
  have hclosed : IsClosed (Set.range (pointsMap B S hS _ a)) :=
    isClosed_range_pointsMap_of_isProper B S hS
      (isAlgebraicSpace_pullback B S hS (ι ≫ π) π hV hX hY)
      (isProper_pullbackMap_of_isProper B S hS hV hU hX hY hψ hπ h)
  obtain ⟨w₁, rfl⟩ : w ∈ Set.range (pointsMap B S hS _ j) := by rw [hrange]; exact hw₁
  have hsub : pointsMap B S hS _ j ⁻¹' O ⊆ Set.range (pointsMap B S hS _ a) := by
    intro z hz
    obtain ⟨r, hr⟩ := hO hz
    rw [pointsMap_comp_apply] at hr
    exact ⟨r, hemb.injective hr⟩
  have hw₁cl : w₁ ∈ closure (pointsMap B S hS _ j ⁻¹' O) :=
    hemb.isOpenMap.preimage_closure_subset_closure_preimage hw
  obtain ⟨r, hr⟩ := hclosed.closure_subset_iff.2 hsub hw₁cl
  exact ⟨r, by rw [pointsMap_comp_apply, hr]⟩

end PointTopology

end AlgebraicGeometry.Space

end
