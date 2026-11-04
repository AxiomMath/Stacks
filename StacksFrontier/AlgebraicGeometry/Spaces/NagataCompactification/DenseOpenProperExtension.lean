module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalBoundary
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure

/-!
# A separated extension of a dense open immersion

Let `ψ : V ⟶ U` be a separated morphism of algebraic spaces and let `j : U₂ ⟶ V` be a morphism
with dense image such that `j ≫ ψ` is an open immersion. Then `ψ⁻¹(U₂) = U₂`: every point of `V`
whose image in `U` lies in `U₂` lies in the image of `j`. Indeed `j` is a section of the
separated morphism `ψ⁻¹(U₂) ⟶ U₂`, hence proper (Stacks 04NX), so its image is closed in the
open subset `ψ⁻¹(U₂)` of `|V|`, in which it is dense.

In the proof of Stacks 0F4B this is applied to the proper extension `ψ₂ : V₂ ⟶ U` of the open
immersion `U₂ ⟶ U`, with `U₂` dense in `V₂`: the complement `V₂ ∖ U₂` is then `ψ₂⁻¹(Z₁)`, where
`Z₁ = U ∖ U₂`.

## Main results

* `AlgebraicGeometry.Space.preimage_range_subset_range_of_denseRange`: the general form, for
  `j ≫ ψ` factoring as a proper morphism followed by an open immersion.
* `AlgebraicGeometry.Space.preimage_range_comp_subset_range_of_denseRange`: `ψ⁻¹(U₂) ⊆ U₂`.

## References

* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **A dense morphism over an open immersion, through a proper map, fills its preimage.** Let
`ψ : V ⟶ X` be separated, `ι : W ⟶ X` an open immersion and `j : U₂ ⟶ V` a morphism with dense
image such that `j ≫ ψ = a ≫ ι` for a proper `a : U₂ ⟶ W`. Then every point of `V` whose image
lies in the image of `ι` lies in the image of `j`: `j` factors through `ψ⁻¹(W)` by a proper
morphism (Stacks 04NX), so its image is closed in the open set `ψ⁻¹(W)`, in which it is dense. -/
theorem preimage_range_subset_range_of_denseRange {X V W U₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (hU₂ : IsAlgebraicSpace B S hS U₂) {ψ : V ⟶ X}
    (hψ : IsSeparated B S hS ψ) {ι : W ⟶ X} (hι : IsOpenImmersion B S hS ι) {j : U₂ ⟶ V}
    {a : U₂ ⟶ W} (ha : IsProper B S hS a) (h : j ≫ ψ = a ≫ ι)
    (hd : DenseRange (pointsMap B S hS U₂ j)) :
    pointsMap B S hS V ψ ⁻¹' Set.range (pointsMap B S hS W ι) ⊆
      Set.range (pointsMap B S hS U₂ j) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  set Ui := Subfunctor.range ι with hUi
  have hUio : IsOpenSubspace B S hS Ui := isOpenSubspace_subfunctorRange B S hS hW hι
  set P := Ui.preimage ψ with hP
  have hPo : IsOpenSubspace B S hS P := isOpenSubspace_preimage B S hS ψ Ui hX hV hUio
  have hle : Subfunctor.range j ≤ P := by
    rw [hP, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp, h]
    exact Subfunctor.range_comp_le a ι
  let j' : U₂ ⟶ P.toFunctor := Subfunctor.lift j hle
  have hj' : j' ≫ P.ι = j := Subfunctor.lift_ι _ _
  have hj'ψ : j' ≫ Ui.fromPreimage ψ = a ≫ Subfunctor.toRange ι := by
    refine (cancel_mono Ui.ι).1 ?_
    rw [Category.assoc, Subfunctor.fromPreimage_ι, reassoc_of% hj', Category.assoc,
      Subfunctor.toRange_ι, h]
  have hsep : IsSeparated B S hS (Ui.fromPreimage ψ) := by
    refine isSeparated_of_comp_mono _ Ui.ι inferInstance ?_
    rw [Subfunctor.fromPreimage_ι]
    exact isSeparated_comp B S hS _ _
      (isSeparated_of_mono (B := B) (S := S) (hS := hS) _ inferInstance) hψ
  have hprop : IsProper B S hS j' := by
    refine isProper_of_comp_of_isSeparated B S hS hU₂ hPo.1 hUio.1 j' _ ?_ hsep
    rw [hj'ψ]
    exact isProper_comp B S hS hU₂ hW hUio.1 _ _ ha (isProper_of_isIso B S hS _)
  have hcl := isClosed_range_pointsMap_of_isProper B S hS hPo.1 hprop
  have hemb : IsOpenEmbedding (pointsMap B S hS _ P.ι) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS P.ι)
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hPo.2)
  have huniv : Set.range (pointsMap B S hS U₂ j') = Set.univ := by
    rw [← hcl.closure_eq, hemb.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp,
      ← pointsMap_comp, hj', hd.closure_range, Set.preimage_univ]
  intro v hv
  have hvP : v ∈ subspacePointSet B S hS V P := by
    rw [hP, subspacePointSet_preimage, hUi, subspacePointSet_range]
    exact hv
  obtain ⟨p, rfl⟩ := hvP
  obtain ⟨u, hu⟩ : p ∈ Set.range (pointsMap B S hS U₂ j') := huniv ▸ Set.mem_univ p
  exact ⟨u, by rw [← hj', pointsMap_comp_apply, hu]⟩

/-- **A separated extension of a dense open immersion is an isomorphism over its image.** Let
`ψ : V ⟶ U` be separated and `j : U₂ ⟶ V` have dense image, with `j ≫ ψ` an open immersion.
Then every point of `V` whose image lies in the image of `U₂` lies in the image of `j`. -/
theorem preimage_range_comp_subset_range_of_denseRange {U V U₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hU₂ : IsAlgebraicSpace B S hS U₂) {ψ : V ⟶ U} (hψ : IsSeparated B S hS ψ) {j : U₂ ⟶ V}
    (hi : IsOpenImmersion B S hS (j ≫ ψ)) (hd : DenseRange (pointsMap B S hS U₂ j)) :
    pointsMap B S hS V ψ ⁻¹' Set.range (pointsMap B S hS U₂ (j ≫ ψ)) ⊆
      Set.range (pointsMap B S hS U₂ j) :=
  preimage_range_subset_range_of_denseRange hU hV hU₂ hU₂ hψ hi (isProper_of_isIso B S hS (𝟙 U₂))
    (Category.id_comp _).symm hd

end AlgebraicGeometry.Space

end
