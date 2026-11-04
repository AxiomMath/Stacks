module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Flattening

/-!
# The flattening diagram of Stacks 0EVC is stable under base change

The conclusion of Stacks 0EVC, `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair`, survives base
change of the base: if `f₀ : X₀ ⟶ Y₀` admits the diagram of the tag over an open `V₀ ⊆ Y₀`, and
`f : X ⟶ Y` is the base change of `f₀` along `u : Y ⟶ Y₀`, then `f` admits the diagram over any
open `V ⊆ Y` contained in the inverse image of `V₀`.

This is the step by which the Stacks proof passes from the Noetherian case of the tag to the
general quasi-compact quasi-separated case: the diagram constructed over a Noetherian stage of an
absolute Noetherian approximation is base changed to the scheme itself.

## Main results

* `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.of_isPullback_of_subset`: the diagram of
  Stacks 0EVC is stable under base change of the base.

## Implementation notes

Both almost blowup squares of the base-changed diagram are base changes of the corresponding
squares upstairs, so both are almost blowup squares by Stacks 0EV7,
`AlgebraicGeometry.isAlmostBlowUpSquare_baseChange`.  The two centres match because the two
routes `X ⟶ Y₀` agree: `(Z₀·𝒪_{Y})·𝒪_X = Z₀·𝒪_X = (Z₀·𝒪_{X₀})·𝒪_X`, which is
`AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` twice.

The relative morphism of the base-changed diagram is the morphism induced into the fibre product
by the relative morphism upstairs; it is itself a base change of that morphism, which gives its
flatness and its finite presentation.  The identification is pasting: the composite of the new
relative square with the base-change square of the modification is the composite of the
base-change square of the right-hand modification with the base-change square of `f`, so
`CategoryTheory.IsPullback.of_right` applies.

Disjointness of the new centre from `V` is `AlgebraicGeometry.Scheme.IdealSheafData.support_comap`:
the support of the inverse image ideal sheaf is the inverse image of the support.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The diagram of Stacks 0EVC is stable under base change of the base.** If `f` is the base
change of `f₀` along `u : Y ⟶ Y₀`, the open `V ⊆ Y` lies in the inverse image of `V₀ ⊆ Y₀`, and
`f₀` admits the diagram of Stacks 0EVC over `V₀`, then `f` admits it over `V`. -/
public theorem HasFlatAlmostBlowUpSquarePair.of_isPullback_of_subset
    {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀} {u : Y ⟶ Y₀} {w : X ⟶ X₀}
    (hX : IsPullback f w u f₀) {V : Y.Opens} {V₀ : Y₀.Opens}
    (hV : (V : Set Y) ⊆ u ⁻¹' (V₀ : Set Y₀))
    (h : HasFlatAlmostBlowUpSquarePair f₀ V₀) :
    HasFlatAlmostBlowUpSquarePair f V := by
  obtain ⟨Z₀, Y₀', b₀, X₀', c₀, g₀, hleft₀, hright₀, hdisj₀, hw₀, hflat₀, hfp₀⟩ := h
  -- the base changes of the two modifications
  set b : pullback u b₀ ⟶ Y := pullback.fst u b₀ with hb
  set c : pullback w c₀ ⟶ X := pullback.fst w c₀ with hc
  -- the relative morphism of the base-changed diagram
  have hlift : (c ≫ f) ≫ u = (pullback.snd w c₀ ≫ g₀) ≫ b₀ := by
    rw [hc, Category.assoc, hX.w, ← Category.assoc, pullback.condition, Category.assoc, ← hw₀,
      Category.assoc]
  set g : pullback w c₀ ⟶ pullback u b₀ :=
    pullback.lift (c ≫ f) (pullback.snd w c₀ ≫ g₀) hlift with hg
  have hgb : g ≫ b = c ≫ f := pullback.lift_fst _ _ _
  -- the new relative morphism is a base change of the old one
  have hgpb : IsPullback g (pullback.snd w c₀) (pullback.snd u b₀) g₀ := by
    refine IsPullback.of_right (h₁₂ := b) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback u b₀)
    rw [hgb, hw₀]
    exact (IsPullback.of_hasPullback w c₀).paste_horiz hX
  -- the two centres of the base-changed diagram agree
  have hcentre : (Z₀.comap f₀).comap w = (Z₀.comap u).comap f := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hX.w]
  refine ⟨Z₀.comap u, pullback u b₀, b, pullback w c₀, c, g,
    isAlmostBlowUpSquare_baseChange Z₀ b₀ u hleft₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcentre ▸ isAlmostBlowUpSquare_baseChange (Z₀.comap f₀) c₀ w hright₀
  · have hsupp : ((Z₀.comap u).support : Set Y) = u ⁻¹' (Z₀.support : Set Y₀) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    rw [hsupp]
    refine Set.disjoint_left.2 fun a haV haZ => ?_
    exact Set.disjoint_left.1 hdisj₀ (hV haV) haZ
  · exact hgb
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hgpb.flip hflat₀
  · exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hgpb.flip
        hfp₀.locallyOfFinitePresentation,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hgpb.flip hfp₀.quasiCompact,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hgpb.flip hfp₀.quasiSeparated⟩

end AlgebraicGeometry

end
