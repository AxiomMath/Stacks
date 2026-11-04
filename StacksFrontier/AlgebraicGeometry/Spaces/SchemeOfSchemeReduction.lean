module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace

/-!
# An algebraic space whose reduction is a scheme is a scheme (Stacks 049D, 07VU)

Decent Spaces, Remark 049D, records that an algebraic space whose reduction is a scheme is a
scheme, which is Limits of Spaces, Lemma 07VU. Being a scheme is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`: if a closed
  immersion of algebraic spaces over `S` is bijective on points and its source is a scheme, then
  its target is a scheme.
* `AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction`:
  **Stacks 049D**, an algebraic space whose reduction is a scheme is a scheme.

## References

* [Stacks Project, Tag 049D](https://stacks.math.columbia.edu/tag/049D)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The target of a bijective closed immersion with scheme source is a scheme.** If
`f : F ⟶ G` is a closed immersion of algebraic spaces over `S` inducing a bijection on points and
`F` is a scheme, then `G` is a scheme. -/
theorem isRepresentable_of_isClosedImmersion_of_bijective
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsClosedImmersion B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable) :
    G.IsRepresentable := by
  classical
  let _ : F.IsRepresentable := hFrep
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      (universallyClosed_of_isClosedImmersion B S hS hF hG f hf)
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ : ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS α ∧
        x ∈ Set.range (pointsMap B S hS (yoneda.obj V) α) := by
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS (Functor.reprX F)
      (Functor.reprW F) p
    refine ⟨affineChart B S hS (Functor.reprX F) i,
      yoneda.map (affineChartι B S hS (Functor.reprX F) i) ≫ (Functor.reprW F).hom,
      isAffine_affineChart B S hS (Functor.reprX F) i, ?_, ⟨_, hq⟩⟩
    refine MorphismProperty.RespectsIso.postcomp _ (Functor.reprW F).hom _ ?_
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
      (isOpenImmersion_toScheme_map_affineChartι B S hS (Functor.reprX F) i)
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hαopen
  have hVopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) α)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen
  have himage :
      IsOpen (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) := by
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
    exact hclosedmap _ hVopen.isClosed_compl
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) with hWdef
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG _ himage
  have hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hyW : y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWpts]
    exact ⟨x, ⟨v, hv⟩, hx⟩
  have hQalg : IsAlgebraicSpace B S hS (pullback f W.ι) :=
    isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG
  have hsq := IsPullback.of_hasPullback f W.ι
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hW.2
  have _ : Mono (pullback.fst f W.ι) := mono_of_presheaf_isOpenImmersion hfstopen
  have hfstpts : Set.range (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) =
      Set.range (pointsMap B S hS (yoneda.obj V) α) := by
    refine subset_antisymm ?_ ?_
    · rintro z ⟨w, rfl⟩
      have hmem : pointsMap B S hS F f (pointsMap B S hS (pullback f W.ι)
          (pullback.fst f W.ι) w) ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
        rw [pointsMap_apply_comm B S hS pullback.condition w]
        exact ⟨_, rfl⟩
      rw [hWpts] at hmem
      obtain ⟨z', hz', hfz'⟩ := hmem
      exact hbij.1 hfz' ▸ hz'
    · rintro z ⟨w, rfl⟩
      have hmem : pointsMap B S hS F f (pointsMap B S hS (yoneda.obj V) α w) ∈
          Set.range (pointsMap B S hS W.toFunctor W.ι) := by
        rw [hWpts]
        exact ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨b, hb⟩ := hmem
      obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS hsq _ b hb.symm
      exact ⟨c, hc⟩
  have hrange : Subfunctor.range (pullback.fst f W.ι) = Subfunctor.range α := by
    have hP := range_pointsMap_ι_range B S hS (pullback.fst f W.ι)
    have hA := range_pointsMap_ι_range B S hS α
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hαopen) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hQalg _ hfstopen) ?_)
    all_goals rw [hP, hA, hfstpts]
  have hQaff : IsAffineSpace B S hS (pullback f W.ι) := by
    refine ⟨V, hVaff, ⟨?_⟩⟩
    refine rangeIsoOfMono B S hS (pullback.fst f W.ι) ≪≫ ?_
    rw [hrange]
    exact (rangeIsoOfMono B S hS α).symm
  have hsndci : IsClosedImmersion B S hS (pullback.snd f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hf
  have hsndsurj : IsSurjective B S hS (pullback.snd f W.ι) := by
    intro b
    obtain ⟨z, -, hfz⟩ : pointsMap B S hS W.toFunctor W.ι b ∈
        pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) := by
      rw [← hWpts]
      exact ⟨b, rfl⟩
    obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS hsq z b hfz
    exact ⟨c, hc⟩
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS (pullback.snd f W.ι) hQalg hW.1
      hsndci hsndsurj hQaff
  obtain ⟨T, -, ⟨eT⟩⟩ := hWaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.IsAlgebraicSpace

open Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An algebraic space over `S` whose reduction is a scheme is a scheme. -/
@[stacks 049D]
theorem isRepresentable_of_isRepresentable_reduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hred : (reduction B S hS X hX).toFunctor.IsRepresentable) :
    X.IsRepresentable := by
  have hclosed : IsClosedSubspace B S hS (reduction B S hS X hX) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ
  exact isRepresentable_of_isClosedImmersion_of_bijective B S hS hclosed.1 hX
    (reduction B S hS X hX).ι hclosed.2
    ⟨pointsMap_injective_of_mono B S hS _, surjective_pointsMap_ι_reduction B S hS X hX⟩ hred

end AlgebraicGeometry.IsAlgebraicSpace

end
