module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# Stacks 05ZR reduced to its affine case

Let `S` be a scheme and `X ⊂ X'` a thickening of algebraic spaces over `S`. **Stacks 05ZR** says
that if `X` is a scheme then so is `X'`. Its content beyond topology is the *affine case*: an
algebraic space `W` admitting a surjective closed immersion `P ⟶ W` from an affine scheme `P` is
affine. That is the closed-immersion case of **Stacks 07VS**, and it is what the source's own
finite-order proof of 05ZR reduces to (its first paragraph) before treating it.

This file proves the reduction: every point of `X'` has an open neighbourhood
which is the target of a surjective closed immersion from an affine open of `X`, so the affine
case makes that neighbourhood affine, and `X'` is its own schematic locus (**Stacks 03JH**). The
affine case enters as the explicit hypothesis `hAffineCase`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective_of_affineCase`: the
  target of a closed immersion of algebraic spaces which is bijective on points and has
  representable source is representable, given the affine case.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_affineCase`: Stacks 05ZR in the
  morphism form `AlgebraicGeometry.Space.IsThickeningHom`, given the affine case.

## Implementation notes

The library's other form of Stacks 05ZR,
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom`, runs through Stacks 07VV and so
through Stacks 07VT, with that proposition's hypotheses `h09YA`, `h07SQ` and `hFinitePresentation`.
The affine case used here is weaker: it is about a closed immersion rather than an arbitrary
integral morphism, and it is a statement about algebraic spaces (Stacks 07VS). The proof below is
the proof of `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` with Stacks
07VT replaced by the affine case at the one place it is used; the base change of a closed immersion
along the inclusion of an open subspace is a closed immersion.

The affine case is also the absolute form of the cartesian statement "a space over an affine
scheme `Z` whose base change to a thickening `Z₀ ⊂ Z` is affine is itself affine": that base
change is a surjective closed immersion into the space.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_schemeOfAffineCase :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_schemeOfAffineCase
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The target of a closed immersion bijective on points out of a scheme is a scheme, given the
affine case.** Let `f : F ⟶ G` be a closed immersion of algebraic spaces over `S` which is
bijective on points, with `F` representable. If every algebraic space receiving a surjective
closed immersion from an affine algebraic space is affine (`hAffineCase`, the closed-immersion
case of **Stacks 07VS**), then `G` is representable.

Every point of `G` is the image of a point of an affine open `V` of `F`; the image of `|V|` is open
since `|f|` is a closed bijection, and the open subspace `W` of `G` it cuts out receives the base
change of `f`, a surjective closed immersion with source `V`. So `W` is affine and the point lies
in the schematic locus of **Stacks 03JH**. -/
theorem isRepresentable_of_isClosedImmersion_of_bijective_of_affineCase
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsClosedImmersion B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable)
    (hAffineCase : ∀ {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : P ⟶ W),
      IsAlgebraicSpace B S hS P → IsAlgebraicSpace B S hS W → IsClosedImmersion B S hS j →
      IsSurjective B S hS j → IsAffineSpace B S hS P → IsAffineSpace B S hS W) :
    G.IsRepresentable := by
  classical
  let _ : F.IsRepresentable := hFrep
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1
        (isIntegralHom_of_isClosedImmersion B S hS f hf)).2
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
  -- The open subspace of the target cut out by the image of the point set of `V`.
  have hVopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) α)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen
  have himage : IsOpen (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) :=
    by
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
  -- The base change of the morphism along that open subspace.
  have hQalg : IsAlgebraicSpace B S hS (pullback f W.ι) :=
    isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG
  have hpb := IsPullback.of_hasPullback f W.ι
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip hW.2
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
      obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS hpb _ b hb.symm
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
  -- The projection to the open subspace is a closed immersion and surjective, so the subspace
  -- is affine by the affine case.
  have hsndci : IsClosedImmersion B S hS (pullback.snd f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hf
  have hsndsurj : IsSurjective B S hS (pullback.snd f W.ι) := by
    intro b
    have hmem : pointsMap B S hS W.toFunctor W.ι b ∈
        Set.range (pointsMap B S hS W.toFunctor W.ι) := ⟨b, rfl⟩
    rw [hWpts] at hmem
    obtain ⟨z, -, hfz⟩ := hmem
    obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS hpb z b hfz
    exact ⟨c, hc⟩
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    hAffineCase (pullback.snd f W.ι) hQalg hW.1 hsndci hsndsurj hQaff
  obtain ⟨T, -, ⟨eT⟩⟩ := hWaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

/-- **Stacks 05ZR, morphism form, given the affine case.** Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`. If `X` is (representable by) a scheme, then so is `X'`, provided every
algebraic space receiving a surjective closed immersion from an affine algebraic space is affine
(`hAffineCase`, the closed-immersion case of **Stacks 07VS**). -/
theorem isRepresentable_of_isThickeningHom_of_affineCase {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (hi : IsThickeningHom B S hS i) (hXrep : X.1.IsRepresentable)
    (hAffineCase : ∀ {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : P ⟶ W),
      IsAlgebraicSpace B S hS P → IsAlgebraicSpace B S hS W → IsClosedImmersion B S hS j →
      IsSurjective B S hS j → IsAffineSpace B S hS P → IsAffineSpace B S hS W) :
    X'.1.IsRepresentable := by
  have := hi.mono
  exact isRepresentable_of_isClosedImmersion_of_bijective_of_affineCase B S hS X.property
    X'.property i.hom hi.isClosedImmersion
    ⟨pointsMap_injective_of_mono B S hS i.hom, hi.surjective_pointsMap⟩ hXrep hAffineCase

end AlgebraicGeometry.Space

end
