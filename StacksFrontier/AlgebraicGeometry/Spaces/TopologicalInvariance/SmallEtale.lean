module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjectionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.TopologicalInvariance.SpacesEtaleEssSurj

/-!
# Topological invariance of the étale site, on schemes and on affines (Stacks 07VW)

Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over a scheme `S`. The equivalence `V ↦ X ×_Y V` of spaces-étale sites of Stacks 05ZH
restricts to equivalences `Y_étale ⟶ X_étale` and `Y_affine,étale ⟶ X_affine,étale`. This is
Stacks 07VW, with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_target_of_isIntegralHom_of_bijective`: the target of an
  integral morphism of algebraic spaces which is bijective on points is a scheme as soon as its
  source is.
* `AlgebraicGeometry.Space.isEquivalence_smallEtalePullback`: **Stacks 07VW on schemes.**
* `AlgebraicGeometry.Space.isEquivalence_affineEtalePullback`: **Stacks 07VW on affines.**

## Implementation notes

The functors are the base's `AlgebraicGeometry.Space.smallEtalePullback` and
`AlgebraicGeometry.Space.affineEtalePullback`, which are the restrictions of base change on the
spaces-étale sites by `AlgebraicGeometry.Space.smallEtalePullbackComparisonIso` and
`AlgebraicGeometry.Space.affineEtalePullbackInclusionIso`. That they are equivalences is the
source's argument: for `V` étale over `Y` the projection `X ×_Y V ⟶ V` is integral, universally
injective and surjective, so `V` is a scheme exactly when `X ×_Y V` is (Stacks 07VV), and `V` is
affine exactly when `X ×_Y V` is (Stacks 07VT); the equivalence of Stacks 05ZH,
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isIntegralHom`, then restricts along
the fully faithful comparison functors by `AlgebraicGeometry.Space.isEquivalence_of_restriction`.

The two implications "from the source" of Stacks 07VV and 07VT are the only nontrivial inputs.
Affineness of the target of a surjective universally closed morphism with affine source is
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`,
stated here without a Stacks attribute (it is part of Stacks 07VT). The implication of
Stacks 07VV from the source is proved here, unregistered, by the source's argument from it.

## References

* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The implication of Stacks 07VV from the source -/

section SchemeOfSource

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An algebraic space which is a scheme has an affine open through each of its points. -/
private theorem exists_isAffine_isOpenImmersion_mem_range_pointsMap [F.IsRepresentable]
    (x : points B S hS F) :
    ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ F),
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

/-- For `f` injective on points and `W` a subfunctor of `G` with points `|f|(A)`, the first
projection `F ×_G W ⟶ F` has image `A` on points. -/
private theorem range_pointsMap_pullback_fst_eq (f : F ⟶ G)
    (hf : Function.Injective (pointsMap B S hS F f)) (W : Subfunctor G)
    {A : Set (points B S hS F)}
    (hW : Set.range (pointsMap B S hS W.toFunctor W.ι) = pointsMap B S hS F f '' A) :
    Set.range (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) = A := by
  refine subset_antisymm ?_ fun z hz ↦ ?_
  · rintro z ⟨w, rfl⟩
    obtain ⟨z', hz', hfz'⟩ : pointsMap B S hS F f (pointsMap B S hS (pullback f W.ι)
        (pullback.fst f W.ι) w) ∈ pointsMap B S hS F f '' A := by
      rw [← hW, pointsMap_apply_comm B S hS pullback.condition w]
      exact ⟨_, rfl⟩
    exact hf hfz' ▸ hz'
  · obtain ⟨b, hb⟩ : pointsMap B S hS F f z ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
      rw [hW]
      exact ⟨z, hz, rfl⟩
    obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f W.ι) _ b hb.symm
    exact ⟨c, hc⟩

/-- The second projection `F ×_G W ⟶ W` is surjective when the points of `W` lie in the image
of `f`. -/
private theorem isSurjective_pullback_snd_of_range_subset (f : F ⟶ G) (W : Subfunctor G)
    (hW : Set.range (pointsMap B S hS W.toFunctor W.ι) ⊆ Set.range (pointsMap B S hS F f)) :
    IsSurjective B S hS (pullback.snd f W.ι) := by
  intro b
  obtain ⟨z, hz⟩ := hW ⟨b, rfl⟩
  obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback f W.ι) z b hz
  exact ⟨c, hc⟩

/-- An algebraic space with an open immersion into `F` is affine when its image on points is that
of an open immersion from an affine scheme. -/
private theorem isAffineSpace_of_range_pointsMap_eq {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (α : yoneda.obj V ⟶ F)
    (hα : IsOpenImmersion B S hS α) (β : P ⟶ F) (hβ : IsOpenImmersion B S hS β)
    (h : Set.range (pointsMap B S hS P β) = Set.range (pointsMap B S hS (yoneda.obj V) α)) :
    IsAffineSpace B S hS P := by
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hα
  have _ : Mono β := mono_of_presheaf_isOpenImmersion hβ
  have hrange : Subfunctor.range β = Subfunctor.range α := by
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hα) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hP _ hβ) ?_) <;>
      rw [range_pointsMap_ι_range B S hS β, range_pointsMap_ι_range B S hS α, h]
  refine ⟨V, hV, ⟨rangeIsoOfMono B S hS β ≪≫ ?_⟩⟩
  rw [hrange]
  exact (rangeIsoOfMono B S hS α).symm

/-- **The target of an integral morphism bijective on points is a scheme when its source is.**
Let `f : F ⟶ G` be an integral morphism of algebraic spaces over `S` inducing a bijection on
points, with `F` a scheme. Then `G` is a scheme.

This is the implication of Stacks 07VV from the source, by the source's argument. Through an
affine open `V` of `F` the open subspace `W` of `G` with points `|f|(|V|)` is formed, which is
open because `f` is universally closed and bijective on points; bijectivity identifies the base
change `F ×_G W` with `V`, so it is affine, and its projection to `W` is integral and surjective,
so `W` is affine by Stacks 07VT. Every point of `G` thus lies in the schematic locus. -/
theorem isRepresentable_target_of_isIntegralHom_of_bijective (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsIntegralHom B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable) :
    G.IsRepresentable := by
  classical
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1 hf).2
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  -- An affine open of the source through the point.
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ :=
    exists_isAffine_isOpenImmersion_mem_range_pointsMap B S hS x
  -- The open subspace of the target cut out by the image of the point set of `V`.
  have himage :
      IsOpen (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) := by
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
    exact hclosedmap _ (isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen).isClosed_compl
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α))
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
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  -- The projection to the open subspace is integral and surjective, so the subspace is affine.
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace B S hS
      (pullback.snd f W.ι) hQalg hW.1
      (isSurjective_pullback_snd_of_range_subset B S hS f W
        (hWpts.trans_subset (Set.image_subset_range _ _)))
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hQalg hW.1
        (pullback.snd f W.ι)).1 (isIntegralHom_pullback_snd B S hS f W.ι hf)).2
      (isAffineSpace_of_range_pointsMap_eq B S hS hQalg hVaff α hαopen _ hfstopen
        (range_pointsMap_pullback_fst_eq B S hS f hbij.1 W hWpts))
  obtain ⟨T, -, ⟨eT⟩⟩ := hWaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

end SchemeOfSource

/-! ### The two equivalences -/

section Equivalences

variable {X Y : AlgebraicSpaces B S hS}

/-- The projection `X ×_Y V ⟶ V` of the base change of `f` is integral when `f` is (Stacks 03ZS). -/
private theorem isIntegralHom_projection_app (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (V : SpacesEtale B S hS Y) :
    IsIntegralHom B S hS ((spacesBaseChange B S hS f).projection.app V).hom :=
  isIntegralHom_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS ((spacesBaseChange B S hS f).isPullback V)).flip hf

/-- **Stacks 07VW, on the étale schemes.** Let `f : X ⟶ Y` be an integral, universally injective
and surjective morphism of algebraic spaces over `S`. Then base change `V ↦ X ×_Y V` is an
equivalence from the small étale site of `Y` to that of `X`; it is the restriction of the
equivalence of Stacks 05ZH on the spaces-étale sites
(`AlgebraicGeometry.Space.smallEtalePullbackComparisonIso`).

The equivalence of Stacks 05ZH restricts along the fully faithful comparison functors of Stacks
03G1 because, for `V` étale over `Y`, `V` is a scheme exactly when `X ×_Y V` is: the projection
`X ×_Y V ⟶ V` is integral and bijective on points, so Stacks 07VV applies in both directions. -/
@[stacks 07VW "the equivalence `Y_étale ⟶ X_étale` of small étale sites, the restriction of the \
equivalence of Stacks 05ZH on spaces-étale sites (that it is the restriction is \
`AlgebraicGeometry.Space.smallEtalePullbackComparisonIso`)"]
theorem isEquivalence_smallEtalePullback (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (hinj : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom) :
    (smallEtalePullback B S hS f hf).IsEquivalence := by
  -- The projection `X ×_Y V ⟶ V` is a base change of `f`: integral (Stacks 03ZS), and bijective
  -- on points (Stacks 03MW, Stacks 03MH).
  have hint := isIntegralHom_projection_app B S hS f hf
  have hbij : ∀ V : SpacesEtale B S hS Y, Function.Bijective (pointsMap B S hS
      ((spacesBaseChange B S hS f).functor.obj V).1.left.1
      ((spacesBaseChange B S hS f).projection.app V).hom) := fun V ↦
    ⟨injective_pointsMap_of_universallyInjective B S hS V.1.left.2
        (universallyInjective_of_isPullback B S hS X.2 V.1.left.2 Y.2 f.hom V.1.hom.hom hinj
          (AlgebraicSpaces.isPullback_hom B S hS ((spacesBaseChange B S hS f).isPullback V))),
      isSurjective_of_isPullback B S hS ((spacesBaseChange B S hS f).isPullback V).flip hsurj⟩
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_full B S hS Y
  have := comparisonFunctor_faithful B S hS Y
  have := isEquivalence_spacesBaseChange_of_isIntegralHom B S hS f hf hinj hsurj
  exact isEquivalence_of_restriction (comparisonFunctor B S hS Y)
    (comparisonFunctor B S hS X) _ ((spacesBaseChange B S hS f).functor)
    (smallEtalePullbackComparisonIso B S hS f hf) fun V hV ↦
      (essImage_comparisonFunctor_iff B S hS Y V).2 <|
        isRepresentable_target_of_isIntegralHom_of_bijective B S hS
          ((spacesBaseChange B S hS f).functor.obj V).1.left.2 V.1.left.2
          ((spacesBaseChange B S hS f).projection.app V).hom (hint V) (hbij V)
          ((essImage_comparisonFunctor_iff B S hS X _).1 hV)

/-- **Stacks 07VW, on the affine étale schemes.** Let `f : X ⟶ Y` be an integral, universally
injective and surjective morphism of algebraic spaces over `S`. Then base change `V ↦ X ×_Y V` is
an equivalence from the affine étale site of `Y` to that of `X`; it is the restriction of the
equivalence on the small étale sites (`AlgebraicGeometry.Space.affineEtalePullbackInclusionIso`).

For `V` étale over `Y` and a scheme, `V` is affine exactly when `X ×_Y V` is: the projection is
integral, so an affine `V` has affine base change, and it is surjective and universally closed,
so an affine base change forces `V` affine by Stacks 07VT. -/
@[stacks 07VW "the equivalence `Y_affine,étale ⟶ X_affine,étale` of affine étale sites, the \
restriction of the equivalence on the small étale sites (that it is the restriction is \
`AlgebraicGeometry.Space.affineEtalePullbackInclusionIso`)"]
theorem isEquivalence_affineEtalePullback (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (hinj : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom) :
    (affineEtalePullback B S hS f hf).IsEquivalence := by
  have := isEquivalence_smallEtalePullback B S hS f hf hinj hsurj
  refine isEquivalence_of_restriction (AffineEtale.inclusion B S hS Y.1)
    (AffineEtale.inclusion B S hS X.1) _ (smallEtalePullback B S hS f hf)
    (affineEtalePullbackInclusionIso B S hS f hf) fun U hU ↦ ?_
  refine (essImage_affineEtaleInclusion_iff B S hS Y.1 U).2 ?_
  refine (isAffineSpace_comparisonFunctor_iff B S hS Y U).1 ?_
  -- The base change is affine, read on the spaces-étale site.
  have hW : IsAffineSpace B S hS ((spacesBaseChange B S hS f).functor.obj
      ((comparisonFunctor B S hS Y).obj U)).1.left.1 := by
    obtain ⟨T, hT, ⟨e⟩⟩ := (isAffineSpace_comparisonFunctor_iff B S hS X _).2
      ((essImage_affineEtaleInclusion_iff B S hS X.1 _).1 hU)
    exact ⟨T, hT, ⟨((SpacesEtale.toSpaces B S hS X ⋙
      ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).mapIso
        ((smallEtalePullbackComparisonIso B S hS f hf).app U)).symm ≪≫ e⟩⟩
  have hP := ((spacesBaseChange B S hS f).functor.obj
    ((comparisonFunctor B S hS Y).obj U)).1.left.2
  have hV := ((comparisonFunctor B S hS Y).obj U).1.left.2
  exact isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace B S hS
    ((spacesBaseChange B S hS f).projection.app _).hom hP hV
    (isSurjective_of_isPullback B S hS ((spacesBaseChange B S hS f).isPullback _).flip hsurj)
    ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hP hV _).1
      (isIntegralHom_projection_app B S hS f hf _)).2 hW

end Equivalences

end AlgebraicGeometry.Space

end
