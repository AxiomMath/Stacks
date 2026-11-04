module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageDescentChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance
import all StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
import all StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
import all StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance

/-!
# Stacks 07VT, 07VV and 07VW with Stacks 07SQ applied in its bounded form

`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed` (Stacks 07VT),
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` (Stacks 07VV) and
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence` (Stacks 07VW) take the conclusion of
Stacks 07SQ — a directed system of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms and affine limit has an affine stage — as the hypothesis `h07SQ`, in its
unbounded form. Over a size-bounded site that form is refuted
(`Stacks.Refute07SQ.not_statement07SQ`): the statement of Stacks 07SQ there asks that the charts
of the system be bounded, `AlgebraicGeometry.Space.ChartsBounded`, which is what keeps the
limits of the affine charts inside the site. This development proves that bounded form,
`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded`.

This file restates the three results with Stacks 07SQ applied through
`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded` rather than carried, the
presentation of Stacks 09YA being asked for in the matching form: `h09YA` yields an
`AlgebraicGeometry.Space.IntegralFiniteSystem` whose diagram has bounded charts. The remaining
named input `hFinitePresentation` is the case of Stacks 07VT in which the morphism is finite and
of finite presentation. None of the statements here is registered: `h09YA` and
`hFinitePresentation` are still carried.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_chartsBounded`
* `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective_of_chartsBounded`
* `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_chartsBounded`

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Affine

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Affineness of the target of a surjection presented as a directed limit of finite morphisms
of finite presentation whose charts are bounded.

The transition morphisms of the system are finite by Stacks 081Z and hence affine; the stages
are quasi-compact by Stacks 06G5 and quasi-separated by Stacks 03DY. The system is therefore a
`AlgebraicGeometry.Space.DescentSituation` with affine limit whose charts are bounded by `hp`,
so Stacks 07SQ produces an affine stage, which is surjective onto the target because the given
morphism factors through it, and `hFinitePresentation` applies to it. -/
private theorem isAffineSpace_of_integralFiniteSystem_of_chartsBounded (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (haff : IsAffineSpace B S hS X)
    (p : IntegralFiniteSystem B S hS f)
    (hp : letI := p.indexPreorder; ChartsBounded B S hS p.diagram)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let : Preorder p.indexType := p.indexPreorder
  let : Nonempty p.indexType := p.indexNonempty
  let : IsDirected p.indexType (· ≤ ·) := p.indexDirected
  have htransition : ∀ {i j : p.indexTypeᵒᵖ} (g : i ⟶ j),
      IsAffineHom B S hS (p.diagram.map g) := by
    intro i j g
    have hsep : IsSeparated B S hS (p.structureMap.app j) :=
      isSeparated_of_isFinite B S hS (p.structureMap.app j) (p.stageAlgebraicSpace j) hY
        (p.stageFinite j)
    have hfin : IsFinite B S hS (p.diagram.map g ≫ p.structureMap.app j) := by
      rw [p.structureMap.naturality g]
      simpa using p.stageFinite i
    exact IsFinite.isAffineHom
      (isFinite_of_comp_of_isSeparated B S hS (p.diagram.map g) (p.structureMap.app j) hfin hsep)
  let D : DescentSituation B S hS hZ p.indexType :=
    { system := p.diagram
      algebraicSpace := fun i ↦ p.stageAlgebraicSpace (Opposite.op i)
      transition_affine := htransition
      quasiCompact := fun i ↦
        isQuasiCompactSpace_of_isFinitePresentation B S hS
          (p.structureMap.app (Opposite.op i)) hY hYqc
          (p.stageFinitePresentation (Opposite.op i))
      quasiSeparated := fun i ↦
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
          (p.stageAlgebraicSpace (Opposite.op i)) hYqs
          (p.stageFinitePresentation (Opposite.op i)).2.2
      limitCone := Cone.mk X p.limitCone
      isLimit := p.isLimit
      limitAlgebraicSpace := hX
      base := Classical.choice p.indexNonempty }
  obtain ⟨i, -, hstageAffine⟩ := hasAffineStageDescent_of_chartsBounded B S hS hZ D hp haff
  have hstageSurj : IsSurjective B S hS (p.structureMap.app (Opposite.op i)) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨pointsMap B S hS X (p.limitCone.app (Opposite.op i)) x, ?_⟩
    rwa [← Function.comp_apply (f := pointsMap B S hS _ (p.structureMap.app (Opposite.op i))),
      ← pointsMap_comp, ← p.compatible (Opposite.op i)]
  exact hFinitePresentation (p.structureMap.app (Opposite.op i))
    (p.stageAlgebraicSpace (Opposite.op i)) hY (p.stageFinite (Opposite.op i))
    (p.stageFinitePresentation (Opposite.op i)) hstageSurj hstageAffine

/-- **Stacks 07VT, with Stacks 07SQ applied in its bounded form.** Let `f : X ⟶ Y` be a
surjective universally closed morphism of algebraic spaces over `S`. If `X` is affine, then so
is `Y`, given `h09YA` (Stacks 09YA, read as the existence of a presentation with bounded
charts) and `hFinitePresentation` (the case of a finite morphism of finite presentation).

The proof is that of `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`
with `AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded` in place of its hypothesis
`h07SQ`. -/
theorem isAffineSpace_of_isSurjective_of_universallyClosed_of_chartsBounded (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (hclosed : UniversallyClosed B S hS f)
    (haff : IsAffineSpace B S hS X)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ p : IntegralFiniteSystem B S hS g,
        letI := p.indexPreorder; ChartsBounded B S hS p.diagram)
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  obtain ⟨hYqc, hYsep, hYqs⟩ := target_isQuasiCompact_and_isAbsolutelyQuasiSeparated B S hS f hX
    hY hsurj hclosed haff
  -- Stacks 08GB, part (4): a morphism from an affine space to a separated space is affine.
  have haffHom : IsAffineHom B S hS f := by
    obtain ⟨T, hT, ⟨e⟩⟩ := haff
    have h : IsAffineHom B S hS (e.inv ≫ f) :=
      isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨T, hT⟩ (e.inv ≫ f) hYsep
    have h' : IsAffineHom B S hS (e.hom ≫ e.inv ≫ f) := isAffineHom_iso_comp e.hom h
    rwa [← Category.assoc, e.hom_inv_id, Category.id_comp] at h'
  -- Stacks 0415: an affine universally closed morphism is integral.
  have hint : IsIntegralHom B S hS f :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX hY f).2 ⟨haffHom, hclosed⟩
  obtain ⟨p, hp⟩ := h09YA f hX hY hint hYqc hYqs
  exact isAffineSpace_of_integralFiniteSystem_of_chartsBounded B S hS f hX hY hsurj haff p hp
    hYqc hYqs hFinitePresentation

end Affine

section Representable

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 07VV, the implication from the source, with Stacks 07SQ applied in its bounded
form.** If the source of an integral morphism of algebraic spaces over `S` which is bijective on
points is a scheme, then so is its target, given `h09YA` and `hFinitePresentation`.

The proof is that of `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`,
with `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_chartsBounded`
as its appeal to Stacks 07VT. -/
theorem isRepresentable_of_isIntegralHom_of_bijective_of_chartsBounded
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsIntegralHom B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ p : IntegralFiniteSystem B S hS g,
        letI := p.indexPreorder; ChartsBounded B S hS p.diagram)
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    G.IsRepresentable := by
  classical
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1 hf).2
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ := exists_affineChart_isOpenImmersion_mem_range B S hS
    (Functor.reprX F) (Functor.reprW F) x
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hαopen
  -- The open subspace of the target cut out by the image of the point set of `V`.
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α))
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG _ (isOpen_image_of_bijective_of_isClosedMap
      hbij hclosedmap (isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen))
  have hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hyW : y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWpts]; exact ⟨x, ⟨v, hv⟩, hx⟩
  -- The base change of the morphism along that open subspace.
  have hQalg : IsAlgebraicSpace B S hS (pullback f W.ι) :=
    isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  have _ : Mono (pullback.fst f W.ι) := mono_of_presheaf_isOpenImmersion hfstopen
  have hlift := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback f W.ι)
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
      obtain ⟨c, hc, -⟩ := hlift _ b hb.symm
      exact ⟨c, hc⟩
  have hrange : Subfunctor.range (pullback.fst f W.ι) = Subfunctor.range α := by
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hαopen) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hQalg _ hfstopen) ?_) <;>
      rw [range_pointsMap_ι_range B S hS (pullback.fst f W.ι), range_pointsMap_ι_range B S hS α,
        hfstpts]
  have hQaff : IsAffineSpace B S hS (pullback f W.ι) := by
    refine ⟨V, hVaff, ⟨rangeIsoOfMono B S hS (pullback.fst f W.ι) ≪≫ ?_⟩⟩
    rw [hrange]; exact (rangeIsoOfMono B S hS α).symm
  -- The projection to the open subspace is integral and surjective, so the subspace is affine.
  have hsndsurj : IsSurjective B S hS (pullback.snd f W.ι) := by
    intro b
    obtain ⟨z, hfz⟩ := hbij.2 (pointsMap B S hS W.toFunctor W.ι b)
    obtain ⟨c, -, hc⟩ := hlift z b hfz
    exact ⟨c, hc⟩
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    isAffineSpace_of_isSurjective_of_universallyClosed_of_chartsBounded B S hS
      (pullback.snd f W.ι) hQalg hW.1
      hsndsurj ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hQalg hW.1
        (pullback.snd f W.ι)).1 (isIntegralHom_pullback_snd B S hS f W.ι hf)).2
      hQaff h09YA hFinitePresentation
  obtain ⟨T, -, ⟨eT⟩⟩ := hWaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

end Representable

section SmallEtale

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 07VW, the equivalence on the étale schemes, with Stacks 07SQ applied in its bounded
form.** Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of
algebraic spaces over `S`. Then base change `V ↦ X ×_Y V` is an equivalence from the small étale
site of `Y` to that of `X`, given `hEquiv` (the conclusion of Stacks 05ZH on the spaces-étale
sites), `h09YA` and `hFinitePresentation`.

The proof is that of `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence`, with
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective_of_chartsBounded` as its
appeal to Stacks 07VV. -/
theorem smallEtalePullback_isEquivalence_of_chartsBounded (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom)
    (hinj : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (hEquiv : (spacesBaseChange B S hS f).functor.IsEquivalence)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ p : IntegralFiniteSystem B S hS g,
        letI := p.indexPreorder; ChartsBounded B S hS p.diagram)
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    (smallEtalePullback B S hS f hf).IsEquivalence := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_full B S hS Y
  have := comparisonFunctor_faithful B S hS Y
  refine isEquivalence_of_restriction (comparisonFunctor B S hS Y)
    (comparisonFunctor B S hS X) _ ((spacesBaseChange B S hS f).functor)
    (smallEtalePullbackComparisonIso B S hS f hf) fun V hV ↦ ?_
  exact (essImage_comparisonFunctor_iff B S hS Y V).2 <|
    isRepresentable_of_isIntegralHom_of_bijective_of_chartsBounded B S hS
      ((spacesBaseChange B S hS f).functor.obj V).1.left.2 V.1.left.2
      ((spacesBaseChange B S hS f).projection.app V).hom
      (isIntegralHom_spacesBaseChange_projection B S hS f hf V)
      (bijective_pointsMap_spacesBaseChange_projection B S hS f hinj hsurj V)
      ((essImage_comparisonFunctor_iff B S hS X _).1 hV) h09YA hFinitePresentation

end SmallEtale

end AlgebraicGeometry.Space

end
