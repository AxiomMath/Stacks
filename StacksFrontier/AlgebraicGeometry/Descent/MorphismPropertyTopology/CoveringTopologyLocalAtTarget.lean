module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.StandardForm.Descent
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings

/-!
# Properties of morphisms local on the target for the fppf, étale, smooth and syntomic topologies

A property `P` of morphisms of schemes is *local on the base for `τ`* when, for every
`τ`-covering `{Yᵢ → Y}` and every `f : X ⟶ Y`, the morphism `f` has `P` if and only if each base
change `Yᵢ ×_Y X ⟶ Yᵢ` has `P`. In Mathlib this is
`CategoryTheory.MorphismProperty.IsLocalAtTarget P (AlgebraicGeometry.Scheme.precoverage
(AlgebraicGeometry.coveringMorphismProperty τ))`.

This file proves the criterion of Tag 02KP for the fppf, étale, smooth and syntomic topologies:
a property which is preserved by base change along the morphisms belonging to `τ`, is Zariski
local on the base, and descends along the surjective morphisms of affine schemes belonging to
`τ`, is local on the base for `τ`.

## Main results

* `AlgebraicGeometry.isLocalAtTarget_precoverage_of_affineDescent`: the criterion, for the four
  topologies at once.

## Implementation notes

The three hypotheses of the source are, in order,
`CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst P (coveringMorphismProperty τ)`,
`AlgebraicGeometry.IsZariskiLocalAtTarget P`, and the hypothesis `hdesc` on a surjective
morphism of affine schemes belonging to `τ`. The source quantifies `τ` over fpqc, fppf, étale,
smooth and syntomic. The four topologies other than fpqc are exactly the topologies of
`AlgebraicGeometry.CoveringTopology` other than Zariski, which is why they are treated here in
one statement, with `τ` ranging over `AlgebraicGeometry.CoveringTopology` and the Zariski case
excluded by hypothesis. The fpqc case is not of this shape, an fpqc covering carrying a
quasi-compactness condition on the family instead of a condition on each member, and is
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`.

No new argument is needed. `AlgebraicGeometry.isLocalAtTarget_of_standardRefinement`, the
criterion behind the three cases of Tag 034G, is stated for an arbitrary morphism property `Q`
cutting out the topology and an arbitrary class `R` of morphisms of affine schemes along which
descent is assumed; Tag 034G is the observation that `R` may be taken to be the morphisms in
*standard* form, a smaller class than `Q`. Tag 02KP assumes descent along all of `Q`, so for the
étale, smooth and syntomic topologies it follows from Tag 034G: a standard étale, standard
smooth or standard syntomic morphism is in particular étale, smooth or syntomic. The fppf
topology has no entry in Tag 034G, so that case instantiates the shared criterion directly at
`R = Q`, its refinement hypothesis being supplied by
`AlgebraicGeometry.QuasiCompactCover.exists_hom`: a flat morphism locally of finite presentation
is an open map, so an fppf covering of an affine — hence quasi-compact — scheme is a
quasi-compact covering and admits a finite refinement by affine schemes through open immersions.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 034G](https://stacks.math.columbia.edu/tag/034G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism belonging to the fppf topology is an open map. -/
private theorem isOpenMap_of_coveringMorphismProperty_fppf {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : coveringMorphismProperty CoveringTopology.fppf f) : IsOpenMap f.base := by
  have _ : Flat f := hf.1
  have _ : LocallyOfFinitePresentation f := hf.2
  exact f.isOpenMap

/-- An fppf covering of an affine scheme is refined, through open immersions, by an fppf covering
of it by affine schemes. -/
private theorem exists_affine_refinement_fppf {T : Scheme.{u}} [IsAffine T]
    (W : T.Cover.{u} (Scheme.precoverage (coveringMorphismProperty CoveringTopology.fppf))) :
    ∃ (V : T.Cover.{u} (Scheme.precoverage (coveringMorphismProperty CoveringTopology.fppf)))
      (r : V.toPreZeroHypercover.Hom W.toPreZeroHypercover),
      (∀ j, IsAffine (V.X j)) ∧
        (∀ j, coveringMorphismProperty CoveringTopology.fppf (V.f j)) ∧
          ∀ j, IsOpenImmersion (r.h₀ j) := by
  have _ : MorphismProperty.RespectsLeft
      (coveringMorphismProperty CoveringTopology.fppf : MorphismProperty Scheme.{u})
      @IsOpenImmersion :=
    ⟨fun i _ f hf ↦ ⟨MorphismProperty.comp_mem @Flat i f inferInstance hf.1,
      MorphismProperty.comp_mem @LocallyOfFinitePresentation i f inferInstance hf.2⟩⟩
  have _ : CompactSpace T := inferInstance
  have _ : QuasiCompactCover W.toPreZeroHypercover :=
    .of_isOpenMap fun i ↦ isOpenMap_of_coveringMorphismProperty_fppf (W.map_prop i)
  obtain ⟨V, r, -, hoi⟩ := QuasiCompactCover.exists_hom W
  exact ⟨V.cover, r, fun j ↦ inferInstanceAs (IsAffine (Spec _)),
    fun j ↦ V.cover.map_prop j, hoi⟩

/-- **Stacks Project, Tag 02KP** for the fppf, étale, smooth and syntomic topologies. Let `P` be
a property of morphisms of schemes and let `τ` be one of fppf, étale, smooth and syntomic.
Assume that

1. `P` is preserved by base change along the morphisms belonging to `τ`, that is along flat
   morphisms locally of finite presentation, syntomic, smooth or étale morphisms depending on
   whether `τ` is fppf, syntomic, smooth or étale;
2. `P` is Zariski local on the base;
3. for every surjective morphism `g : S' ⟶ S` of affine schemes belonging to `τ` and every
   morphism of schemes `f : X ⟶ S`, the property `P` holds for `f` if it holds for the base
   change `S' ×_S X ⟶ S'`.

Then `P` is `τ` local on the base. -/
@[stacks 02KP "the fppf, étale, smooth and syntomic cases"]
theorem isLocalAtTarget_precoverage_of_affineDescent (P : MorphismProperty Scheme.{u})
    (τ : CoveringTopology) (hτ : τ ≠ .zariski)
    [P.IsStableUnderBaseChangeAgainst (coveringMorphismProperty τ)]
    [IsZariskiLocalAtTarget P]
    (hdesc : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S'] (g : S' ⟶ S), Surjective g →
      coveringMorphismProperty τ g → ∀ f : X ⟶ S, P (pullback.snd f g) → P f) :
    P.IsLocalAtTarget (Scheme.precoverage (coveringMorphismProperty τ)) := by
  cases τ with
  | fppf =>
    have _ := Flat.isStableUnderBaseChange.{u}
    have _ := locallyOfFinitePresentation_isStableUnderBaseChange.{u}
    have _ : MorphismProperty.IsStableUnderBaseChange
        (coveringMorphismProperty CoveringTopology.fppf : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.inf
    refine isLocalAtTarget_of_standardRefinement P
      (Q := coveringMorphismProperty CoveringTopology.fppf)
      (R := coveringMorphismProperty CoveringTopology.fppf) ?_ ?_ ?_ ?_ ?_
    · exact fun g hsurj hg f hp ↦ hdesc g hsurj hg f hp
    · intro X Y g hg
      exact ⟨inferInstance, inferInstance⟩
    · intro U S W _ _ _ g w hg
      exact (coveringMorphismProperty CoveringTopology.fppf).pullback_fst w g hg
    · exact fun _ ↦ isOpenMap_of_coveringMorphismProperty_fppf
    · intro T _ W
      exact exists_affine_refinement_fppf W
  | syntomic =>
    have _ : P.IsStableUnderBaseChangeAgainst (@Syntomic : MorphismProperty Scheme.{u}) :=
      inferInstance
    exact isLocalAtTarget_syntomic_of_standard_descent P
      fun g hsurj hg f hp ↦ hdesc g hsurj (syntomic_of_standardSyntomic hg) f hp
  | smooth =>
    have _ : P.IsStableUnderBaseChangeAgainst (@Smooth : MorphismProperty Scheme.{u}) :=
      inferInstance
    refine isLocalAtTarget_smooth_of_standard_descent P ?_
    intro S S' X _ _ g hsurj hg f hp
    refine hdesc g hsurj ?_ f hp
    exact (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
      (RingHom.IsStandardSmooth.smooth hg)
  | etale =>
    have _ : P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u}) :=
      inferInstance
    refine isLocalAtTarget_etale_of_standard_descent P ?_
    intro S S' X _ _ g hsurj hg f hp
    refine hdesc g hsurj ?_ f hp
    let _ : Algebra Γ(S, ⊤) Γ(S', ⊤) := g.appTop.hom.toAlgebra
    let _ : Algebra.IsStandardEtale Γ(S, ⊤) Γ(S', ⊤) := hg
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale _ _))
  | zariski => exact absurd rfl hτ

end AlgebraicGeometry

end
