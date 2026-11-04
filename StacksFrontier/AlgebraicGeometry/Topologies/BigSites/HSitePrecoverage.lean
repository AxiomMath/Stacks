module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSitePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ProperRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.HToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ProperFinitePresentationRefinement

/-!
# The site axioms for the precoverage of a big h site, and its refinement by proper morphisms

The covering families of a big h site `B` are its chosen, size-bounded h coverings, and the
precoverage `AlgebraicGeometry.BigHSite.precoverage` consists of the presieves they present.
This file proves that this precoverage satisfies the site axioms in the form of Mathlib's
`CategoryTheory.Precoverage` classes, that it contains the étale precoverage of the associated
big étale site, and that it satisfies the refinement property (0EZ8) of the comparison situation
of Stacks 0EZ3 for the proper morphisms.

## Main results

* `AlgebraicGeometry.IsHCovering.of_hom` — being an h covering is inherited along refinements
  by families whose members are locally of finite presentation.
* `AlgebraicGeometry.BigHSite.mem_precoverage_iff_isHCovering` — a family of the site presents
  a covering presieve exactly when its image in all schemes is an h covering.
* The instances `BigHSite.precoverage_hasIsos`, `BigHSite.precoverage_isStableUnderBaseChange`
  and `BigHSite.precoverage_isStableUnderComposition`.
* `AlgebraicGeometry.BigHSite.etalePrecoverage_le_precoverage` — étale coverings are h
  coverings.
* `AlgebraicGeometry.BigHSite.exists_properRefinement` — **property 0EZ8** for the h topology.

## Implementation notes

The arguments are those of the ph site,
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSitePrecoverage`, with Stacks 0ETY in place
of Stacks 0DBI. The refinement uses Stacks 0ETU,
`AlgebraicGeometry.exists_finitePresentation_proper_refinement_of_isHCovering`: over an affine
open of the target an h covering is refined by the affine opens of a single proper surjection of
finite presentation, which is an h covering by Stacks 0ETW. The three stages are assembled from
this affine-local step by `AlgebraicGeometry.BigEtaleSite.exists_properRefinement_of_affine`.

## References

* [Stacks Project, Tag 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
* [Stacks Project, Tag 0ETW](https://stacks.math.columbia.edu/tag/0ETW)
* [Stacks Project, Tag 0ETY](https://stacks.math.columbia.edu/tag/0ETY)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- **Being an h covering is inherited along refinements.** If `E` is an h covering refining the
family `F`, and every member of `F` is locally of finite presentation, then `F` is an h
covering. -/
public theorem IsHCovering.of_hom {T : Scheme.{u}} {E : PreZeroHypercover.{v} T}
    {F : PreZeroHypercover.{w} T} (hE : IsHCovering E.X E.f) (φ : E.Hom F)
    (hF : ∀ i, LocallyOfFinitePresentation (F.f i)) : IsHCovering F.X F.f :=
  ⟨hF, hE.2.of_hom φ fun _ => inferInstance⟩

namespace BigHSite

variable (B : BigHSite.{u})

/-- **The covering presieves of a big h site are the presieves of its h coverings.** A family
`E` of the site presents a presieve of `B.precoverage` exactly when its image in all schemes is
an h covering. -/
public theorem mem_precoverage_iff_isHCovering {T : B.Schemes}
    (E : PreZeroHypercover.{u + 1} T) :
    E.presieve₀ ∈ B.precoverage T ↔
      IsHCovering (E.map B.inclusion).X (E.map B.inclusion).f := by
  constructor
  · rintro ⟨E', hR, hE'⟩
    have hE'h : IsHCovering (E'.map B.inclusion).X (E'.map B.inclusion).f := hE'.1
    refine hE'h.of_hom
      (PreZeroHypercover.Hom.map B.inclusion (PreZeroHypercover.homOfPresieveLE hR.symm.le))
      fun i => ?_
    let φ := PreZeroHypercover.homOfPresieveLE hR.le
    have hlfp : LocallyOfFinitePresentation (B.inclusion.map (E'.f (φ.s₀ i))) := hE'h.1 (φ.s₀ i)
    show LocallyOfFinitePresentation (B.inclusion.map (E.f i))
    have : IsIso (B.inclusion.map (φ.h₀ i)) := by
      dsimp [φ, PreZeroHypercover.homOfPresieveLE]
      infer_instance
    rw [← φ.w₀ i, Functor.map_comp]
    infer_instance
  · intro h
    obtain ⟨⟨Vbase, Vfam⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨T, E⟩ h
    change T = Vbase at hT
    subst hT
    exact ⟨Vfam, PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb, hV⟩

/-- **Stacks 0ETY (1), on a big h site.** The precoverage of a big h site contains the
isomorphisms. -/
public instance precoverage_hasIsos : B.precoverage.HasIsos := by
  constructor
  intro U V g hg
  refine ⟨PreZeroHypercover.singleton g, ?_, B.coverings_isSite.1 g⟩
  simp

/-- **Stacks 0ETY (3), on a big h site.** The precoverage of a big h site is stable under base
change. -/
public instance precoverage_isStableUnderBaseChange : B.precoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    let E : PreZeroHypercover.{u + 1} S := ⟨ι, X, f⟩
    let F : PreZeroHypercover.{u + 1} Y := ⟨ι, P, p₁⟩
    have hE : IsHCovering (E.map B.inclusion).X (E.map B.inclusion).f :=
      (B.mem_precoverage_iff_isHCovering E).1 hf
    refine (B.mem_precoverage_iff_isHCovering F).2 ?_
    have hpb := isHCovering_pullback hE (B.inclusion.map g)
    have hsq : ∀ i, IsPullback (B.inclusion.map (p₂ i)) (B.inclusion.map (p₁ i))
        (B.inclusion.map (f i)) (B.inclusion.map g) :=
      fun i => ((h i).map B.inclusion).flip
    let φ : PreZeroHypercover.Hom
        ⟨ι, fun i => pullback (B.inclusion.map (f i)) (B.inclusion.map g),
          fun i => pullback.snd (B.inclusion.map (f i)) (B.inclusion.map g)⟩
        (F.map B.inclusion) :=
      { s₀ := id
        h₀ := fun i => (hsq i).isoPullback.inv
        w₀ := fun i => (hsq i).isoPullback_inv_snd }
    refine hpb.of_hom φ fun i => ?_
    change LocallyOfFinitePresentation (B.inclusion.map (p₁ i))
    exact MorphismProperty.of_isPullback (hsq i) (hE.1 i)

/-- **Stacks 0ETY (2), on a big h site.** The precoverage of a big h site is stable under
composition. -/
public instance precoverage_isStableUnderComposition :
    B.precoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover.{u + 1} S := ⟨ι, X, f⟩
    let F : ∀ i, PreZeroHypercover.{u + 1} (X i) := fun i => ⟨σ i, Y i, g i⟩
    have hE : IsHCovering (E.map B.inclusion).X (E.map B.inclusion).f :=
      (B.mem_precoverage_iff_isHCovering E).1 hf
    have hF : ∀ i, IsHCovering ((F i).map B.inclusion).X ((F i).map B.inclusion).f :=
      fun i => (B.mem_precoverage_iff_isHCovering (F i)).1 (hg i)
    have hbind := isHCovering_bind (E.map B.inclusion) hE (fun i => (F i).map B.inclusion) hF
    change (E.bind F).presieve₀ ∈ B.precoverage S
    refine (B.mem_precoverage_iff_isHCovering (E.bind F)).2 (hbind.of_hom ?_ fun p => ?_)
    · exact
        { s₀ := id
          h₀ := fun _ => 𝟙 _
          w₀ := fun p => by
            change 𝟙 _ ≫ B.inclusion.map (g p.1 p.2 ≫ f p.1) =
              B.inclusion.map (g p.1 p.2) ≫ B.inclusion.map (f p.1)
            rw [Category.id_comp, Functor.map_comp] }
    · have h₁ : LocallyOfFinitePresentation (B.inclusion.map (f p.1)) := hE.1 p.1
      have h₂ : LocallyOfFinitePresentation (B.inclusion.map (g p.1 p.2)) := (hF p.1).1 p.2
      change LocallyOfFinitePresentation (B.inclusion.map (g p.1 p.2 ≫ f p.1))
      rw [Functor.map_comp]
      infer_instance

/-- Étale coverings of the underlying category of a big h site are h coverings: the precoverage
of the associated big étale site is contained in the precoverage of the h site. -/
public theorem etalePrecoverage_le_precoverage :
    (hAssociatedBigEtaleSite B).precoverage ≤ B.precoverage := by
  intro X R hR
  obtain ⟨E, hR, hE⟩ := hR
  exact ⟨E, hR, ((etaleBounded_eq_hEtaleBounded B ⟨X, E⟩).mpr hE).1⟩

/-- **Property 0EZ8 for the h topology.** Every h covering of an object `U` of a big h site is
refined in three stages: by an étale covering `{V ⟶ U}`, then by a single proper surjection
`W ⟶ V` of finite presentation over each member, which is an h covering, and finally by an
étale covering of `W`.

The étale covering consists of the affine opens of `U`. Over an affine open `V` the base change
of the given covering is an h covering (Stacks 0ETY (3)), and Stacks 0ETU refines it by the
finitely many affine opens of a proper surjection `W ⟶ V` of finite presentation, which is an h
covering by Stacks 0ETW. -/
public theorem exists_properRefinement (U : B.Schemes) (R : Presieve U)
    (hR : R ∈ B.precoverage U) :
    ∃ S : Presieve U, S ∈ (hAssociatedBigEtaleSite B).precoverage U ∧
      ∀ ⦃V : B.Schemes⦄ (v : V ⟶ U), S v →
        ∃ (W : B.Schemes) (f : W ⟶ V), IsProper (B.inclusion.map f) ∧
          Presieve.singleton f ∈ B.precoverage V ∧
          ∃ T : Presieve W, T ∈ (hAssociatedBigEtaleSite B).precoverage W ∧
            T.FactorsThruAlong R (f ≫ v) :=
  (hAssociatedBigEtaleSite B).exists_properRefinement_of_affine B.precoverage fun O hO => by
    obtain ⟨E, rfl, hE⟩ := hR
    have hh : IsHCovering (E.map B.inclusion).X (E.map B.inclusion).f := hE.1
    have : IsAffine O.toScheme := hO
    have hpb := isHCovering_pullback hh O.ι
    obtain ⟨J, W₀, p, V, j, hJ, hp, hps, hpfp, -, hj, hcov, hfac⟩ :=
      exists_finitePresentation_proper_refinement_of_isHCovering _ _ hpb
    have hW : W₀.size < B.cutoff := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p
      (Scheme.size_lt_of_isOpenImmersion O.ι U.2)
    let W : B.Schemes := ⟨W₀, hW⟩
    let f : W ⟶ B.obj O.toScheme (Scheme.size_lt_of_isOpenImmersion O.ι U.2) := ⟨p⟩
    refine ⟨W, f, hp, ?_, J, V, j, hj, hcov, fun k => ?_⟩
    · have hs : (PreZeroHypercover.singleton.{u + 1} f).presieve₀ = Presieve.singleton f := by
        simp
      rw [← hs, B.mem_precoverage_iff_isHCovering]
      exact (surjective_proper_isHCovering p hpfp).reindex Equiv.punitEquivPUnit
    · obtain ⟨s₀, h₀, hh₀⟩ := hfac k
      let s : E.I₀ := s₀
      let h : V k ⟶ pullback (B.inclusion.map (E.f s)) O.ι := h₀
      have hh : h ≫ pullback.snd (B.inclusion.map (E.f s)) O.ι = j k ≫ p := hh₀
      refine ⟨E.X s, E.f s, Presieve.ofArrows.mk _,
        h ≫ pullback.fst (B.inclusion.map (E.f s)) O.ι, ?_⟩
      have hc : pullback.fst (B.inclusion.map (E.f s)) O.ι ≫ B.inclusion.map (E.f s) =
          pullback.snd _ O.ι ≫ O.ι := pullback.condition
      show (h ≫ pullback.fst (B.inclusion.map (E.f s)) O.ι) ≫ B.inclusion.map (E.f s) =
        j k ≫ p ≫ O.ι
      rw [Category.assoc, hc, ← Category.assoc, hh, Category.assoc]

end BigHSite

end AlgebraicGeometry

end
