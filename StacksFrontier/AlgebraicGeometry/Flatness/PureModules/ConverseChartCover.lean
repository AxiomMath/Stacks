module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardConverseAux
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre

/-!
# The coverage input of the purity criterion, from the pointed form of Tag 05KW

The purity criterion of Tag 05L4, in the form
`AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range`, is a biconditional
whose hypotheses include a *coverage* clause: every associated point of the fibre of the base
change `X ×_S S' ⟶ S'` over the distinguished point `s'` is in the image of the induced morphism
`X' ⟶ X ×_S S'`. This file supplies that clause for the chart produced by Tag 05KW, and uses it
together with the purity input to run the criterion forward.

The chase is the following. A point of the fibre of `X ×_S S' ⟶ S'` over `s'` is pinned down by
its image in `X`: the fibre comparison `AlgebraicGeometry.baseChangeFiberMap` identifies that
fibre with the fibre `X_s`, and it is an isomorphism because the neighbourhood is elementary, so
the composite of the fibre inclusion with the projection to `X` is injective
(`AlgebraicGeometry.baseChangeFiber_fst_injective`). The pointed form of
Tag 05KW produces, for each point of `X_s`, a point of the chart mapping to it and lying over
`s'`; its image in `X ×_S S'` lies in the fibre over `s'` and has the same image in `X`, hence is
the point we started from.

The two projections alone do *not* determine a point of `X ×_S S'`, so the unpointed form of
Tag 05KW — which only gives `X_s ⊆ g(X')` — is not enough: injectivity of the fibre comparison,
that is, elementariness of the neighbourhood, is what makes the chase close.

## Main results

* `AlgebraicGeometry.exists_pullbackLift_eq_fiberι`: the coverage clause of Tag 05L4, from the
  pointed covering clause of Tag 05KW.
* `AlgebraicGeometry.relativeAssassin_specializing_mem_range_of_isPureAlong`: Tag 05L4 run
  forward at a chart of Tag 05KW.
* `AlgebraicGeometry.exists_chart_relativeAssassin_specializing_mem_range`: the same, with the
  chart produced rather than assumed.

## Implementation notes

That the fibre comparison is an isomorphism is `AlgebraicGeometry.isIso_baseChangeFiberMap`,
which assumes only that the residue field map at the point is an isomorphism. For an étale
neighbourhood that hypothesis is exactly elementariness
(`AlgebraicGeometry.isIso_toBase_residueFieldMap_of_isElementary`), which is why it is the one
this file feeds the comparison.

## References

* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The coverage hypothesis of Tag 05L4: every point of the fibre of the base change
`X ×_S S' ⟶ S'` over the distinguished point of an elementary étale neighbourhood is in the image
of the induced morphism from the chart.

The input is the *pointed* covering clause of Tag 05KW — each point of `X_s` is hit by a point of
the chart lying over the distinguished point — and the mechanism is
`AlgebraicGeometry.baseChangeFiber_fst_injective`: both the given point of the fibre and the image
of the chart point produced by the covering clause lie over the distinguished point and have the
same image in `X`, so they are equal. -/
theorem exists_pullbackLift_eq_fiberι {X S X' : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) (g : X' ⟶ X) (hcomm : g ≫ f = p ≫ U.toBase)
    (hcov : ∀ x : f.fiber s, ∃ y : X', g y = f.fiberι s x ∧ p y = U.point)
    (z : (pullback.snd f U.toBase).fiber U.point) :
    ∃ y : X', pullback.lift g p hcomm y =
      (pullback.snd f U.toBase).fiberι U.point z := by
  set w := (pullback.snd f U.toBase).fiberι U.point z with hw
  have hwfib : (pullback.snd f U.toBase) w = U.point :=
    ((pullback.snd f U.toBase).range_fiberι U.point).le ⟨z, rfl⟩
  have hx : f (pullback.fst f U.toBase w) = s := by
    have hc := congrArg (fun m : pullback f U.toBase ⟶ S => m w)
      (pullback.condition : pullback.fst f U.toBase ≫ f = pullback.snd f U.toBase ≫ U.toBase)
    simp only [Scheme.Hom.comp_apply] at hc
    rw [hc, hwfib, U.map_point]
  obtain ⟨y, hgy, hpy⟩ := hcov ((f.fiberHomeo s).symm ⟨pullback.fst f U.toBase w, hx⟩)
  rw [f.fiberι_fiberHomeo_symm] at hgy
  exact ⟨y, pullbackLift_eq_fiberι_of_fst_eq f U hU p g hcomm z y hpy hgy⟩

/-- Purity of the chart's module along the chart's fibre, from projectivity of the chart's
sections. This is the hypothesis `hpure'` of Tag 05L4.

It is supplied by the *forward* implication of Tag 05MD already proved in
`AlgebraicGeometry.isPureRelative_of_isLocallyProjective_pushforward`: projectivity of
`Γ(X', g^*ℱ)` over `Γ(S', 𝒪_{S'})` says exactly that the direct image of `g^*ℱ` along the affine
morphism `X' ⟶ S'` is locally projective, and relative purity of `g^*ℱ` over `S'` follows, of
which purity along the fibre over the distinguished point is one instance. -/
theorem isPureAlong_of_projective_sections_of_isAffine {S X' : Scheme.{u}} [IsAffine X']
    [IsAffine S] (p : X' ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p] (G : X'.Modules)
    [G.IsFiniteType] [G.IsQuasicoherent] (s : S)
    (hproj : letI : Module Γ(S, ⊤) Γ(G, ⊤) := Module.compHom Γ(G, ⊤) p.appTop.hom
      Module.Projective Γ(S, ⊤) Γ(G, ⊤)) :
    IsPureAlong ({ S := S, X := X', f := p, F := G, s := s } : PrePureSituation.{u}) := by
  have : IsAffineHom p := isAffineHom_of_isAffine p
  exact isPureRelative_of_isLocallyProjective_pushforward p G
    (isLocallyProjective_pushforward_of_projective_sections p G hproj) s

/-- Tag 05L4 run forward at a chart of the shape Tag 05KW produces: if `ℱ` is pure along `X_s`,
then the image of `X' ⟶ X ×_S S'` contains every point of the relative assassin of the base
change lying over a point specializing to the distinguished point.

The two hypotheses that Tag 05L4 needs beyond the data of the chart are both discharged here:
the purity input `hpure'` is
`AlgebraicGeometry.isPureAlong_of_projective_sections_of_isAffine` applied to the projectivity of
the chart's sections, and the coverage input is
`AlgebraicGeometry.exists_pullbackLift_eq_fiberι`. -/
theorem relativeAssassin_specializing_mem_range_of_isPureAlong
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    {s : S} (U : EtaleNeighborhood S s) (hU : U.IsElementary) [IsAffine U.scheme]
    (p : X' ⟶ U.scheme) [IsAffine X'] [LocallyOfFiniteType p]
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hproj : let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
      letI : Module Γ(U.scheme, ⊤) N := Module.compHom N p.appTop.hom
      Module.Projective Γ(U.scheme, ⊤) N)
    (hcov : ∀ x : f.fiber s, ∃ y : X', g y = f.fiberι s x ∧ p y = U.point)
    (hpure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})) :
    ∀ x : pullback (C := Scheme.{u}) f U.toBase,
      x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
          ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
        pullback.snd f U.toBase x ⤳ U.point →
          x ∈ Set.range (pullback.lift g p hcomm) := by
  have hFqc : F.IsQuasicoherent := inferInstance
  have hG : ((Scheme.Modules.pullback g).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
  have hGqc : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace X.toRingedSpace
      g.toLRSHom.toShHom F hFqc
  refine (isPureAlong_iff_relativeAssassin_specializing_mem_range f F s U hU p g hcomm hflat
    (isPureAlong_of_projective_sections_of_isAffine p ((Scheme.Modules.pullback g).obj F) U.point
      hproj) ?_).mp hpure
  intro z _
  exact exists_pullbackLift_eq_fiberι f U hU p g hcomm hcov z

/-- The conclusion of `AlgebraicGeometry.relativeAssassin_specializing_mem_range_of_isPureAlong`
with the chart produced rather than assumed: for `f` of finite presentation and `ℱ` of finite
presentation, quasi-coherent and flat over `S` along `X_s`, purity of `ℱ` along `X_s` yields an
affine elementary étale neighbourhood and an affine chart étale over `X` whose sections are
projective and whose image in `X ×_S S'` contains the relevant part of the relative assassin.

The chart is the one Tag 05KW produces, in the pointed form
`AlgebraicGeometry.exists_elementary_pointed_projective_cover`; local finite type of its structure
morphism `X' ⟶ S'` is read off from the commutative square, the composite `X' ⟶ X ⟶ S` being
locally of finite type. -/
theorem exists_chart_relativeAssassin_specializing_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure : IsPureAlong
      ({ S := S
         X := X
         f := f
         F := F
         isFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
         s := s } : PrePureSituation.{u})) :
    ∃ (U : EtaleNeighborhood S s) (X' : Scheme.{u}) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
      (hcomm : g ≫ f = p ≫ U.toBase),
      U.IsElementary ∧ IsAffine U.scheme ∧ IsAffine X' ∧ Etale g ∧ LocallyOfFiniteType p ∧
      (let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
       letI : Module Γ(U.scheme, ⊤) N := Module.compHom N p.appTop.hom
       Module.Projective Γ(U.scheme, ⊤) N) ∧
      ∀ x : pullback (C := Scheme.{u}) f U.toBase,
        x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
          pullback.snd f U.toBase x ⤳ U.point →
            x ∈ Set.range (pullback.lift g p hcomm) := by
  have hFt : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hflat
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  obtain ⟨A, hAe, hAa, Y, hY, h, g, hg, hcomm, hcov, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f F s hf hflat
  have hcompLFT : LocallyOfFiniteType (h ≫ A.toBase) := by rw [hcomm]; infer_instance
  have hLFT : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h A.toBase
  exact ⟨A, Y, h, g, hcomm.symm, hAe, hAa, hY, hg, hLFT, hproj,
    relativeAssassin_specializing_mem_range_of_isPureAlong f F A hAe h g hcomm.symm hflat
      hproj hcov hpure⟩

end AlgebraicGeometry

end
