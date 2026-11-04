module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalize
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRelocalizeRepresentable

/-!
# Finite presentation hypotheses of a relative Hom situation

For a relative Hom situation `(f : X ⟶ B, F, G)`, the hypotheses that `f`, `F` and `G` are of
finite presentation and that `G` is flat over `B` with support proper over `B` are kept by base
change along any `B' ⟶ B` and by relocalization along a morphism `h : W ⟶ S` of the site. Hence,
if the relative Hom functor is an algebraic space affine and of finite presentation over the base
for every such situation over `Spec ℤ` whose base is an affine scheme of finite type over `ℤ`, the
same holds for every such situation.

## Main results

* `AlgebraicGeometry.Space.HomSituation.finitePresentationHypotheses_baseChangedSituation`: the
  hypotheses are kept by base change of the base.
* `AlgebraicGeometry.Space.HomSituation.finitePresentationHypotheses_relocalize`: the hypotheses
  are kept by relocalization of the base scheme.
* `isAffineFinitePresentationAlgebraicSpaceOverBase_of_stages_of_isFinitePresentation`
  (in `AlgebraicGeometry.Space.HomSituation`): the relative Hom functor of a situation satisfying
  the hypotheses is an algebraic space affine and of finite presentation over the base, as soon as
  this holds over affine bases of finite type over `ℤ`.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.HomSituation

open CoherentSituation

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)
  {base' : AlgebraicSpaces B S hS} (p : base' ⟶ s.base)

/-- Finite presentation of the morphism and of the two modules, flatness of `G` over the base and
properness of its support are kept by base change of the base along `p`. -/
theorem finitePresentationHypotheses_baseChangedSituation
    (hf : IsFinitePresentation B S hS s.f.hom) (hF : s.F.IsFinitePresentationOnSite)
    (hG : s.G.IsFinitePresentationOnSite) (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G)
    (hproper : HasProperSupportOver s.f s.G) :
    IsFinitePresentation B S hS (s.baseChangedSituation p).f.hom ∧
      (s.baseChangedSituation p).F.IsFinitePresentationOnSite ∧
      (s.baseChangedSituation p).G.IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (s.baseChangedSituation p).X.2 (s.baseChangedSituation p).f.hom
        (s.baseChangedSituation p).G ∧
      HasProperSupportOver (s.baseChangedSituation p).f (s.baseChangedSituation p).G := by
  have sq : IsPullback (s.baseChangedSourceProjection p) (s.baseChangedMorphism p) s.f p :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS s.f p
  exact ⟨IsFinitePresentation.of_isPullback B S hS (s.baseChangedSource p).2 s.X.2 base'.2
      s.base.2 (AlgebraicSpaces.isPullback_hom B S hS sq) hf,
    isFinitePresentationOnSite_modulePullback B S hS _ _ hF,
    isFinitePresentationOnSite_modulePullback B S hS _ _ hG,
    isFlatOver_modulePullback_of_isFinitePresentationOnSite B S hS sq s.G hG hflat,
    hproper.of_isPullback sq hG⟩

end BaseChange

section Relocalize

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) (s : HomSituation B W hW)

/-- Finite presentation of the morphism and of the two modules, flatness of `G` over the base and
properness of its support are kept by relocalization of the base scheme along `h : W ⟶ S`. -/
theorem finitePresentationHypotheses_relocalize
    (hf : IsFinitePresentation B W hW s.f.hom) (hF : s.F.IsFinitePresentationOnSite)
    (hG : s.G.IsFinitePresentationOnSite) (hflat : IsFlatOver B W hW s.X.2 s.f.hom s.G)
    (hproper : HasProperSupportOver s.f s.G) :
    IsFinitePresentation B S hS (s.relocalize h).f.hom ∧
      (s.relocalize h).F.IsFinitePresentationOnSite ∧
      (s.relocalize h).G.IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (s.relocalize h).X.2 (s.relocalize h).f.hom (s.relocalize h).G ∧
      HasProperSupportOver (s.relocalize h).f (s.relocalize h).G := by
  refine ⟨⟨(Space.holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h _ s.f.hom).2 hf.1,
      (isQuasiCompact_relocalize_iff B W hW S hS h s.f.hom).2 hf.2.1,
      (isQuasiSeparated_relocalize_iff B W hW S hS h s.f.hom).2 hf.2.2⟩,
    isFinitePresentationOnSite_relocalizeModulesEquivalence_functor h s.F hF,
    isFinitePresentationOnSite_relocalizeModulesEquivalence_functor h s.G hG,
    isFlatOver_relocalizeModulesEquivalence_functorSE B W S hW hS h s.f.hom s.X.2 _ s.G hflat, ?_⟩
  obtain ⟨hp, hU, hpr⟩ := hproper
  exact ⟨_, (hasProperSupport_relocalizeModulesEquivalence_functor_iffSE B W S hW hS h
    s.X.2 s.base.2 s.f.hom (relocalizeSpaceSE B W S hW hS h s.X).2
    (relocalizeSpaceSE B W S hW hS h s.base).2 hp s.G).2 ⟨hU, hpr⟩⟩

end Relocalize

section Reduction

variable {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W}

/-- Let `(f : X ⟶ B, F, G)` be a relative Hom situation over a scheme `W` of the site with `f` of
finite presentation, `F` and `G` of finite presentation, `G` flat over `B` and with support proper
over `B`. If the relative Hom functor is an algebraic space affine and of finite presentation over
the base for every such situation over `Spec ℤ` whose base is an affine scheme of finite type over
`ℤ`, then `Hom(F, G)` is an algebraic space affine and of finite presentation over `B`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_stages_of_isFinitePresentation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hstage : ∀ (T₀ : BigAffineFppf B (⊤_ Scheme.{u}) hZ),
      LocallyOfFiniteType (terminal.from ((BigAffineFppf.toScheme _ _ hZ).obj T₀)) →
      ∀ (v : HomSituation B (⊤_ Scheme.{u}) hZ),
        v.base = (schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T₀) →
        IsFinitePresentation B _ hZ v.f.hom → v.F.IsFinitePresentationOnSite →
        v.G.IsFinitePresentationOnSite → IsFlatOver B _ hZ v.X.2 v.f.hom v.G →
        HasProperSupportOver v.f v.G →
        v.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B _ hZ))
    (s : HomSituation B W hW) (hc : ModulePushforwardCoherence B W hW)
    (hf : IsFinitePresentation B W hW s.f.hom) (hF : s.F.IsFinitePresentationOnSite)
    (hG : s.G.IsFinitePresentationOnSite) (hflat : IsFlatOver B W hW s.X.2 s.f.hom s.G)
    (hproper : HasProperSupportOver s.f s.G) :
    s.IsAffineFinitePresentationAlgebraicSpaceOverBase hc := by
  let h : B.obj hW ⟶ B.obj hZ := ⟨terminal.from W⟩
  refine s.isAffineFinitePresentationAlgebraicSpaceOverBase_of_relocalize h hc fun Z hZaff p => ?_
  obtain ⟨hf₁, hF₁, hG₁, hflat₁, hproper₁⟩ :=
    s.finitePresentationHypotheses_baseChangedSituation p hf hF hG hflat hproper
  obtain ⟨hf₂, hF₂, hG₂, hflat₂, hproper₂⟩ :=
    (s.baseChangedSituation p).finitePresentationHypotheses_relocalize h hf₁ hF₁ hG₁ hflat₁
      hproper₁
  obtain ⟨hf₃, hF₃, hG₃, hflat₃, hproper₃⟩ :=
    ((s.baseChangedSituation p).relocalize h).finitePresentationHypotheses_baseChangedSituation
      (relocalizeSchemeSpaceHom B W (⊤_ Scheme.{u}) hW hZ h Z) hf₂ hF₂ hG₂ hflat₂ hproper₂
  let T : BigAffineFppf B (⊤_ Scheme.{u}) hZ := ⟨(Over.map h).obj Z, hZaff⟩
  exact (isAffineFinitePresentationAlgebraicSpaceOverBase_of_stages hZ hstage T _ (Iso.refl _)
    hf₃ hF₃ hG₃ hflat₃ hproper₃).exists_scheme

end Reduction

end AlgebraicGeometry.Space.HomSituation

end
