module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleLocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The projective bundle of an invertible module on an algebraic space

Let `X` be an algebraic space over a scheme `S` and `ℒ` an invertible `𝒪_X`-module on the small
étale site of `X`.  With the normalization of Stacks 0ERT, the projective bundle
`π : P = 𝐏(ℒ) = Proj_X(Sym^*(ℒ)) ⟶ X` is `X` itself, and `𝒪_P(1) = ℒ`: the projection `π` is an
isomorphism, and the tautological surjection `π^*ℒ ⟶ 𝒪_P(1)` is an isomorphism.  This is the
normalization the proof of Stacks 0ES0 reads off ("`P = 𝐏(ℒ) = X` with `𝒪_P(1) = ℒ`").

The first statement is read on the presenting chart `U` of `X`.  There `π` is the projection of
the projective bundle of the chart restriction `ℒ|_U`, a module of rank one, which is
Zariski-locally on `U` the projective space `ℙ⁰`, that is an isomorphism; and a morphism of
algebraic spaces whose base change along a surjective étale chart is an isomorphism is an
isomorphism (Stacks 041Y).  The second is that a surjection between invertible modules is an
isomorphism: `π^*ℒ` is invertible (Stacks 0B8P) and so is `𝒪_P(1)`.

## Main results

* `Stacks.ProjectiveBundle.isIso_of_isLocallyProjectiveSpace_zero`: a morphism of schemes which
  is Zariski-locally on the target `ℙ⁰` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_of_isPullback_of_isIso_of_surjective_of_etale`: a morphism of
  algebraic spaces whose base change along a surjective étale scheme chart of the target is an
  isomorphism is an isomorphism.
* `AlgebraicGeometry.Space.isIso_projectiveBundleProj_of_rank_one` and
  `AlgebraicGeometry.Space.isIso_projectiveBundleProj_of_isInvertibleModule`: **the projection
  `𝐏(ℒ) ⟶ X` is an isomorphism.**
* `AlgebraicGeometry.Space.projectiveBundleTwistIsoOfIsInvertibleModule`: **`π^*ℒ ≅ 𝒪_P(1)`**,
  through the tautological surjection, an isomorphism by
  `AlgebraicGeometry.Space.PrivateChern.isIso_projectiveBundleTautological`.
* `AlgebraicGeometry.Space.projectiveBundleTwistInvPullbackIso`: the same read on `X`,
  `(π⁻¹)^*𝒪_P(1) ≅ ℒ`.

## References

* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
* [Stacks Project, Tag 0ES0](https://stacks.math.columbia.edu/tag/0ES0)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundle

/-- **A morphism of schemes which is Zariski-locally on the target the projective space `ℙ⁰` is
an isomorphism**: being an isomorphism is local on the target, and `ℙ⁰_V ⟶ V` is an
isomorphism. -/
theorem isIso_of_isLocallyProjectiveSpace_zero {H P : AlgebraicGeometry.Scheme.{u}} {f : H ⟶ P}
    (hf : IsLocallyProjectiveSpace f 0) : IsIso f := by
  change MorphismProperty.isomorphisms AlgebraicGeometry.Scheme f
  refine AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (f := f) fun y => ?_
  obtain ⟨V, hyV, e, he⟩ := hf y
  refine ⟨V, hyV, ?_⟩
  rw [← he]
  exact inferInstanceAs (IsIso (e.hom ≫ (AlgebraicGeometry.projectiveSpaceOver 0 V.toScheme ↘
    V.toScheme)))

end Stacks.ProjectiveBundle

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **A morphism of algebraic spaces whose base change along a surjective étale scheme chart of
the target is an isomorphism is an isomorphism.**  Given a cartesian square
`P ×_X U = P'` with `c : U ⟶ X` surjective and étale and `P' ⟶ U` an isomorphism of the site,
`f : Y ⟶ X` is an isomorphism: the chart is an fppf covering of `X`, and being an isomorphism is
fppf local on the target (Stacks 041Y). -/
theorem isIso_of_isPullback_of_isIso_of_surjective_of_etale {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) {U P : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X.1} {c' : yoneda.obj P ⟶ Y.1}
    {p : P ⟶ U}
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hpb : IsPullback c' (yoneda.map p) f.hom c) [IsIso p] : IsIso f := by
  let V : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let cV : V ⟶ X := ObjectProperty.homMk c
  refine isIso_of_forall_isIso_pullback_snd B S hS f (fun _ : PUnit.{1} => V) (fun _ => cV)
    (isFppfCovering_atlas B S hS X.property hsurj het) fun _ => ?_
  refine isIso_pullback_snd_of_isIso_pullback_snd_hom B S hS f cV ?_
  change IsIso (pullback.snd f.hom c)
  rw [← hpb.isoPullback_inv_snd]
  infer_instance

section RankOne

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]

/-- Over an étale chart, the projection of the chart bundle of a module of rank one is an
isomorphism. -/
theorem isIso_chartBundleToChart_of_rank_one
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E 1)
    (V : SmallEtale B S hS X.1) : IsIso (chartBundleToChart E V) :=
  Stacks.ProjectiveBundle.isIso_of_isLocallyProjectiveSpace_zero
    (isLocallyProjectiveSpace_chartBundleToChart E 0 hr V)

/-- **The projection of the projective bundle of a module of rank one is an isomorphism**:
`𝐏(ℒ) = X`. -/
theorem isIso_projectiveBundleProj_of_rank_one
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E 1)
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    IsIso (projectiveBundleProj E hfree) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map
      ((projectiveBundleChartFamily E hfree).siteToChart
        (presentationChart (projectiveBundlePresentation X)))) := by
    rw [CartesianChartFamily.toScheme_map_siteToChart]
    exact isIso_chartBundleToChart_of_rank_one E hr _
  have : IsIso ((projectiveBundleChartFamily E hfree).siteToChart
      (presentationChart (projectiveBundlePresentation X))) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  exact isIso_of_isPullback_of_isIso_of_surjective_of_etale (projectiveBundleProj E hfree)
    (surjective_projectiveBundlePresentation X)
    (presentationChart (projectiveBundlePresentation X)).property
    (isPullback_projectiveBundleProj E hfree)

end RankOne

section Invertible

variable (L : Modules.{u, u} B S hS X.1 X.2) [hLq : L.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite L) (hL : IsInvertibleModule X L)

include hL

/-- **The projective bundle of an invertible module is the base**: for `ℒ` invertible on `X` the
projection `π : 𝐏(ℒ) ⟶ X` is an isomorphism.  An invertible module has rank one (Stacks 0B8Q). -/
theorem isIso_projectiveBundleProj_of_isInvertibleModule :
    IsIso (projectiveBundleProj L hfree) :=
  isIso_projectiveBundleProj_of_rank_one L
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL)) hfree

/-- **`𝒪_P(1) = π^*ℒ` on the projective bundle `P = 𝐏(ℒ)` of an invertible module**: the
tautological surjection `π^*ℒ ⟶ 𝒪_P(1)` is an isomorphism
(`AlgebraicGeometry.Space.PrivateChern.isIso_projectiveBundleTautological`). -/
def projectiveBundleTwistIsoOfIsInvertibleModule :
    (modulePullback B S hS (projectiveBundleProj L hfree)).obj L ≅
      (projectiveBundleTwist L hfree).obj :=
  haveI := PrivateChern.isIso_projectiveBundleTautological L hfree hL
  asIso (projectiveBundleTautological L hfree).hom

/-- The forward map of `projectiveBundleTwistIsoOfIsInvertibleModule` is the tautological
surjection `π^*ℒ ⟶ 𝒪_P(1)`. -/
@[simp]
theorem projectiveBundleTwistIsoOfIsInvertibleModule_hom :
    (projectiveBundleTwistIsoOfIsInvertibleModule L hfree hL).hom =
      (projectiveBundleTautological L hfree).hom :=
  rfl

/-- **`𝒪_P(1) = ℒ` under the identification `P = 𝐏(ℒ) = X`**: the inverse image of `𝒪_P(1)`
along the inverse `X ⟶ P` of the projection is `ℒ`. -/
def projectiveBundleTwistInvPullbackIso :
    haveI := isIso_projectiveBundleProj_of_isInvertibleModule L hfree hL
    (modulePullback B S hS (inv (projectiveBundleProj L hfree))).obj
        (projectiveBundleTwist L hfree).obj ≅ L :=
  haveI := isIso_projectiveBundleProj_of_isInvertibleModule L hfree hL
  (modulePullback B S hS (inv (projectiveBundleProj L hfree))).mapIso
      (projectiveBundleTwistIsoOfIsInvertibleModule L hfree hL).symm ≪≫
    (modulePullbackCompIso B S hS (inv (projectiveBundleProj L hfree))
      (projectiveBundleProj L hfree)).app L ≪≫
    eqToIso (congrArg (fun g => (modulePullback B S hS g).obj L) (IsIso.inv_hom_id _)) ≪≫
    (modulePullbackIdIso B S hS X).app L

end Invertible

end AlgebraicGeometry.Space

end
