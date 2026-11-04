module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ConverseEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ConverseRingCore
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 05MD: local projectivity of the direct image is relative purity

Let `f : X ⟶ S` be an affine morphism of finite presentation and let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite presentation which is flat over `S`. Tag 05MD asserts that the direct image
`f_*ℱ` is locally projective on `S` if and only if `ℱ` is pure relative to `S`, and specializes
this to a ring map `A → B` of finite presentation and a finitely presented `B`-module `N` flat
over `A`.

The implication from local projectivity to purity is
`AlgebraicGeometry.isPureRelative_of_isLocallyProjective_pushforward`, proved without flatness or
finite presentation. This file proves the converse and states the biconditional in both forms.

## The shape of the converse

Local projectivity is a local condition on `S`, and it descends along an fpqc covering by Tag
05JZ, so it suffices to produce, at each point `s` of `S`, an étale morphism to `S` whose image
contains `s` and over which the sections of the pullback of `f_*ℱ` are projective. Purity of `ℱ`
along `X_s` supplies exactly such data through
`AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong`: an affine
elementary étale neighbourhood `S'` of `s`, an affine chart `X'` étale over `X` whose sections are
projective over `Γ(S', 𝒪_{S'})`, and an affine open `W₀ ∋ s'` of `S'` over every point of which
the associated points of the fibre of `ℱ ×_S S'` lie in the image of `X' ⟶ X ×_S S'`.

Over `W₀` the situation is entirely affine, and the chart hypothesis becomes the hypothesis of
Tag 05DH; `AlgebraicGeometry.projective_sections_of_fibrewiseContainment` turns it into
projectivity of the sections of `ℱ ×_S S'` on the preimage of `W₀`, which is projectivity of the
sections of the direct image of `ℱ ×_S S'` on `W₀` itself. Tag 02KG identifies that direct image
with the pullback of `f_*ℱ` to `S'`, and
`AlgebraicGeometry.isLocallyProjective_of_forall_exists_etale_affineOpen` performs the descent.

## Main results

* `AlgebraicGeometry.isLocallyProjective_pushforward_of_isPureRelative`: the converse implication
  in the scheme form.
* `AlgebraicGeometry.isLocallyProjective_pushforward_iff_isPureRelative`: Tag 05MD, the scheme
  biconditional.
* `AlgebraicGeometry.projective_iff_isPureRelative_tilde`: Tag 05MD, the ring biconditional.

## References

* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The data the chart of
`AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong` provides, turned
into projectivity of the sections of the pullback of the direct image on an affine open of the
neighbourhood.

The chart's projectivity is fed to
`AlgebraicGeometry.isLocallyProjective_pushforward_of_projective_sections` and transported to the
direct image along `X' ⟶ X ×_S S' ⟶ S'` with
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; the ring core
`AlgebraicGeometry.projective_sections_of_fibrewiseContainment` consumes it together with the
containment statement, and Tag 02KG
(`AlgebraicGeometry.projective_sections_pullback_pushforward`) puts the answer on the pullback of
`f_*ℱ`. -/
theorem projective_sections_pullback_pushforward_of_chart {X S X' : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    (U : EtaleNeighborhood S s) [IsAffine U.scheme] (p : X' ⟶ U.scheme) [IsAffine X']
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hproj : let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
      letI : Module Γ(U.scheme, ⊤) N := Module.compHom N p.appTop.hom
      Module.Projective Γ(U.scheme, ⊤) N)
    {WO : (U.scheme).Opens} (hWO : IsAffineOpen WO)
    (hWOsub : (WO : Set U.scheme) ⊆ Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd f U.toBase)
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)
      (chartImageOpens f U p g hcomm)) :
    Module.Projective Γ(U.scheme, WO)
      Γ((Scheme.Modules.pullback U.toBase).obj ((Scheme.Modules.pushforward f).obj F), WO) := by
  have hqEtale : Etale (pullback.lift g p hcomm) :=
    etale_pullback_lift_of_etale f U.toBase g p hcomm
  have hGqc : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
    isQuasicoherent_pullback_obj g F
  have hFUqc : ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F).IsQuasicoherent :=
    isQuasicoherent_pullback_obj _ F
  have hflatFU : IsFlatOver (pullback.snd f U.toBase).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) :=
    @modulePullback_isFlatOver _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback f U.toBase) F
      (show F.IsQuasicoherent from inferInstance) hflat
  -- the chart's module is the restriction to `X'` of the base change, by `pullbackComp`
  have heG : (Scheme.Modules.pullback (pullback.lift g p hcomm)).obj
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) ≅
        (Scheme.Modules.pullback g).obj F :=
    (Scheme.Modules.pullbackComp (pullback.lift g p hcomm) (pullback.fst f U.toBase)).app F ≪≫
      (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app F
  -- the chart hypothesis, as local projectivity of a direct image along `X' ⟶ S'`
  have hchart : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward (pullback.lift g p hcomm ≫ pullback.snd f U.toBase)).obj
        ((Scheme.Modules.pullback (pullback.lift g p hcomm)).obj
          ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F))) := by
    rw [pullback.lift_snd]
    exact Scheme.Modules.isLocallyProjective_of_iso
      ((Scheme.Modules.pushforward p).mapIso heG).symm
      (isLocallyProjective_pushforward_of_projective_sections p _ hproj)
  -- the ring core, then Tag 02KG
  exact projective_sections_pullback_pushforward f U.toBase F WO
    (projective_sections_of_fibrewiseContainment (pullback.snd f U.toBase) _ hflatFU
      (pullback.lift g p hcomm) hWO (chartImageOpens f U p g hcomm) subset_rfl hWOsub hchart)

/-- **Stacks Project, Tag 05MD**, the implication from (2) to (1). For an affine morphism of
finite presentation, a quasi-coherent module of finite presentation which is flat over the base
and pure relative to the base has locally projective direct image.

At each point of the base, purity along the fibre produces the chart of Tag 05KW and the affine
open of Tags 05KR and 05LW
(`AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong`); over that
affine open the sections of the pullback of the direct image are projective by
`AlgebraicGeometry.projective_sections_pullback_pushforward_of_chart`. The affine opens so
obtained form an étale, hence fpqc, covering family of the base, and Tag 05JZ descends local
projectivity along it. -/
@[sga "3 VIB 6.9" "6.9 a)"]
theorem isLocallyProjective_pushforward_of_isPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    letI : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
    IsPureRelative f F →
      Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f).obj F) := by
  intro hpure
  refine isLocallyProjective_of_forall_exists_etale_affineOpen _ fun s => ?_
  obtain ⟨U, X', p, g, hcomm, hUa, hX'a, hgE, _, hLFT, hproj, WO, hWOaff, hWOmem, hWOsub⟩ :=
    exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong f F s
      (fun x => hflat (f.fiberι s x)) (hpure s)
  exact ⟨U.scheme, U.toBase, inferInstance, WO, hWOaff, ⟨U.point, hWOmem, U.map_point⟩,
    projective_sections_pullback_pushforward_of_chart f F hflat U p g hcomm hproj hWOaff hWOsub⟩

/-- **Stacks Project, Tag 05MD**, the scheme form. For an affine morphism of finite presentation
and a quasi-coherent module of finite presentation which is flat over the base, the direct image
is locally projective exactly when the module is pure relative to the base.

The implication from local projectivity to purity is
`AlgebraicGeometry.isPureRelative_of_isLocallyProjective_pushforward`, which needs neither
flatness nor finite presentation; the converse is
`AlgebraicGeometry.isLocallyProjective_pushforward_of_isPureRelative`. -/
@[stacks 05MD "the scheme criterion, as a biconditional", sga "3 VIB 6.9" "more general"]
theorem isLocallyProjective_pushforward_iff_isPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    letI : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
    Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f).obj F) ↔
      IsPureRelative f F :=
  let : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  ⟨isPureRelative_of_isLocallyProjective_pushforward f F,
    isLocallyProjective_pushforward_of_isPureRelative f F hflat⟩

/-- **Stacks Project, Tag 05MD**, the ring form. Let `A → B` be of finite presentation and let `N`
be a finitely presented `B`-module which is flat over `A`. Then `N` is projective over `A` exactly
when the sheaf `Ñ` on `Spec B` is pure relative to `Spec A`.

Both directions come from the scheme form applied to `Spec B ⟶ Spec A`: the direct image of `Ñ`
is the sheaf associated to `N` viewed as an `A`-module (Tag 01I9,
`AlgebraicGeometry.pushforwardTildeIso`), so local projectivity of the direct image is
projectivity of that `A`-module by Tag 05JQ
(`AlgebraicGeometry.isLocallyProjective_tilde_iff_projective`). -/
@[stacks 05MD "the affine ring specialization, as a biconditional"]
theorem projective_iff_isPureRelative_tilde (A B N : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Algebra.FinitePresentation A B] [Module.FinitePresentation B N] [Module.Flat A N] :
    Module.Projective A N ↔
      IsPureRelative (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (tilde (ModuleCat.of (CommRingCat.of B) N)) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let M : ModuleCat.{u} (CommRingCat.of B) := ModuleCat.of (CommRingCat.of B) N
  let NA : ModuleCat.{u} (CommRingCat.of A) := (ModuleCat.restrictScalars φ.hom).obj M
  have : (tilde M).IsFinitePresentation := (tilde_isFinitePresentation_iff M).2 inferInstance
  -- `N` with its `A`-action is `N` with the action restricted along `A → B`
  have e : N ≃ₗ[A] NA :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r n =>
        (IsScalarTower.algebraMap_smul (A := B) (M := N) r n).symm }
  have hiso : (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅ tilde NA :=
    (pushforwardTildeIso (CommRingCat.of A) (CommRingCat.of B) φ).app M
  refine Iff.trans ?_ (isLocallyProjective_pushforward_iff_isPureRelative (Spec.map φ) (tilde M)
    (isFlatOver_spec_tilde_of_flat φ M rfl inferInstance))
  constructor
  · intro hNproj
    have hprojNA : Module.Projective (CommRingCat.of A) NA := Module.Projective.of_equiv e
    exact Scheme.Modules.isLocallyProjective_of_iso hiso.symm
      ((isLocallyProjective_tilde_iff_projective (CommRingCat.of A) NA).2 hprojNA)
  · intro hLP
    have hNA : Module.Projective (CommRingCat.of A) NA :=
      (isLocallyProjective_tilde_iff_projective (CommRingCat.of A) NA).1
        (Scheme.Modules.isLocallyProjective_of_iso hiso hLP)
    exact Module.Projective.of_equiv e.symm

end AlgebraicGeometry

end
