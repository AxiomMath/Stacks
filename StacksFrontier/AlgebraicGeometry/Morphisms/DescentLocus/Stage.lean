module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperFlatModule
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE

/-!
# A Noetherian stage for the descent problem over an affine open

Let `f : X ⟶ S` be a morphism and `E` a module on `X`. Over an affine open `V` of `S` the base
change `X_V ⟶ Spec Γ(S, V)` of `f` is, in the situation of [Stacks, Tag 0BDP], the base change of a
proper morphism `X₀ ⟶ Spec A₀` with `A₀` Noetherian, and the restriction of `E` is the pullback
of a coherent module `E₀` flat over `A₀`. Such data is a `NoetherianStage`.

The point of a stage is that, for any `h : T ⟶ Spec Γ(S, V)`, the base change of `f` along
`h ≫ V.fromSpec` is a base change of `X₀` along `h ≫ Spec φ`, and the pullback of `E` is the
pullback of `E₀`; this is `NoetherianStage.isPullback_stageMap` and `NoetherianStage.stageIso`.

## Main definitions

* `AlgebraicGeometry.DescentLocus.NoetherianStage`: the data of a Noetherian stage.
* `AlgebraicGeometry.DescentLocus.NoetherianStage.stageMap`: the map from the base change of `X`
  along `h ≫ V.fromSpec` to `X₀`.

## Main results

* `AlgebraicGeometry.DescentLocus.NoetherianStage.isPullback_stageMap`: the square over `X₀` is
  cartesian.
* `AlgebraicGeometry.DescentLocus.NoetherianStage.stageIso`: the two pullbacks of the module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentLocus

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) {V : S.Opens} (hV : IsAffineOpen V)

/-- A **Noetherian stage** of `f` and `E` over the affine open `V`: a Noetherian ring `A₀` with a
map `φ : A₀ ⟶ Γ(S, V)`, a proper `f₀ : X₀ ⟶ Spec A₀` whose base change along `Spec φ` is the base
change of `f` to `V`, and a coherent `E₀` flat over `A₀` pulling back to the restriction of `E`. -/
structure NoetherianStage where
  /-- The Noetherian ring. -/
  A₀ : Type u
  [commRing : CommRing A₀]
  [isNoetherianRing : IsNoetherianRing A₀]
  /-- The ring map to the sections over `V`. -/
  φ : A₀ →+* Γ(S, V)
  /-- The model of `X`. -/
  X₀ : Scheme.{u}
  /-- The model of `f`. -/
  f₀ : X₀ ⟶ Spec (.of A₀)
  /-- The comparison map. -/
  g : pullback f hV.fromSpec ⟶ X₀
  /-- The model of `E`. -/
  E₀ : X₀.Modules
  isProper : IsProper f₀
  isPullback : IsPullback g (pullback.snd f hV.fromSpec) f₀ (Spec.map (CommRingCat.ofHom φ))
  isCoherent : E₀.IsCoherent
  isFlatOver : IsFlatOver f₀.toLRSHom.toShHom E₀
  /-- The restriction of `E` is the pullback of the model. -/
  iso : (Scheme.Modules.pullback (pullback.fst f hV.fromSpec)).obj E ≅
    (Scheme.Modules.pullback g).obj E₀

variable {T : Scheme.{u}} (h : T ⟶ Spec Γ(S, V))

/-- The comparison from the base change along `h ≫ V.fromSpec` to the base change along
`V.fromSpec`. -/
def toChart : pullback f (h ≫ hV.fromSpec) ⟶ pullback f hV.fromSpec :=
  pullback.lift (pullback.fst f (h ≫ hV.fromSpec)) (pullback.snd f (h ≫ hV.fromSpec) ≫ h)
    (by simp [pullback.condition])

/-- The comparison `toChart` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem toChart_fst :
    toChart f hV h ≫ pullback.fst f hV.fromSpec = pullback.fst f (h ≫ hV.fromSpec) :=
  pullback.lift_fst _ _ _

/-- The second projection of `toChart` is the second projection followed by `h`. -/
@[reassoc (attr := simp)]
theorem toChart_snd :
    toChart f hV h ≫ pullback.snd f hV.fromSpec = pullback.snd f (h ≫ hV.fromSpec) ≫ h :=
  pullback.lift_snd _ _ _

/-- The square formed by `toChart`, the two second projections and `h` is cartesian. -/
theorem isPullback_toChart :
    IsPullback (toChart f hV h) (pullback.snd f (h ≫ hV.fromSpec)) (pullback.snd f hV.fromSpec)
      h := by
  refine IsPullback.of_right ?_ (toChart_snd f hV h) (IsPullback.of_hasPullback f hV.fromSpec)
  simpa using IsPullback.of_hasPullback f (h ≫ hV.fromSpec)

namespace NoetherianStage

attribute [instance] commRing isNoetherianRing isProper isCoherent

variable {f E hV} (St : NoetherianStage f E hV)

/-- The map from the base change along `h ≫ V.fromSpec` to the model `X₀`. -/
def stageMap : pullback f (h ≫ hV.fromSpec) ⟶ St.X₀ := toChart f hV h ≫ St.g

/-- **The base change along `h ≫ V.fromSpec` is a base change of the stage.** -/
theorem isPullback_stageMap :
    IsPullback (St.stageMap h) (pullback.snd f (h ≫ hV.fromSpec)) St.f₀
      (h ≫ Spec.map (CommRingCat.ofHom St.φ)) :=
  (isPullback_toChart f hV h).paste_horiz St.isPullback

/-- **The pullback of `E` is the pullback of the model `E₀`.** -/
def stageIso : (Scheme.Modules.pullback (pullback.fst f (h ≫ hV.fromSpec))).obj E ≅
    (Scheme.Modules.pullback (St.stageMap h)).obj St.E₀ :=
  (Scheme.Modules.pullbackCongr (toChart_fst f hV h)).symm.app E ≪≫
    ((Scheme.Modules.pullbackComp (toChart f hV h) (pullback.fst f hV.fromSpec)).app E).symm ≪≫
    (Scheme.Modules.pullback (toChart f hV h)).mapIso St.iso ≪≫
    (Scheme.Modules.pullbackComp (toChart f hV h) St.g).app St.E₀

end NoetherianStage

/-- **A Noetherian stage exists** over every affine open, for a flat proper morphism locally of
finite presentation and a finite locally free module: this is absolute Noetherian approximation,
`AlgebraicGeometry.exists_noetherian_model_of_isProper`, applied to the base change of `f` to
`V` and the restriction of `E`, which is finitely presented and flat over `Γ(S, V)`. -/
theorem nonempty_noetherianStage [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    Nonempty (NoetherianStage f E hV) := by
  let E' := (Scheme.Modules.pullback (pullback.fst f hV.fromSpec)).obj E
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E' :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ E inferInstance
  have : E'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E'
  have hpair : AlgebraicGeometry.SheafOfModules.IsFlat E' ∧ E'.IsFinitePresentation :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae E').out 4 1).mp hE'
  have : E'.IsFinitePresentation := hpair.2
  have hflat : IsFlatOver (pullback.snd f hV.fromSpec).toLRSHom.toShHom E' :=
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ E'
  obtain ⟨A₀, _, _, φ, X₀, f₀, g, E₀, hp, hpb, hc, hfl, ⟨e⟩⟩ :=
    exists_noetherian_model_of_isProper (A := Γ(S, V)) (pullback.snd f hV.fromSpec) E' hflat
  exact ⟨⟨A₀, φ, X₀, f₀, g, E₀, hp, hpb, hc, hfl, e⟩⟩

end AlgebraicGeometry.DescentLocus
