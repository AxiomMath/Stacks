module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite

/-!
# Coherence of the higher direct images along a proper morphism, with nothing carried

Let `S` be a scheme and `f : X ⟶ Y` a proper morphism of algebraic spaces over `S` with `Y`
locally Noetherian.  Stacks 08AR asserts that for a coherent `𝒪_X`-module `𝓕` every higher
direct image `R^i f_*𝓕` is a coherent `𝒪_Y`-module.
`AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_isProper_of_devissage` is a
reduction of it to three results of other tags, given as hypotheses; this file proves it with
none.

The proof is the source's.  Quasi-coherence of `R^i f_*𝓕` is Stacks 0720
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`), and on a
locally Noetherian algebraic space a quasi-coherent module is coherent as soon as its sections
over every affine étale chart are finite over the functions on that chart (Stacks 07UB).  Over an
affine chart `V` of `Y` those sections are, by étale base change (Stacks 03LX) and the
degeneration of the Leray spectral sequence over an affine base (Stacks 08EX), the cohomology of
the restriction of `𝓕` along the base change `f_V : X_V ⟶ V`, which is proper over an affine
Noetherian scheme; that cohomology is finite by the dévissage of Stacks 08AN with the Chow-lemma
witness, `AlgebraicGeometry.Space.hasFiniteCohomologyOver_of_isProper`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_isProper`: **Stacks 08AR**.

## Implementation notes

**The module universe** is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_properCoherence
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- **Stacks 08AR.**  Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y`
locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.  Then `R^i f_*𝓕` is a coherent
`𝒪_Y`-module for every `i`.

`R^i f_*𝓕` is quasi-coherent by Stacks 0720, so by Stacks 07UB it suffices that its sections over
every affine étale chart `V` of `Y` are finite over `𝒪_Y(V)`.  Those sections are the sections
over the identity chart of the restriction of `R^i f_*𝓕` to `V`, which is
`R^i f'_*(𝓕|_U)` for the base change `f' : U = V ×_Y X ⟶ V` by Stacks 03LX; over the affine
scheme `V` this is `R^i Γ(V, f'_* −)(𝓕|_U)`, the higher direct images of `f'` being
quasi-coherent and hence acyclic over the affine `V` (Stacks 0720 and 03DW, degenerating the
Leray spectral sequence).  The base change `f'` is proper (Stacks 0EPD) and `𝓕|_U` is coherent,
so `AlgebraicGeometry.Space.hasFiniteCohomologyOver_of_isProper` applies. -/
@[stacks 08AR, ega "III 3.2.1" "more general"]
theorem isCoherent_higherDirectImage_of_isProper {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived i).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  have hfqs := isQuasiSeparated_of_isSeparated B S hS hf.1
  refine isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS Y.1 Y.2 hY _
    (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f hf.2.1.2 hfqs F i)
    (fun V hV ↦ ?_)
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj V)) := isLocallyNoetherian_chart B S hS hY V
  have hV' : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj V)) := hV
  have hf' : IsProper B S hS (chartBaseChangeProjection B S hS f V).hom :=
    isProper_of_isPullback B S hS (chartBaseChangeSpace B S hS f V).2 X.2
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V)) Y.2
      (isPullback_chartBaseChangeProjection B S hS f V).flip hf
  have hX' : HasEtaleLocalProperty B S hS (chartBaseChangeSpace B S hS f V).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (chartBaseChangeSpace B S hS f V).2
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
      (chartBaseChangeProjection B S hS f V).hom hf'.2.1.1
      (hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _) inferInstance)
  have : Fact (HasEtaleLocalProperty B S hS (chartBaseChangeSpace B S hS f V).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hX'⟩
  have hG : IsCoherent B S hS _ _ ((chartBaseChangeModulePullback B S hS f V).obj F) :=
    isCoherent_of_iso B S hS _
      ((modulePullbackIsoEtaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
        (isEtale_chartBaseChangeInclusion B S hS f V)).app F)
      (isCoherent_modulePullback B S hS (chartBaseChangeInclusion B S hS f V) F hF)
  have : ((chartBaseChangeModulePullback B S hS f V).obj F).IsQuasicoherentOnSite :=
    hG.toIsQuasicoherentOnSite
  have hfin := hasFiniteCohomologyOver_of_isProper B S hS ((SmallEtale.toOver B S hS Y.1).obj V)
    hV' (chartBaseChangeProjection B S hS f V) hf'
    ((chartBaseChangeModulePullback B S hS f V).obj F) hG i
  have e₁ := evaluationRightDerivedIso B S hS
    (isTerminalIdEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
    (chartBaseChangeProjection B S hS f V) ((chartBaseChangeModulePullback B S hS f V).obj F)
    (fun q n hn ↦ isZero_rightDerived_evaluation_of_isAffineChart B S hS _ _ _
      (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS
        (chartBaseChangeProjection B S hS f V) hf'.2.1.2
        (isQuasiSeparated_of_isSeparated B S hS hf'.1) _ q)
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)) hV' n hn) i
  have e₂ := (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V))).O)
      (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))).mapIso
    ((moduleHigherPushforwardEtaleBaseChangeIso B S hS (chartBaseChangeInclusion B S hS f V)
      (chartBaseChangeProjection B S hS f V) f (chartToSpace B S hS Y V)
      (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V) i).app F)
  have := modulePushforward_additive B S hS
    (Y := (⟨yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V),
      isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V)⟩ :
        AlgebraicSpaces B S hS))
    (chartBaseChangeProjection B S hS f V)
  have : (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V))).O)
      (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))).Additive :=
    ⟨fun {_ _ _ _} ↦ rfl⟩
  have e : ((modulePushforward B S hS
      (Y := (⟨yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V),
        isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V)⟩ :
          AlgebraicSpaces B S hS))
      (chartBaseChangeProjection B S hS f V) ⋙
      SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))
            (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V))).O)
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))).rightDerived i).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F) ≅
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))
            (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V))).O)
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
            (isEtale_chartToSpace B S hS Y V)).obj
          (((modulePushforward B S hS f).rightDerived i).obj F)) := e₁ ≪≫ e₂
  exact (Module.Finite.equiv_iff e.toLinearEquiv).1 hfin

end AlgebraicGeometry.Space

end
