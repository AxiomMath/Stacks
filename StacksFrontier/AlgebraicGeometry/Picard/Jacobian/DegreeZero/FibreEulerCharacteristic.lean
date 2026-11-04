module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.DerivedPushforwardToField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleFamily
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of the fibres of a proper flat family is locally constant

Let `f : X ⟶ S` be a proper morphism of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation, flat over `S`. The function `s ↦ χ(X_s, ℱ_s)` on `S`, the Euler characteristic of
the restriction of `ℱ` to the scheme-theoretic fibre `X_s = X ×_S Spec κ(s)`, is locally constant,
and its formation commutes with base change ([Stacks, Tag 0B9T]).

The proof is the source's. By [Stacks, Tag 0B91] (from [Stacks, Tag 0A1H], in
`Perfect/ProperFlatPushforwardPerfectBaseChange.lean`) the object `Rf_*ℱ` is perfect
and `Li_s^*Rf_*ℱ ≅ R(f_s)_*ℱ_s`, so `χ(X_s, ℱ_s)` is the derived-fibre Euler characteristic of
`Rf_*ℱ` at `s` (`AlgebraicGeometry.eulerCharacteristic_eq_finsum_homology_derivedPushforward`),
which is locally constant by [Stacks, Tag 0BDJ].

The declarations use
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`
directly. Nothing here is registered against Tag 0B9T.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreCoherentEulerCharacteristic`: the
  function `s ↦ χ(X_s, ℱ_s)`, read through `AlgebraicGeometry.eulerCharacteristic` of the coherent
  fibre module (the base's `fibreEulerCharacteristic` is the same function as a finite sum over
  `cohomologyOverField`, with no properness or coherence binder).

## Main results

* `fibreCoherentEulerCharacteristic_eq_chiDerivedFibre`: `χ(X_s, ℱ_s)` is the derived-fibre Euler
  characteristic of `Rf_*ℱ`.
* `isLocallyConstant_fibreCoherentEulerCharacteristic_and_baseChange`: the function
  `s ↦ χ(X_s, ℱ_s)` is locally constant and commutes with base change.

## References

* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isFinitePresentation)

/-- **The function `s ↦ χ(X_s, ℱ_s)`** of [Stacks, Tag 0B9T], for a proper morphism `f` and an
`𝒪_X`-module `ℱ` of finite presentation: the Euler characteristic
(`AlgebraicGeometry.eulerCharacteristic`, [Stacks, Tag 0BEJ]) of the restriction `ℱ_s` of `ℱ`
to the scheme-theoretic fibre `X_s = X ×_S Spec κ(s)`, which is proper over `κ(s)`. -/
def fibreCoherentEulerCharacteristic {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (F : X.Modules)
    [F.IsFinitePresentation] : S → ℤ :=
  fun s => @eulerCharacteristic (S.residueField s) _ (f.fiber s) (f.fiberToSpecResidueField s)
    (inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField s))))
    ((Scheme.Modules.pullback (f.fiberι s)).obj F)
    (have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
        F inferInstance).1
      have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
        F inferInstance).2
      Stacks.Chow.fiberModule_isCoherent f F s)

/-- The Euler characteristic of a coherent module `M` on a scheme proper over `κ(s)` is the
derived-fibre Euler characteristic of `E` at `s`, given `Li_s^*E ≅ Rq_*M`. -/
private theorem eulerCharacteristic_eq_chiDerivedFibre_of_iso {S : Scheme.{u}} (s : S)
    (E : DerivedCategory S.Modules) (hE : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) E)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (S.residueField s)) [IsProper q] (M : Y.Modules)
    [M.IsCoherent]
    (e : (derivedPullback (S.fromSpecResidueField s).toLRSHom.toShHom).obj E ≅
      derivedPushforwardModule q M) :
    eulerCharacteristic (S.residueField s) q M = DerivedFibreBetti.chiDerivedFibre S E hE s := by
  refine (eulerCharacteristic_eq_finsum_homology_derivedPushforward (S.residueField s)
    q M).trans ?_
  refine finsum_congr fun i => congrArg (fun n : ℕ => (i.negOnePow : ℤ) * (n : ℤ)) ?_
  exact ((moduleSpecΓFunctor (R := S.residueField s)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (S.residueField s)).Modules i).mapIso
      e)).toLinearEquiv.finrank_eq.symm

/-- **`χ(X_s, ℱ_s)` is the derived-fibre Euler characteristic of `Rf_*ℱ`**.
This is the first step of the source proof of [Stacks, Tag 0B9T]:
the base change of [Stacks, Tag 0B91] to `Spec κ(s) ⟶ S` identifies `Li_s^*Rf_*ℱ` with
`R(f_s)_*ℱ_s`, and the cohomology of the latter is that of `ℱ_s`
(`AlgebraicGeometry.eulerCharacteristic_eq_finsum_homology_derivedPushforward`). -/
theorem fibreCoherentEulerCharacteristic_eq_chiDerivedFibre
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (hf : FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hpc : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (derivedPushforwardModule f F)) :
    fibreCoherentEulerCharacteristic f F =
      DerivedFibreBetti.chiDerivedFibre S (derivedPushforwardModule f F) hpc := by
  funext s
  have : IsProper (f.fiberToSpecResidueField s) :=
    inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField s)))
  have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
    F inferInstance).1
  have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
    F inferInstance).2
  obtain ⟨e⟩ := ProperFlatBaseChange.nonempty_derivedPullback_derivedPushforward_module_iso
    f (S.fromSpecResidueField s) (f.fiberToSpecResidueField s) (f.fiberι s)
    (IsPullback.of_hasPullback _ _) hf inferInstance F inferInstance hflat
  exact eulerCharacteristic_eq_chiDerivedFibre_of_iso s _ hpc _ _ e

/-- **[Stacks, Tag 0B9T].** Let `f : X ⟶ S` be
a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation,
flat over `S`. The function `s ↦ χ(X_s, ℱ_s)` is locally constant on `S`, and its formation
commutes with base change: for every `g : S' ⟶ S`, the function attached to the base change
`X ×_S S' ⟶ S'` and the pullback of `ℱ` is the function attached to `f` and `ℱ`, composed with
`g`.

Here `χ(X_s, ℱ_s)` is `AlgebraicGeometry.eulerCharacteristic` ([Stacks, Tag 0BEJ]) of the
restriction of `ℱ` to the scheme-theoretic fibre `X_s ⟶ Spec κ(s)`
(`fibreCoherentEulerCharacteristic`). The proof is the source's: by
`fibreCoherentEulerCharacteristic_eq_chiDerivedFibre` the function is the derived-fibre Euler
characteristic of `Rf_*ℱ`, which is perfect, and that is locally constant by
[Stacks, Tag 0BDJ]; base change is the base-change clause of [Stacks, Tag 0BDI] summed over the
degrees, together with the base change of [Stacks, Tag 0B91] along `Spec κ(s') ⟶ S' ⟶ S`. -/
@[ega "III 7.9.5" "special case", ega "III 7.9.7" "special case", sga "7 X 2.29" "more general"]
theorem isLocallyConstant_fibreCoherentEulerCharacteristic_and_baseChange
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (hf : FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsLocallyConstant (fibreCoherentEulerCharacteristic f F) ∧
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
        @fibreCoherentEulerCharacteristic _ _ (pullback.snd f g) _
            ((Scheme.Modules.pullback (pullback.fst f g)).obj F)
            (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ F) =
          fibreCoherentEulerCharacteristic f F ∘ g.base := by
  have hperf := ProperFlatBaseChange.isPerfect_derivedPushforward_module f hf
    inferInstance F inferInstance hflat
  have hpc : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (derivedPushforwardModule f F) :=
    DerivedFibreBetti.isPseudoCoherent_of_isPerfect _ hperf
  have hid := fibreCoherentEulerCharacteristic_eq_chiDerivedFibre f hf F hflat hpc
  refine ⟨hid ▸ DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _ hperf, fun {S'} g => ?_⟩
  rw [hid, ← DerivedFibreBetti.chiDerivedFibre_derivedPullback g _ hpc]
  funext s'
  have : IsProper ((pullback.snd f g).fiberToSpecResidueField s') :=
    inferInstanceAs (IsProper (pullback.snd (pullback.snd f g) (S'.fromSpecResidueField s')))
  have : ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ F
  have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F) inferInstance).1
  have := (isQuasicoherent_isFiniteType_of_isFinitePresentation
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F) inferInstance).2
  let t := S'.fromSpecResidueField s' ≫ g
  have hsq : IsPullback ((pullback.snd f g).fiberι s' ≫ pullback.fst f g)
      ((pullback.snd f g).fiberToSpecResidueField s') f t :=
    (IsPullback.of_hasPullback (pullback.snd f g) (S'.fromSpecResidueField s')).paste_horiz
      (IsPullback.of_hasPullback f g)
  obtain ⟨e⟩ := ProperFlatBaseChange.nonempty_derivedPullback_derivedPushforward_module_iso
    f t _ _ hsq hf inferInstance F inferInstance hflat
  let e' : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (S'.fromSpecResidueField s').toLRSHom.toShHom).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
        (derivedPushforwardModule f F)) ≅
      derivedPushforwardModule ((pullback.snd f g).fiberToSpecResidueField s')
        ((Scheme.Modules.pullback ((pullback.snd f g).fiberι s')).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) :=
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (S'.fromSpecResidueField s').toLRSHom.toShHom g.toLRSHom.toShHom).app _ ≪≫ e ≪≫
      (derivedPushforward ((pullback.snd f g).fiberToSpecResidueField s').toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((Scheme.Modules.pullbackComp _ _).app F).symm)
  exact eulerCharacteristic_eq_chiDerivedFibre_of_iso s' _ _ _ _ e'

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
