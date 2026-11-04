module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.DerivedSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The splitting of `Rf_*𝒪_X` survives base change

Let `f : X ⟶ S` be proper, flat and of finite presentation and suppose that
`Rf_*𝒪_X ≅ X₁ ⊕ P` in `D(𝒪_S)` with `X₁` of Tor amplitude in `[0, 0]` and `P` perfect of Tor
amplitude in `[1, b]`. For every cartesian square with base `g : S' ⟶ S`, the same holds for the
base change `f' : X' ⟶ S'`: cohomology and base change ([Stacks, Tag 0B91]) gives
`Lg^*Rf_*𝒪_X ≅ Rf'_*𝒪_{X'}`, derived pullback is additive, preserves perfectness
([Stacks, Tag 09UA]) and Tor amplitude ([Stacks, Tag 09U8]).

All derived categories are at the standard model, named explicitly.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **The splitting of `Rf_*𝒪_X` survives base change.** -/
theorem exists_splitting_of_isPullback {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g) (hfp : FinitePresentation f)
    [IsProper f] [Flat f] (b : ℤ) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard S.Modules
    letI := HasDerivedCategory.standard X'.Modules
    letI := HasDerivedCategory.standard S'.Modules
    (∃ X₁ P : DerivedCategory S.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f
          (Scheme.unitModule X) ≅ X₁ ⊞ P) ∧
      HasTorAmplitudeStd S X₁ 0 0 ∧ Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧
      HasTorAmplitudeStd S P 1 b) →
    ∃ X₁ P : DerivedCategory S'.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f'
          (Scheme.unitModule X') ≅ X₁ ⊞ P) ∧
      HasTorAmplitudeStd S' X₁ 0 0 ∧ Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧
      HasTorAmplitudeStd S' P 1 b := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard S.Modules
  let := HasDerivedCategory.standard X'.Modules
  let := HasDerivedCategory.standard S'.Modules
  rintro ⟨X₁, P, ⟨e⟩, h₁, hP, hPb⟩
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S'.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace))
  have : (Scheme.unitModule X).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have hflat : IsFlatOver f.toLRSHom.toShHom (Scheme.unitModule X) := fun x =>
    (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit f x).1
      (Flat.stalkMap f x)
  obtain ⟨ebc⟩ := ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward f g f' g' hsq hfp
    ‹_› (Scheme.unitModule X) ‹_› hflat
  let L₀ := derivedPullback g.toLRSHom.toShHom
  let L : DerivedCategory S.Modules ⥤ DerivedCategory S'.Modules := L₀
  have : L.Additive := (inferInstance : L₀.Additive)
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBiproducts _
  let eU : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f'
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ≅
      ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f' (Scheme.unitModule X') :=
    (derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor X'.Modules 0).mapIso (Scheme.Modules.pullbackUnitIso g'))
  have hT := Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
    g.toLRSHom.toShHom
  exact ⟨L.obj X₁, L.obj P, ⟨eU.symm ≪≫ ebc.symm ≪≫ L.mapIso e ≪≫ L.mapBiprod _ _⟩,
    hT _ _ _ h₁, RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ P hP,
    hT _ _ _ hPb⟩

end StacksDraft.Perfect.GeomReducedFibre

end
