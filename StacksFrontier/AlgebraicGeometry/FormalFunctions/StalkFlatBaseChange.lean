module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.QuasiSeparated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for the higher direct images, with unit coefficients

[Stacks, Tag 0GN5] compares `g^* (R ⁱ f_* ℱ) ⊗ 𝒢` with `R ⁱ f'_* ((g')^* ℱ ⊗ (f')^* 𝒢)` for a
cartesian square of schemes and a quasi-coherent `𝒢` on the new base which is flat over the old
one. Taking `𝒢 = 𝒪_{S'}` turns that into flat base change for the higher direct images in every
degree, which is the statement [Stacks, Tag 02KH] part (1) makes for a flat morphism `g`.

This file carries out that specialization. The flatness hypothesis of [Stacks, Tag 0GN5] at the
structure sheaf is flatness of `g` read stalk by stalk,
`AlgebraicGeometry.isFlatOver_unit_of_flat`; what is added here is the pair of unit
isomorphisms removing the two tensor factors.

## Main results

* `Stacks.FormalFunctions.nonempty_pullbackHigherDirectImageIso`: **flat base change for the
  higher direct images in every degree**, `g^* (R ⁱ f_* ℱ) ≅ R ⁱ f'_* ((g')^* ℱ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.FormalFunctions

open Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- The structure sheaf is quasi-coherent, in the spelling [Stacks, Tag 0GN5] is stated in. -/
public instance isQuasicoherent_unit_structureSheafRing (W : Scheme.{u}) :
    (SheafOfModules.unit (structureSheafRing W.toRingedSpace)).IsQuasicoherent :=
  inferInstanceAs (Scheme.unitModule W).IsQuasicoherent

/-- The coefficient functor of [Stacks, Tag 0GN5] at the structure sheaf is the inverse image:
tensoring with the unit does nothing. -/
public def baseCoefficientsUnitIso (g : S' ⟶ S)
    (M : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (baseCoefficients g
        (SheafOfModules.unit (structureSheafRing S'.toRingedSpace))).obj M ≅
      (modulePullback g.toLRSHom.toShHom).obj M :=
  ρ_ ((modulePullback g.toLRSHom.toShHom).obj M)

/-- The coefficient functor upstairs of [Stacks, Tag 0GN5] at the structure sheaf is the
inverse image: the second tensor factor is the structure sheaf of `X'`, and tensoring with the
unit does nothing. -/
public def totalCoefficientsUnitIso (g' : X' ⟶ X) (f' : X' ⟶ S')
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (totalCoefficients g' f'
        (SheafOfModules.unit (structureSheafRing S'.toRingedSpace))).obj F ≅
      (modulePullback g'.toLRSHom.toShHom).obj F :=
  whiskerLeftIso ((modulePullback g'.toLRSHom.toShHom).obj F)
      (modulePullbackUnitIso f'.toLRSHom.toShHom) ≪≫
    ρ_ ((modulePullback g'.toLRSHom.toShHom).obj F)

/-- **Flat base change for the higher direct images, in every degree.** For a cartesian square
of schemes with `f` quasi-compact and quasi-separated and `g` flat, and a quasi-coherent
`𝒪_X`-module `ℱ`,

`g ^* (R ⁱ f_* ℱ) ≅ R ⁱ f'_* ((g') ^* ℱ)`.

This is [Stacks, Tag 0GN5] at `𝒢 = 𝒪_{S'}`, which is flat over `S` precisely because `g` is a
flat morphism; the two tensor factors are removed by the unit isomorphisms above. **No
`@[stacks 02KH]` attribute is attached**: that tag also asserts part (2), the base-change
statement for a quasi-separated `g`, and identifies the comparison with the canonical
base-change map, neither of which is claimed here. -/
@[ega "III 1.4.15" "partial"]
public theorem nonempty_pullbackHigherDirectImageIso (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    Nonempty
      ((Scheme.Modules.pullback g).obj
          (((Scheme.Modules.pushforward f).rightDerived i).obj F) ≅
        ((Scheme.Modules.pushforward f').rightDerived i).obj
          ((Scheme.Modules.pullback g').obj F)) := by
  have : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F :=
    inferInstanceAs F.IsQuasicoherent
  have hG := AlgebraicGeometry.isFlatOver_unit_of_flat g
  have hiso := isIso_degreewiseComparison_app H
    (SheafOfModules.unit (structureSheafRing S'.toRingedSpace)) hG F i
  exact ⟨(baseCoefficientsUnitIso g
      (((modulePushforward f.toLRSHom.toShHom).rightDerived i).obj F)).symm ≪≫
    @asIso _ _ _ _ ((degreewiseComparison H
        (SheafOfModules.unit (structureSheafRing S'.toRingedSpace)) hG i).app F) hiso ≪≫
    ((modulePushforward f'.toLRSHom.toShHom).rightDerived i).mapIso
      (totalCoefficientsUnitIso g' f' F)⟩

end Stacks.FormalFunctions

end
