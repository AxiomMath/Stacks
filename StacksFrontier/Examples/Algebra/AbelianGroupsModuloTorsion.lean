module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.Examples.Algebra.ModulesModuloTorsion

/-!
# Abelian groups modulo torsion groups

The Serre quotient of the category of abelian groups by the torsion abelian groups is canonically
equivalent to the category of rational vector spaces, the equivalence being induced by
rationalization.

This is the localization statement of the previous file for `R = ℤ` and `S` the nonzero integers,
transported along the identification of `ℤ`-module localization at the nonzero integers with
extension of scalars to `ℚ`.

## Main results

* `Stacks.Examples.extendScalarsRat_isLocalization`: rationalization identifies rational vector
  spaces with the Serre quotient of abelian groups by torsion groups.

## Implementation notes

Abelian groups are represented by `ModuleCat ℤ` and rational vector spaces by `ModuleCat ℚ`. A
torsion abelian group is a module in which every element is annihilated by a nonzero integer. The
`IsLocalization` instance states the canonical equivalence with the Serre quotient, including its
compatibility with rationalization.

## References

* [Stacks Project, Tag 0B0M](https://stacks.math.columbia.edu/tag/0B0M)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Examples

open CategoryTheory
open scoped TensorProduct ChangeOfRings

private theorem extendScalarsTensorIso_hom_tmul
    {R : Type u} [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q]
    (M : ModuleCat.{max v u} R) (q : Q) (m : M) :
    (Dualizing.extendScalarsTensorIso Q M).hom (q ⊗ₜ[R, algebraMap R Q] m) = q ⊗ₜ[R] m := rfl

private noncomputable def rationalizationIsoLocalizedModuleFunctor
    {R Q : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
    (S : Submonoid R) [IsLocalization S Q]
    (e : Q ≃ₐ[R] Localization S) :
    ModuleCat.extendScalars.{u, u, max v u} (algebraMap R Q) ≅
      ModuleCat.localizedModuleFunctor.{max v u} S ⋙
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R Q)
  let G := ModuleCat.localizedModuleFunctor.{max v u} S ⋙
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let f := M.localizedModuleMkLinearMap S
    letI : Module Q (M.localizedModule S) := Module.compHom (M.localizedModule S) e.toRingHom
    letI : IsScalarTower R Q (M.localizedModule S) :=
      IsScalarTower.of_algebraMap_smul (fun r x => by
        change e (algebraMap R Q r) • x = r • x
        simpa only [e.commutes] using algebraMap_smul (Localization S) r x)
    exact Dualizing.extendScalarsTensorIso Q M ≪≫
      (IsLocalizedModule.isBaseChange S Q f).equiv.toModuleIso
  · intro M N f
    let fm := M.localizedModuleMkLinearMap S
    let fn := N.localizedModuleMkLinearMap S
    let : Module Q (M.localizedModule S) := Module.compHom (M.localizedModule S) e.toRingHom
    let : Module Q (N.localizedModule S) := Module.compHom (N.localizedModule S) e.toRingHom
    let : IsScalarTower R Q (M.localizedModule S) :=
      IsScalarTower.of_algebraMap_smul (fun r x => by
        change e (algebraMap R Q r) • x = r • x
        simpa only [e.commutes] using algebraMap_smul (Localization S) r x)
    let : IsScalarTower R Q (N.localizedModule S) :=
      IsScalarTower.of_algebraMap_smul (fun r x => by
        change e (algebraMap R Q r) • x = r • x
        simpa only [e.commutes] using algebraMap_smul (Localization S) r x)
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let EM := (IsLocalizedModule.isBaseChange S Q fm).equiv
    let EN := (IsLocalizedModule.isBaseChange S Q fn).equiv
    change EN ((1 : Q) ⊗ₜ[R] (f.hom m)) = (G.map f).hom (EM ((1 : Q) ⊗ₜ[R] m))
    simp only [EM, EN, IsBaseChange.equiv_tmul, one_smul]
    exact (IsLocalizedModule.map_apply S fm fn f.hom m).symm

/-- Rationalization presents rational vector spaces as the Serre quotient of abelian groups by
torsion groups. -/
@[stacks 0B0M]
public instance extendScalarsRat_isLocalization :
    (ModuleCat.extendScalars (algebraMap ℤ ℚ) :
      ModuleCat.{v} ℤ ⥤ ModuleCat.{v} ℚ).IsLocalization
      (localizationTorsionModuleProperty (R := ℤ)
        (nonZeroDivisors ℤ) : ObjectProperty (ModuleCat.{v} ℤ)).isoModSerre := by
  let S : Submonoid ℤ := nonZeroDivisors ℤ
  let e : ℚ ≃ₐ[ℤ] Localization S := IsLocalization.algEquiv S ℚ (Localization S)
  let : (ModuleCat.localizedModuleFunctor.{v} S).IsLocalization
      (localizationTorsionModuleProperty (R := ℤ) S :
        ObjectProperty (ModuleCat.{v} ℤ)).isoModSerre :=
    localizedModuleFunctor_isLocalization.{0, v} (R := ℤ) S
  exact Functor.IsLocalization.of_equivalence_target
    (ModuleCat.localizedModuleFunctor.{v} S)
    (localizationTorsionModuleProperty (R := ℤ) S :
      ObjectProperty (ModuleCat.{v} ℤ)).isoModSerre
    (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ ℚ))
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv)
    (rationalizationIsoLocalizedModuleFunctor.{0, v} (R := ℤ) (Q := ℚ) S e).symm

end Stacks.Examples

end
