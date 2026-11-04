module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# `Q(f_*C^•) ⟶ Rf_*(QC^•)` is invertible along an affine morphism

Let `f : X ⟶ Y` be an affine morphism of schemes and let `C^•` be a cochain complex of
quasi-coherent `𝒪_X`-modules, with no boundedness hypothesis.  The comparison

`Q(f_*C^•) ⟶ Rf_*(QC^•)`

of `Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ` is an
isomorphism: the termwise direct image of `C^•` already computes the derived direct image.

This is the affine counterpart of
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ`, and
its proof is that one with a single input exchanged.  `pushforwardComparisonQ` is the unit
`f_* ⟶ Rf_*` of the derived functor with the two comparisons between `Q` and `Qh ∘ quotient`
inserted at either end; those comparisons are isomorphisms unconditionally, so only the unit is
at issue, and it is invertible by [Stacks, Tag 0G9N] for an affine morphism, which is
`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom`.

## Main results

* `AlgebraicGeometry.isIso_pushforwardComparisonQ_of_isAffineHom`: the statement above.

## Implementation notes

*Three spellings of the category of `𝒪_X`-modules meet here, and all of them by `rfl`.*
`pushforwardComparisonQ` is stated at
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`, the spelling the tensor product
of sheaves of modules forces; the derived pushforward unit of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` is stated at
`SheafOfModules (structureSheafRing X)`; and the affine invertibility statement is stated at
`SheafOfModules X.ringCatSheaf`, the spelling the quasi-coherent subcategory uses.  The three are
the same category and elaboration crosses them with no cast, exactly as the documentation of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/StructureSheafAsADerivedUnit.lean` records.

*`HasDerivedCategory.standard` is installed at priority `10000`*, not at the default.  The
locally small models of `StacksFrontier.Homology.DerivedCategory.LocallySmall` are global instances
and beat a default-priority local attribute; with the default priority the `have`s below are
elaborated at the locally small model while the goal, whose statement bakes in the model that
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/CupProductAndDerivedPushforward.lean`
installs, is at the standard one, and the two do not unify.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`Q(f_*C^•) ⟶ Rf_*(QC^•)` is invertible along an affine morphism of schemes**, for a
cochain complex `C^•` of quasi-coherent `𝒪_X`-modules and with no boundedness hypothesis.

The comparison is the unit of the derived direct image with the two comparisons between `Q` and
`Qh ∘ quotient` inserted at either end.  Those are isomorphisms for every morphism, and the unit
is invertible at a complex of quasi-coherent modules along an affine morphism by
[Stacks, Tag 0G9N], `AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom`.

This is the input that the source's proof of [Stacks, Tag 0B55] gets from [Stacks, Tag 08KS] for
a closed embedding, and it is what the affine case of [Stacks, Tag 08I9] needs in its place. -/
@[stacks 0G9N "the comparison Q(f_*C) ⟶ Rf_*(QC) at the Q spelling: it is invertible for an \
affine morphism of schemes and a complex of quasi-coherent modules, with no boundedness \
hypothesis"]
theorem isIso_pushforwardComparisonQ_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (C : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hqc : ∀ n : ℤ, (C.X n : SheafOfModules.{u} X.ringCatSheaf).IsQuasicoherent) :
    IsIso (pushforwardComparisonQ f.toLRSHom.toShHom C) := by
  have h₁ : IsIso (((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y.toRingedSpace)).app
        ((pushforwardComplex f.toLRSHom.toShHom).obj C)).inv) := inferInstance
  have h₂ : IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj C)) :=
    AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom f C hqc
  have h₃ : IsIso ((derivedPushforward f.toLRSHom.toShHom).map
      (((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)).app
          C).hom)) :=
    ((derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)).app
          C)).isIso_hom
  dsimp only [pushforwardComparisonQ]
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)

end AlgebraicGeometry

end
