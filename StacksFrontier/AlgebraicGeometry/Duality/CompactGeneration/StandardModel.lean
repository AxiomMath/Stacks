module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The coherator and the twisted inverse image at the standard model

The derived category of `𝒪_X`-modules is used at two models in this library: the locally small
one, `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which [Stacks, Tag 0CR0] and
[Stacks, Tag 0A9E] are proved (Brown representability needs direct sums indexed by the morphism
universe), and `CategoryTheory.HasDerivedCategory.standard`, at which the relative cup product
and the trace maps of the duality chapter are built. This file carries the two adjoints across.

For a quasi-compact quasi-separated scheme `X` the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right
adjoint at the standard model, and for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated
schemes the functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint at the standard model.

## Main results

* `Stacks.Duality.StandardModel.isLeftAdjoint_of_comp_iso` — a functor conjugate by equivalences
  to a left adjoint is a left adjoint.
* `Stacks.Duality.StandardModel.isLeftAdjoint_quasiCoherentι` — [Stacks, Tag 0CR0] at the
  standard model.
* `Stacks.Duality.StandardModel.isLeftAdjoint_quasiCoherentDerivedPushforward` — [Stacks,
  Tag 0A9E] at the standard model.

## Implementation notes

The comparison of the two ambient derived categories is `StacksDraft.DerivedModel.modelEquiv`,
it restricts to the quasi-coherent parts by
`StacksDraft.DerivedModel.derivedCategoryBModelEquiv`, and the two derived direct images agree
across it by `StacksDraft.DerivedModel.rightDerivedModelIso`, both being total right derived
functors of the same functor. Every `HasDerivedCategory` instance is named explicitly, as the
implementation notes of `StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`
ask.

## References

* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality.StandardModel

/-- **A functor conjugate to a left adjoint by equivalences is a left adjoint.** If
`G ⋙ H ≅ F ⋙ G'` with `F` and `H` equivalences and `G'` a left adjoint, then `G` is a left
adjoint. -/
theorem isLeftAdjoint_of_comp_iso {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B'] {G : A ⥤ B} {G' : A' ⥤ B'} {F : A ⥤ A'} {H : B ⥤ B'} [F.IsEquivalence]
    [H.IsEquivalence] [G'.IsLeftAdjoint] (e : G ⋙ H ≅ F ⋙ G') : G.IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm H.inv ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G H.asEquivalence.unitIso.symm ≪≫
      G.rightUnitor)

variable (X : Scheme.{u})

/-- `D_QCoh(𝒪_X)` at the standard model is equivalent to `D_QCoh(𝒪_X)` at the locally small
model, by the restriction of the comparison of the two ambient derived categories. -/
abbrev quasiCoherentModelEquiv :
    @quasiCoherentDerivedCategory X (HasDerivedCategory.standard X.Modules) ≌
      quasiCoherentDerivedCategory X :=
  StacksDraft.DerivedModel.derivedCategoryBModelEquiv
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) (HasDerivedCategory.standard X.Modules)
    (Scheme.Modules.hasDerivedCategory X)

/-- **[Stacks, Tag 0CR0] at the standard model.** For a quasi-compact quasi-separated scheme `X`
the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` of the standard model has a right adjoint: it is conjugate,
by the comparison equivalences, to the inclusion at the locally small model, which has one by
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`. -/
instance isLeftAdjoint_quasiCoherentι [CompactSpace X] [QuasiSeparatedSpace X] :
    (@DerivedCategoryB.derivedCategoryB X.Modules _ _ (HasDerivedCategory.standard X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.IsLeftAdjoint := by
  have := Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι X
  exact isLeftAdjoint_of_comp_iso (F := (quasiCoherentModelEquiv X).functor)
    (H := (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard X.Modules)
      (Scheme.Modules.hasDerivedCategory X)).functor)
    (G' := Stacks.Duality.Coherator.quasiCoherentι X) (Iso.refl _)

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The derived direct image read at the two models.** `Rf_*` at the standard model followed
by the comparison of `D(𝒪_Y)` is `Rf_*` at the locally small model preceded by the comparison
of `D(𝒪_X)`: both are total right derived functors of degreewise direct image. -/
def derivedPushforwardModelIso :
    @derivedPushforward X Y f (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard Y.Modules) ⋙
      (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard Y.Modules)
        (Scheme.Modules.hasDerivedCategory Y)).functor ≅
    (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X)).functor ⋙ derivedPushforward f :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (Functor.totalRightDerivedUnit
      (@homotopyPushforward X Y f (HasDerivedCategory.standard Y.Modules))
      (@DerivedCategory.Qh X.Modules _ _ (HasDerivedCategory.standard X.Modules))
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (Functor.totalRightDerivedUnit (homotopyPushforward f) DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (Localization.compUniqFunctor _ _ _)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _))

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Part (1) of [Stacks, Tag 08D5] at the standard model**: for a morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes, `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. This is
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`, which is
stated at an arbitrary model. -/
theorem isQuasicoherent_homology_derivedPushforward (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
    f K.obj K.2 i

/-- **[Stacks, Tag 0A9E] at the standard model.** For a morphism `f : X ⟶ Y` of quasi-compact
quasi-separated schemes, `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` at the standard model has a right
adjoint: it is conjugate, by the comparison equivalences, to `Rf_*` at the locally small model,
which has one by
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward :
    (quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward f)).IsLeftAdjoint := by
  have :=
    Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs f
  exact isLeftAdjoint_of_comp_iso (F := (quasiCoherentModelEquiv X).functor)
    (H := (quasiCoherentModelEquiv Y).functor)
    (G' := Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward f)
    (((fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (ι _) (derivedPushforwardModelIso f)))

end Standard

end Stacks.Duality.StandardModel

end
