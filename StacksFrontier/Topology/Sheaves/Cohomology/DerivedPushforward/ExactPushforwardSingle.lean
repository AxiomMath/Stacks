module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

/-!
# The derived pushforward of a sheaf along an exact direct image

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces along which the direct image
`f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is exact. Then a module placed in degree `0` has no higher direct
images: `(f_* F)[0] ≅ Rf_*(F[0])`, naturally in `F`. The results hold for arbitrary models of the
two derived categories.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso`:
  the natural isomorphism `f_* ⋙ (-)[0] ≅ (-)[0] ⋙ Rf_*`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit`:
  for an exact `f_*` the comparison `f_* ⟶ Rf_*` out of the homotopy category is invertible
  everywhere.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso_hom_app`:
  the value of the isomorphism at a module, as the comparison at the complex `F[0]`.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe w₁ w₂ u

noncomputable section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
  [PreservesFiniteColimits (modulePushforward f)]

/-- For a morphism of ringed spaces along which `f_*` is exact, the comparison `f_* ⟶ Rf_*` out of
the homotopy category is invertible. -/
instance isIso_derivedPushforwardUnit : IsIso (derivedPushforwardUnit f) := by
  have h : ∀ M, IsIso ((derivedPushforwardUnit f).app M) := fun M => by
    rw [← Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app
      (modulePushforward f) M]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **`(f_* F)[0] ≅ Rf_*(F[0])` for an exact direct image**, naturally in the module `F`.

It is the comparison `derivedPushforwardUnit f` at the complex `F[0]` of the homotopy category,
read through the commutation of `f_*` with `(-)[0]` on homotopy categories and the identification
of the single functor of the derived category with that of the homotopy category followed by `Qh`.
-/
def derivedPushforwardSingleIso :
    modulePushforward f ⋙ DerivedCategory.singleFunctor _ 0 ≅
      DerivedCategory.singleFunctor _ 0 ⋙ derivedPushforward f :=
  Functor.isoWhiskerLeft (modulePushforward f)
      (DerivedCategory.singleFunctorIsoCompQh _ 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.singleFunctor _ 0)
      (asIso (derivedPushforwardUnit f)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh _ 0).symm
      (derivedPushforward f)

/-- The value of `derivedPushforwardSingleIso` at a module `F`: the comparison
`f_* ⟶ Rf_*` at the complex `F[0]`, between the two identifications of the single functor of the
derived category with that of the homotopy category followed by `Qh`. -/
theorem derivedPushforwardSingleIso_hom_app (F : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedPushforwardSingleIso f).hom.app F =
      (DerivedCategory.singleFunctorIsoCompQh _ 0).hom.app ((modulePushforward f).obj F) ≫
        DerivedCategory.Qh.map
          (((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0).inv.app F) ≫
        (derivedPushforwardUnit f).app ((HomotopyCategory.singleFunctor _ 0).obj F) ≫
        (derivedPushforward f).map ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app F) := by
  simp [derivedPushforwardSingleIso]

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
