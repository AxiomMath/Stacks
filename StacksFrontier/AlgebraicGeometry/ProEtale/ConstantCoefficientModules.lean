module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingModulesSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantCoefficientsEquivalence

/-!
# Coefficient modules on the pro-étale site are sheaves of `Λ`-modules

Let `X` be a scheme and `Λ` a ring. The objects of `D(X_proét, Λ)` are complexes of sheaves of
modules over the constant coefficient ring sheaf `\underline{Λ}` on `X_proét`. A sheaf of
modules over `\underline{Λ}` is the same thing as a sheaf of `Λ`-modules on `X_proét`: the two
categories are equivalent, through sheafification of the presheaf of modules over the constant
presheaf of rings in one direction and the sheaf of sections, read as `Λ`-modules, in the other.
This lets the statements about sheaves of `Λ`-modules (constructibility, derived tensor products,
change of rings) be applied to the coefficient modules of `D(X_proét, Λ)`.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`: the equivalence between sheaves of
  `Λ`-modules on `X_proét` and sheaves of modules over the constant coefficient ring sheaf.
* `AlgebraicGeometry.ProEtale.overCoefficientModuleEquiv`: the same over an object `V` of
  `X_proét`, for the slice site and the restricted coefficient ring sheaf.

## Main results

* `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquivFunctorIso`: its functor is
  `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor`, which is therefore an
  equivalence.
* `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquivOverIso`: the two equivalences
  commute with restriction to `V`.

## Implementation notes

The constant coefficient ring sheaf is built from the coefficient ring lifted by `ULift` into the
universe of the module sections; the equivalence first restricts scalars along
`ULift.ringEquiv`, which changes nothing, and then applies the library's equivalence
`Stacks.ConstantRingModules.moduleSheafEquivalence` (inverted) to the sheafification map of the
constant presheaf of rings, with its functor replaced, through
`Stacks.ConstantRingModules.moduleSheafEquivalenceInverseIso`, by the isomorphic sheafification
functor `Stacks.ConstantRingModules.sheafificationFunctor`, so that it is sheafification on the
nose. The slice compatibility is `Stacks.ConstantRingModules.sheafificationFunctorOverIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-- **Coefficient modules on `X_proét` are sheaves of `Λ`-modules**: the category of sheaves of
`Λ`-modules on the small pro-étale site is equivalent to the category of sheaves of modules over
the constant coefficient ring sheaf. -/
def constantCoefficientModuleEquiv :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) ≌
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) :=
  letI e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r w}
    (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ))
  letI : (Scheme.ProEt.topology X).HasSheafCompose e.functor :=
    hasSheafCompose_of_preservesLimitsOfSize _
  letI : (Scheme.ProEt.topology X).HasSheafCompose e.inverse :=
    hasSheafCompose_of_preservesLimitsOfSize _
  (Sheaf.coefficientEquivalence (Scheme.ProEt.topology X) e).trans
    ((Stacks.ConstantRingModules.moduleSheafEquivalence.{max (u + 1) r w} _ _
      (constantCoefficientRingMap.{u, r, w} X Λ)).symm.changeFunctor
      (Stacks.ConstantRingModules.moduleSheafEquivalenceInverseIso.{max (u + 1) r w} _ _
        (constantCoefficientRingMap.{u, r, w} X Λ)))

/-- The functor of `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv` is the functor
`AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor` reading a sheaf of
`Λ`-modules over the constant coefficient ring sheaf. -/
def constantCoefficientModuleEquivFunctorIso :
    (constantCoefficientModuleEquiv.{u, r, w} X Λ).functor ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ :=
  NatIso.ofComponents
    (fun _ ↦ (PresheafOfModules.sheafification.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)).mapIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by ext; rfl)))
    (fun {F G} f ↦ by
      let S := PresheafOfModules.sheafification.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)
      change S.map _ ≫ S.map _ = S.map _ ≫ S.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)

/-- **Coefficient modules over an object of `X_proét` are sheaves of `Λ`-modules on the slice
site**: the category of sheaves of `Λ`-modules on `X_proét/V` is equivalent to the category of
sheaves of modules over the restriction to `V` of the constant coefficient ring sheaf. -/
def overCoefficientModuleEquiv (V : X.ProEt) :
    Sheaf ((Scheme.ProEt.topology X).over V) (ModuleCat.{max (u + 1) r w} Λ) ≌
      SheafOfModules.{max (u + 1) r w}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, r, w} X Λ).O)).over V) :=
  letI e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r w}
    (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ))
  letI : ((Scheme.ProEt.topology X).over V).HasSheafCompose e.functor :=
    hasSheafCompose_of_preservesLimitsOfSize _
  letI : ((Scheme.ProEt.topology X).over V).HasSheafCompose e.inverse :=
    hasSheafCompose_of_preservesLimitsOfSize _
  (Sheaf.coefficientEquivalence _ e).trans
    ((Stacks.ConstantRingModules.moduleSheafEquivalence.{max (u + 1) r w} _ _
      (Stacks.ConstantRingModules.overRingMap _ _
        (constantCoefficientRingMap.{u, r, w} X Λ) V)).symm.changeFunctor
      (Stacks.ConstantRingModules.moduleSheafEquivalenceInverseIso.{max (u + 1) r w} _ _
        (Stacks.ConstantRingModules.overRingMap _ _
          (constantCoefficientRingMap.{u, r, w} X Λ) V)))

/-- **The identification of coefficient modules commutes with restriction to an object `V` of
`X_proét`**: a sheaf of `Λ`-modules read over `\underline{Λ}` and restricted to `V` is its
restriction to the slice site read over `\underline{Λ}|_V`. -/
def constantCoefficientModuleEquivOverIso (V : X.ProEt) :
    (constantCoefficientModuleEquiv.{u, r, w} X Λ).functor ⋙
        SheafOfModules.overFunctor.{max (u + 1) r w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, r, w} X Λ).O)) V ≅
      (Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) r w} Λ) V ⋙
        (overCoefficientModuleEquiv.{u, r, w} X Λ V).functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.ConstantRingModules.sheafificationFunctorOverIso.{max (u + 1) r w}
        _ _ (constantCoefficientRingMap.{u, r, w} X Λ) V) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale

end
