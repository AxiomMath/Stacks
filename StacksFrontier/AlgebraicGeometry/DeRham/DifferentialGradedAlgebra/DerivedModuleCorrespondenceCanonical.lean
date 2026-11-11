module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence

/-!
# The canonical identification of de Rham classes with derived module maps

The structure `AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence` packages, for
the relative de Rham complex `Ω^•`, a forgetful map from morphisms `Ω^• ⟶ Ω^•[n]` of the derived
category `D(Ω^•, d)` of right differential graded `Ω^•`-modules to morphisms of `D(A)`, an
identification `H^n_{dR} ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])`, and an evaluation at the unit, inverse to
each other. This file constructs the canonical term of it from Differential Graded Sheaves,
Section 0FU3 as proved in
`StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence`:
the forgetful map is `AlgebraicGeometry.SheafOfModules.deRhamForgetHom`, the identification is
`AlgebraicGeometry.SheafOfModules.deRhamClassDerivedEquiv` and the evaluation at the unit is the
literal one, `AlgebraicGeometry.SheafOfModules.deRhamEvalOne`. For it, the morphism
`AlgebraicGeometry.SheafOfModules.deRhamClassDerivedMorphism` is the morphism
`AlgebraicGeometry.SheafOfModules.deRhamClassMorphism` of Remark 0FU7.

The two spellings of `Ω^•[n]` in `D(Ω^•, d)` — the image of the translate in the homotopy category,
and the translate of the image — are identified by the commutation of the localization functor
with the translations.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamDerivedRegularShiftIso`: the two spellings of `Ω^•[n]`.
* `AlgebraicGeometry.SheafOfModules.deRhamDerivedModuleCorrespondence`: **the canonical
  identification of Section 0FU3 for the relative de Rham complex.**

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamClassDerivedMorphism_deRhamDerivedModuleCorrespondence`:
  for the canonical identification, `deRhamClassDerivedMorphism` is `deRhamClassMorphism`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The commutation of the localization functor `K(A) ⥤ D(A, d)` with the translations, named so
that it can be supplied for a sheaf of differential graded algebras whose ringed site is not found
by unification. -/
noncomputable abbrev toDerivedCategoryCommShift {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (toDerivedCategory.{u, u, u} A).CommShift ℤ :=
  inferInstance

end SheafOfModules.DifferentialGradedModule

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The commutation of the localization functor `K(Ω^•) ⥤ D(Ω^•, d)` with the translations. -/
noncomputable instance deRhamToDerivedCategoryCommShift :
    (_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u}
      (deRhamDifferentialGradedAlgebra B D)).CommShift ℤ :=
  _root_.SheafOfModules.DifferentialGradedModule.toDerivedCategoryCommShift (X := baseSite A)
    (deRhamDifferentialGradedAlgebra B D)

/-- The image in `D(Ω^•, d)` of the translate `Ω^•[n]` of the regular module, computed in the
homotopy category, is the translate of the image of `Ω^•`. -/
noncomputable def deRhamDerivedRegularShiftIso (n : ℤ) :
    deRhamDerivedRegularShift B D n ≅ (deRhamDerivedRegular B D)⟦n⟧ :=
  ((_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u}
    (deRhamDifferentialGradedAlgebra B D)).commShiftIso n).app
      ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj
        (deRhamRegularModule B D))

/-- **The identification of Differential Graded Sheaves, Section 0FU3, for the relative de Rham
complex**, as a term of `DeRhamDerivedModuleCorrespondence`: forgetting the differential graded
structure is `deRhamForgetHom`, the identification `H^n_{dR} ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])` is
`deRhamClassDerivedEquiv`, and the evaluation at the unit is `deRhamEvalOne`. -/
noncomputable def deRhamDerivedModuleCorrespondence : DeRhamDerivedModuleCorrespondence B D where
  forget n g := deRhamForgetHom B D n (g ≫ (deRhamDerivedRegularShiftIso B D n).hom)
  classEquiv n := (deRhamClassDerivedEquiv B D n).trans
    ((Iso.refl _).homCongr (deRhamDerivedRegularShiftIso B D n).symm)
  evalOne n := deRhamEvalOne B D n
  evalOne_forget_classEquiv n ξ := by
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact deRhamEvalOne_deRhamClassMorphism B D n ξ

/-- For the canonical identification of Section 0FU3, the morphism attached to a relative de Rham
class `ξ` by `deRhamClassDerivedMorphism` is the morphism `ξ'` of Remark 0FU7. -/
theorem deRhamClassDerivedMorphism_deRhamDerivedModuleCorrespondence (n : ℤ)
    (ξ : deRhamCohomology B D n) :
    deRhamClassDerivedMorphism B D (deRhamDerivedModuleCorrespondence B D) n ξ =
      deRhamClassMorphism B D n ξ := by
  simp only [deRhamClassDerivedMorphism, deRhamDerivedModuleCorrespondence, Equiv.trans_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.SheafOfModules

end
