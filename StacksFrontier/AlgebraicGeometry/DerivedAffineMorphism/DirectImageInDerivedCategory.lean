module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel

/-!
# Direct image of a quasi-coherent module along an affine morphism, in the derived category

Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module.
The higher direct images of `F` vanish ([Stacks, Tag 01XC]), so the ordinary direct image
`f_*F`, placed in degree zero, *is* the derived direct image of `F[0]`:

`(f_*F)[0] ≅ Rf_*(F[0])` in `D(𝒪_S)`. In particular `f_*𝒪_X = Rf_*𝒪_X`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.isQuasicoherent_single_obj_X` — every term
  of the complex `F[0]` is quasi-coherent when `F` is.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso` — the
  isomorphism `(f_*F)[0] ≅ Rf_*(F[0])` for `f` affine and `F` quasi-coherent.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.homologyDerivedPushforwardSingleIso` and
  `Stacks.AlgebraicGeometry.DerivedAffinePushforward.isZero_homology_derivedPushforwardSingle` —
  the cohomology sheaves of `Rf_*(F[0])`: the direct image in degree zero and nothing else.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardStructureSheafIso` — the
  case `F = 𝒪_X`, that is `f_*𝒪_X = Rf_*𝒪_X`.

## Implementation notes

Every statement takes `[HasDerivedCategory.{w} _]` arguments rather than fixing a model of the
derived categories.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Every term of the complex `F[0]` concentrated in degree zero is quasi-coherent when `F` is. -/
theorem isQuasicoherent_single_obj_X (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (n : ℤ) :
    (((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F).X
      n).IsQuasicoherent := by
  have : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
    containsZero_isQuasicoherent X
  obtain rfl | h := eq_or_ne n 0
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm inferInstance
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) (0 : ℤ) F n h).isoZero.symm (ObjectProperty.prop_zero _)

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **The derived direct image of a quasi-coherent module along an affine morphism is its
ordinary direct image**: for `f` affine and `F` quasi-coherent, `(f_*F)[0] ≅ Rf_*(F[0])` in
`D(𝒪_S)`. -/
def derivedPushforwardSingleIso [IsAffineHom f] (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
        ((pushforwardSheafOfModules f).obj F) ≅
      (AnyModel.derivedPushforward.{w} f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F) :=
  let P := pushforwardSheafOfModules f
  let K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ :=
    (CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F
  have := AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom.{w} f K
    (isQuasicoherent_single_obj_X F)
  (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} S.ringCatSheaf) 0).app (P.obj F) ≪≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).app F)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} S.ringCatSheaf)).app
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (DerivedCategory.Qh.mapIso
      ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).symm ≪≫
    asIso ((AnyModel.derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj K)) ≪≫
    (AnyModel.derivedPushforward.{w} f).mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} X.ringCatSheaf) 0).app F).symm)

/-- **The direct image is the only cohomology sheaf of the derived direct image**: for `f`
affine and `F` quasi-coherent, `H^0(Rf_*(F[0])) ≅ f_*F`. -/
def homologyDerivedPushforwardSingleIso [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
        ((AnyModel.derivedPushforward.{w} f).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F)) ≅
      (pushforwardSheafOfModules f).obj F :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).mapIso
      (derivedPushforwardSingleIso.{w} f F).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} S.ringCatSheaf) 0).app ((pushforwardSheafOfModules f).obj F)

/-- **The higher direct images of a quasi-coherent module along an affine morphism vanish**:
for `f` affine and `F` quasi-coherent, `H^i(Rf_*(F[0])) = 0` for every `i ≠ 0`. -/
theorem isZero_homology_derivedPushforwardSingle [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] {i : ℤ} (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).obj
      ((AnyModel.derivedPushforward.{w} f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F))) :=
  have h : IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
        ((pushforwardSheafOfModules f).obj F))) :=
    (((DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} S.ringCatSheaf) i).app
        ((CochainComplex.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
          ((pushforwardSheafOfModules f).obj F))).isZero_iff).2
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        ((pushforwardSheafOfModules f).obj F) i hi)
  h.of_iso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).mapIso
    (derivedPushforwardSingleIso.{w} f F).symm)

/-- **`f_*𝒪_X = Rf_*𝒪_X` for an affine morphism**: `(f_*𝒪_X)[0] ≅ Rf_*(𝒪_X[0])` in
`D(𝒪_S)`. -/
def derivedPushforwardStructureSheafIso [IsAffineHom f] :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
        ((pushforwardSheafOfModules f).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (AnyModel.derivedPushforward.{w} f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
  derivedPushforwardSingleIso.{w} f (SheafOfModules.unit X.ringCatSheaf)

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
