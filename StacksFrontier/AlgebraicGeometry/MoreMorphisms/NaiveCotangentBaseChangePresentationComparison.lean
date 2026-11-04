module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalClasses

/-!
# The pulled-back presentation comparison computes the base change map of `NL` in degree `-1`

For commutative squares `i' ≫ p = g' ≫ i` and `g' ≫ (i ≫ h) = (i' ≫ h') ≫ g` of schemes with `i`,
`i'` immersions, the degree `-1` comparison `pulledPresentationNegOne` of the pulled-back
polynomial presentation of `𝒪_X` with that of `𝒪_{X'}`, followed by the comparison of the latter
with `NL_{X'/Y'}`, is the degree `-1` component of the pullback of the comparison with
`NL_{X/Y}` followed by the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of
[Stacks Project, Tag 0FV5] (`pulledPresentationNegOne_comp_presentationToNaiveCotangent`).
This is the identity the proof of [Stacks Project, Tag 0FV9] feeds to
`homologyMap_inv_homologyNegOneι_eq_of_degreewise`.

Both sides are maps out of a pullback of a conormal sheaf, so they are compared on the unit
images of conormal classes of polynomial relations, where both are computed by the class
formulas of `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalClasses`
and agree by `presentationRingMap_comp_evaluation`.

## Implementation notes

The class formulas are restated here in the spellings the identity is stated in (the structure
map of `i ≫ h` through `ringedSpaceHom`, the complexes through `pulledComplexFunctor`), and the
element fed to the base change map is abstracted (`baseChangeMapOfComparison_f_negOne_unit_of_eq`):
an element term that differs from the lemma's under the coercion of the base change map, even only
by an unfolding, makes the kernel evaluate the base change map.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.NaiveCotangentFlatBaseChange

universe u

noncomputable section

namespace Stacks.NaiveCotangentPulledImmersion

section BaseChangeMapSpelling

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      inverseImageSheaf f'.toLRSHom.toShHom)
    (hbc : inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom)

/-- The conormal class of a section of the kernel of the canonical presentation over
`(ringedSpaceHom f)⁻¹𝒪_Y` is the conormal class of the same section over
`inverseImageBaseRingOnMiddle f.toLRSHom.toShHom`. -/
theorem conormalClassX_inverseImageSheaf_ringedSpaceHom (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U) :
    conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageSheaf (ringedSpaceHom f)) _)
      (canonicalPresentation (Opens.grothendieckTopology X.carrier)
        (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom f)))
      (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t =
    conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
      (canonicalPresentation (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
        (ringedSpaceStructureMap f.toLRSHom.toShHom))
      (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t := rfl

/-- `baseChangeMapOfComparison_f_negOne_unit_conormalClassX` on a section of the kernel of the
canonical presentation over `(ringedSpaceHom f)⁻¹𝒪_Y`. -/
theorem baseChangeMapOfComparison_f_negOne_unit_conormalClassX_of_ringedSpaceHom
    (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f'))).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f)))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom f')))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' :=
  (congrArg (fun x => (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
      ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
      (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U x) : _))
    (conormalClassX_inverseImageSheaf_ringedSpaceHom f U t)).trans
    (baseChangeMapOfComparison_f_negOne_unit_conormalClassX f f' g' bc hbc U t t' ht')

/-- `baseChangeMapOfComparison_f_negOne_unit_conormalClassX`, with the conormal sheaf of the
canonical presentation over `(ringedSpaceHom f)⁻¹𝒪_Y` read in `NL_{X/Y}`. -/
theorem baseChangeMapOfComparison_f_negOne_unit_conormalClassX_naiveCotangentComplex
    (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f'))).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app
            ((AlgebraicGeometry.Scheme.naiveCotangentComplex f).X (-1))).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f)))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom f')))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' :=
 by
  refine Eq.trans ?_
    (baseChangeMapOfComparison_f_negOne_unit_conormalClassX_of_ringedSpaceHom f f' g' bc hbc U t t'
        ht')
  exact congrArg (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
      ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)).hom rfl

/-- `baseChangeMapOfComparison_f_negOne_unit_conormalClassX`, with the conormal sheaf of the
canonical presentation over `(ringedSpaceHom f)⁻¹𝒪_Y` read in `NL` of `ringedSpaceHom f`. -/
theorem baseChangeMapOfComparison_f_negOne_unit_conormalClassX_ringedSpaceHom
    (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f'))).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f))).X (-1))).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f)))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom f')))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' :=
 by
  refine Eq.trans ?_
    (baseChangeMapOfComparison_f_negOne_unit_conormalClassX_of_ringedSpaceHom f f' g' bc hbc U t t'
        ht')
  exact congrArg (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
      ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)).hom rfl

/-- `baseChangeMapOfComparison_f_negOne_unit_conormalClassX_naiveCotangentComplex`, with the
degree `-1` component of the base change map taken as a morphism out of the pullback along `g'`
of `NL_{X/Y}`. -/
theorem baseChangeMapOfComparison_f_negOne_unit_scheme
    (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f'))).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    ((@HomologicalComplex.Hom.f _ _ _ _ _
        ((pulledComplexFunctor g'.toLRSHom.toShHom).obj
            (AlgebraicGeometry.Scheme.naiveCotangentComplex f))
        _ (baseChangeMapOfComparison f f' g' bc hbc) (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app
            ((AlgebraicGeometry.Scheme.naiveCotangentComplex f).X (-1))).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f)))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom f')))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' :=

  baseChangeMapOfComparison_f_negOne_unit_conormalClassX_naiveCotangentComplex f f' g' bc hbc U t
      t' ht'

/-- The degree `-1` component of the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` sends the
image under the unit of a section `y` equal to the conormal class of `t` to the conormal class of
`t'`, where `t'` is the image of `t` in the free algebra over `(f')⁻¹𝒪_{Y'}`. -/
theorem baseChangeMapOfComparison_f_negOne_unit_of_eq
    (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f))).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom f'))).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (y : ((AlgebraicGeometry.Scheme.naiveCotangentComplex f).X (-1)).val.obj U)
    (hy : y = conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom f)) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom f)))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    ((@HomologicalComplex.Hom.f _ _ _ _ _
        ((pulledComplexFunctor g'.toLRSHom.toShHom).obj
            (AlgebraicGeometry.Scheme.naiveCotangentComplex f))
        _ (baseChangeMapOfComparison f f' g' bc hbc) (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app
            ((AlgebraicGeometry.Scheme.naiveCotangentComplex f).X (-1))).val.app U
          y) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom f')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom f')))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' :=

  hy ▸ baseChangeMapOfComparison_f_negOne_unit_scheme f f' g' bc hbc U t t' ht'

end BaseChangeMapSpelling

section PulledComp

/-- `comp_f_val_app` for complexes of modules over the structure sheaf of a ringed space. -/
theorem comp_f_val_app_ringedSpace {T : RingedSpace.{u, u}}
    {inst : HasZeroMorphisms (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T.carrier) T.sheaf))}
    {K L M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology T.carrier) T.sheaf)) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (i : ℤ) (U : (Opens T.carrier)ᵒᵖ) (x : (K.X i).val.obj U) :
    ((φ ≫ ψ).f i).val.app U x = (ψ.f i).val.app U ((φ.f i).val.app U x) :=
  rfl

/-- On the image under the unit of a section `x`, the degree `i` component of
`((g')^*a ≫ (g')^*b) ≫ d` is `d_i` applied to the image under the unit of `(a ≫ b)_i x`. -/
theorem pulledComplexFunctor_map_comp_map_comp_f_unit {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)
    {K L M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ}
    {N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.carrier) X'.sheaf)) ℤ}
    (a : K ⟶ L) (b : L ⟶ M) (d : (pulledComplexFunctor g').obj M ⟶ N) (i : ℤ)
    (U : (Opens X.carrier)ᵒᵖ) (x : (K.X i).val.obj U) :
    ((((pulledComplexFunctor g').map a ≫ (pulledComplexFunctor g').map b) ≫ d).f i).val.app
        ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app (K.X i)).val.app U x) =
      (d.f i).val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app (M.X i)).val.app U (((a ≫ b).f i).val.app U x)) := by
  have h := pulledComplexFunctor_map_f_unitC g' (a ≫ b) i U x
  rw [Functor.map_comp] at h
  exact (comp_f_val_app_ringedSpace _ _ i _ _).trans (congrArg _ h)

/-- **Maps out of the degree `-1` term of a pulled-back complex, against a composite of
pulled-back chain maps followed by a chain map.**  Such a map agrees with
`(((g')^*a ≫ (g')^*b) ≫ d)_{-1}` as soon as both agree on the images under the unit of
conormal classes, the second being evaluated through the values `y` of `(a ≫ b)_{-1}`. -/
theorem pulledComplexFunctor_hom_ext_conormalClassX {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)
    {R A : CategoryTheory.Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (a : R ⟶ A) (φ : A ⟶ X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) φ.hom]
    {K L M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ}
    (e : K.X (-1) = (conormalSequence.{u, u, u, u} _ R A X.sheaf a φ).X₁)
    {N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.carrier) X'.sheaf)) ℤ}
    (α : K ⟶ L) (β : L ⟶ M) (d : (pulledComplexFunctor g').obj M ⟶ N)
    (f : (twoStepPullback g').obj (K.X (-1)) ⟶ N.X (-1))
    (y : ∀ (U : (Opens X.carrier)ᵒᵖ) (_ : kernelIdeal φ.hom U), (M.X (-1)).val.obj U)
    (hy : ∀ (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U),
      ((α ≫ β).f (-1)).val.app U (conormalClassX a φ e U s) = y U s)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U),
      f.val.app ((Opens.map g'.hom.base).op.obj U)
          (((twoStepCompAdjunction g').unit.app _).val.app U (conormalClassX a φ e U s)) =
        (d.f (-1)).val.app ((Opens.map g'.hom.base).op.obj U)
          (((twoStepCompAdjunction g').unit.app (M.X (-1))).val.app U (y U s))) :
    f = (((pulledComplexFunctor g').map α ≫ (pulledComplexFunctor g').map β) ≫ d).f (-1) :=
  twoStepPullback_hom_ext_conormalClassX g' a φ e (fun U s =>
    ((h U s).trans (congrArg _ (congrArg _ (hy U s)).symm)).trans
      (pulledComplexFunctor_map_comp_map_comp_f_unit g' α β d (-1) U _).symm)

/-- `pulledComplexFunctor_hom_ext_conormalClassX` for a morphism of schemes. -/
theorem pulledComplexFunctor_hom_ext_conormalClassX_scheme {X X' : Scheme.{u}} (g' : X' ⟶ X)
    {R A : CategoryTheory.Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (a : R ⟶ A) (φ : A ⟶ X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) φ.hom]
    {K L M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier)
        X.toRingedSpace.sheaf)) ℤ}
    (e : K.X (-1) = (conormalSequence.{u, u, u, u} _ R A X.sheaf a φ).X₁)
    {N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
        X'.toRingedSpace.sheaf)) ℤ}
    (α : K ⟶ L) (β : L ⟶ M) (d : (pulledComplexFunctor g'.toLRSHom.toShHom).obj M ⟶ N)
    (f : (twoStepPullback g'.toLRSHom.toShHom).obj (K.X (-1)) ⟶ N.X (-1))
    (y : ∀ (U : (Opens X.carrier)ᵒᵖ) (_ : kernelIdeal φ.hom U), (M.X (-1)).val.obj U)
    (hy : ∀ (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U),
      ((α ≫ β).f (-1)).val.app U (conormalClassX a φ e U s) = y U s)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U),
      f.val.app ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
          (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
            (conormalClassX a φ e U s)) =
        (@HomologicalComplex.Hom.f _ _ _ _ _ ((pulledComplexFunctor g'.toLRSHom.toShHom).obj M) _
            d (-1)).val.app ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
          (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app (M.X (-1))).val.app U (y U s))) :
    f = (((pulledComplexFunctor g'.toLRSHom.toShHom).map α ≫
      (pulledComplexFunctor g'.toLRSHom.toShHom).map β) ≫ d).f (-1) :=
  pulledComplexFunctor_hom_ext_conormalClassX g'.toLRSHom.toShHom a φ e α β d f y hy h

end PulledComp

section IdentityB

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- The comparison of the polynomial presentation with `NL_{X/Y}` in degree `-1`, as a
composite out of `towerPresentationComplex`, on conormal classes. -/
theorem presentationComparison_comp_inv_f_negOne_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    ((@CategoryStruct.comp _ _ (towerPresentationComplex i h) _
        (AlgebraicGeometry.Scheme.naiveCotangentComplex (i ≫ h)) (presentationComparison i h)
        (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv).f (-1)).val.app U
        (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
          (towerPresentationComplex_X_negOne i h) U s) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
            ((evaluationRingMap i h).hom.app U s),
          evaluation_comp_inv_mem_kernelIdeal i h U s⟩ :=
  (comp_f_val_app _ _ (-1) U _).trans
    ((congrArg _ (presentationComparison_conormalClassX i h U s)).trans
      (schemePresentationIso_inv_f_negOne_conormalClassX i h U
        ⟨(evaluationRingMap i h).hom.app U s, evaluationRingMap_mem_kernelIdeal i h U s⟩))

/-- The section of the degree `-1` term of `NL_{X/Y}` for `i ≫ h` given by the conormal class of
the image of a relation `s` of `towerPresentation i h` in the canonical presentation over
`(ringedSpaceHom (i ≫ h))⁻¹𝒪_Y`. -/
noncomputable def relationClassX (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal (towerPresentation i
    h).hom U) :
    ((AlgebraicGeometry.Scheme.naiveCotangentComplex (i ≫ h)).X (-1)).val.obj U :=
  conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
            ((evaluationRingMap i h).hom.app U s),
          evaluation_comp_inv_mem_kernelIdeal i h U s⟩

/-- The degree `-1` comparison `pulledPresentationNegOne` followed by the degree `-1` component of
`presentationToNaiveCotangent i' h'` is the degree `-1` component of the pullback along `g'` of
the comparison of `towerPresentationComplex i h` with `NL_{X/Y}`, followed by the base change map
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`. -/
theorem pulledPresentationNegOne_comp_presentationToNaiveCotangent (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    pulledPresentationNegOne i h i' h' g' p g hip w ≫ (presentationToNaiveCotangent i' h').f (-1) =
      ((((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
          (pulledComplexFunctor g'.toLRSHom.toShHom).map
            ((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv :
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
                ringedSpaceStructureMap (ringedSpaceHom i)) ⟶
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))) :
          (pulledComplexFunctor g'.toLRSHom.toShHom).obj (towerPresentationComplex i h) ⟶
            pulledComplex (i ≫ h) g')) ≫
        baseChangeMapOfComparison (i ≫ h) (i' ≫ h') g'
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp (i ≫ h) (i' ≫ h') g' g
            w)).f (-1) := by
  refine pulledComplexFunctor_hom_ext_conormalClassX_scheme g'
    (towerCoefficientMap i h) (towerPresentation i h) (towerPresentationComplex_X_negOne i h)
    (presentationComparison i h) ((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv :
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
                ringedSpaceStructureMap (ringedSpaceHom i)) ⟶
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))) (baseChangeMapOfComparison (i ≫
                  h) (i' ≫ h') g'
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp (i ≫ h) (i' ≫ h') g' g w)) _
          (relationClassX i h)
    (presentationComparison_comp_inv_f_negOne_conormalClassX i h)
    (fun U s => ?_)
  have hpoly : (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
          (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
          (inverseImageSheaf (ringedSpaceHom (i' ≫ h'))) X'.sheaf X'.sheaf
          (inverseImageCompIso (ringedSpaceHom i') (ringedSpaceHom h')).inv (𝟙 _)).hom.app
              ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
            ((evaluationRingMap i' h').hom.app ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
              (pulledRelation i h i' h' g' p g hip w U s).1) =
      (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf (i' ≫ h').toLRSHom.toShHom)
        X'.sheaf X'.sheaf (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h')
          g' g w) (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle (i ≫ h).toLRSHom.toShHom) X.sheaf) U).hom
          ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
            (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
              ((evaluationRingMap i h).hom.app U s)))) :=
    congrArg (fun φ => φ.hom.app U s.1) ((congrArg (· ≫ _)
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base).homEquiv _
          _).apply_symm_apply
        (presentationRingMap i h i' h' g' p g hip w)).symm.trans
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base).homEquiv_unit _ _
          (presentationRingComparison i h i' h' g' p g hip w)))).symm.trans
      (presentationRingMap_comp_evaluation i h i' h' g' p g hip w))
  refine ((comp_val_app _ _ _ _).trans ((congrArg _
    (pulledPresentationNegOne_unit_conormalClassX i h i' h' g' p g hip w U s)).trans
    (presentationToNaiveCotangent_f_negOne_conormalClassX i' h' _
      (pulledRelation i h i' h' g' p g hip w U s)))).trans ?_
  have hy : relationClassX i h U s = _ := rfl
  exact (baseChangeMapOfComparison_f_negOne_unit_of_eq (i ≫ h) (i' ≫ h') g'
    (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
    (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp (i ≫ h) (i' ≫ h') g' g w) U _ _
    (relationClassX i h U s) hy hpoly).symm

end IdentityB

end Stacks.NaiveCotangentPulledImmersion

end
