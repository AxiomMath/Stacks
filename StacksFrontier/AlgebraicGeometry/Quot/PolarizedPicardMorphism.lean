module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing

/-!
# The polarized families of the relatively ample objects of a Picard stack, as families over `X₀`

Fix an object `X₀ ⟶ V₀` of `Spaces'_{fp, flat, proper}` over the big fppf site of `Spec(ℤ)`. For
an object `(T, L)` of `Picardstack_{X₀/V₀}` with `L` ample on `X_T/T`, let
`AlgebraicGeometry.amplePolarizedFamily` be the polarized family `(Z ⟶ T, L|_Z)` with `Z` the
scheme model of `X_T`. This file gives the remaining data of the comparison of the relatively
ample locus of `Picardstack_{X₀/V₀}` with the polarized families over `X₀`:

* the cartesian morphism `(Z ⟶ T) ⟶ (X₀ ⟶ V₀)` of `Spaces'_{fp, flat, proper}` from the image of
  the polarized family under the forgetful functor of Stacks 0D3Y; and
* for a morphism `(T', L') ⟶ (T, L)` of the Picard stack, the morphism of polarized families
  between the two scheme models: the morphism `Z' ⟶ Z` of schemes induced by `X_{T'} ⟶ X_T`,
  whose square is cartesian, and the comparison of polarizations obtained from the comparison of
  the Picard stack through the reading of modules on represented algebraic spaces as modules on
  schemes (`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`).

## Main definitions

* `AlgebraicGeometry.ampleArrow`: the cartesian morphism to `X₀`.
* `AlgebraicGeometry.ampleModelMap`: the morphism of scheme models of a morphism of the Picard
  stack.
* `AlgebraicGeometry.ampleModuleComparison` and `AlgebraicGeometry.ampleLineBundleIso`: the
  comparison of polarizations, on the represented algebraic spaces and on the schemes.
* `AlgebraicGeometry.amplePolarizedHom`: the morphism of polarized families.

## Main results

* `AlgebraicGeometry.amplePolarizedHom_comp_ampleArrow`: the morphism of polarized families
  commutes with the two morphisms to `X₀`.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
  {hc : Space.ModulePushforwardCoherence B integerBase B.contains_integerBase}

/-! ### The morphism to `X₀` -/

section Arrow

/-- The morphism of base schemes `T ⟶ V₀` of the test scheme of an object of the Picard stack,
from the normal form of `T`. -/
def ampleBaseMap (A : Space.PicardObject (properFlatPicardSituation X₀)) :
    (schemeOverIntegers B).obj A.T.left.left ⟶ X₀.obj.obj.right :=
  (integerNormIso A.T.left).hom ≫ yoneda.preimage A.T.hom.hom

/-- The Yoneda image of the morphism `T ⟶ V₀` is the structure morphism of the test scheme, from
the normal form of `T`. -/
theorem yoneda_map_ampleBaseMap (A : Space.PicardObject (properFlatPicardSituation X₀)) :
    yoneda.map (ampleBaseMap A) = yoneda.map (integerNormIso A.T.left).hom ≫ A.T.hom.hom :=
  (CategoryTheory.Functor.map_comp _ _ _).trans
    (congrArg (fun k => yoneda.map (integerNormIso A.T.left).hom ≫ k)
      (CategoryTheory.Functor.map_preimage yoneda A.T.hom.hom))

/-- The morphism `T ⟶ V₀` as a morphism of algebraic spaces is the structure morphism of the test
scheme, from the normal form of `T`. -/
theorem schemeSpaceMap_ampleBaseMap (A : Space.PicardObject (properFlatPicardSituation X₀)) :
    schemeSpaceMap (ampleBaseMap A) =
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map (integerNormIso A.T.left).hom ≫
        A.T.hom :=
  ObjectProperty.hom_ext _ (yoneda_map_ampleBaseMap A)

variable {A : Space.PicardObject (properFlatPicardSituation X₀)}
  (hA : Space.picardAmple hc (properFlatPicardSituation X₀) A)

/-- The left leg of the morphism to `X₀`: the projection `yoneda Z ≅ X_T ⟶ X₀`. -/
abbrev ampleArrowLeft : schemeSpace (ampleModel hA) ⟶ X₀.obj.obj.left :=
  (ampleModelSpaceIso hA).hom ≫ Space.baseChangeProjection (properFlatPicardSituation X₀).f A.T

/-- The square of the morphism to `X₀` commutes, as a square of algebraic spaces. -/
theorem ampleArrowLeft_comp :
    ampleArrowLeft hA ≫ commaHomAsSpaceMap X₀.obj.obj =
      schemeSpaceMap (ampleModelHom hA) ≫ schemeSpaceMap (ampleBaseMap A) := by
  have hsq : Space.baseChangeProjection (properFlatPicardSituation X₀).f A.T ≫
      (properFlatPicardSituation X₀).f =
        Space.baseChangeInclusion (properFlatPicardSituation X₀).f A.T ≫ A.T.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
      (properFlatPicardSituation X₀).f
      ((Space.schemesOverToOver (properFlatPicardSituation X₀).base).obj A.T).hom).w
  rw [schemeSpaceMap_ampleModelHom, schemeSpaceMap_ampleBaseMap, ampleArrowLeft]
  simp only [Functor.mapIso_inv]
  exact congrArg (fun k => (ampleModelSpaceIso hA).hom ≫ k) hsq

/-- The comma-category morphism underlying the morphism to `X₀`: the projection `yoneda Z ≅ X_T ⟶
X₀` over the morphism `T ⟶ V₀`. -/
def ampleArrowComma :
    (forgetPolarizationObj B (amplePolarizedFamily hA)).obj.obj ⟶ X₀.obj.obj where
  left := ampleArrowLeft hA
  right := ampleBaseMap A
  w := congrArg (fun k => k.hom) (ampleArrowLeft_comp hA)

/-- The square of the morphism to `X₀` is cartesian: it is the square defining `X_T`, up to the
two identifications. -/
theorem isPullback_ampleArrowLeft :
    IsPullback (ampleArrowLeft hA) (schemeSpaceMap (ampleModelHom hA))
      (commaHomAsSpaceMap X₀.obj.obj) (schemeSpaceMap (ampleBaseMap A)) := by
  refine (AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
    (properFlatPicardSituation X₀).f
    ((Space.schemesOverToOver (properFlatPicardSituation X₀).base).obj A.T).hom).of_iso
    (ampleModelSpaceIso hA).symm (Iso.refl _)
    ((schemeSpaceFunctor B integerBase B.contains_integerBase).mapIso
      (integerNormIso A.T.left)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm
  · rw [schemeSpaceMap_ampleModelHom]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [schemeSpaceMap_ampleBaseMap]
    have h : (schemeSpaceFunctor B integerBase B.contains_integerBase).map
          (integerNormIso A.T.left).inv ≫
        (schemeSpaceFunctor B integerBase B.contains_integerBase).map
          (integerNormIso A.T.left).hom ≫ A.T.hom = A.T.hom := by
      rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).trans h.symm

/-- The morphism to `X₀` is strongly cartesian, by Stacks 04U9. -/
theorem isStronglyCartesian_ampleArrowComma :
    (spacesProjection B integerBase B.contains_integerBase).IsStronglyCartesian
      (ampleArrowComma hA).right (ampleArrowComma hA) :=
  SpacesDescent.isStronglyCartesian_of_isPullback (ampleArrowComma hA).right
    (ampleArrowComma hA) rfl rfl (by simp) (by simp; rfl) (by simp; rfl)
    (AlgebraicSpaces.isPullback_hom B integerBase B.contains_integerBase
      (isPullback_ampleArrowLeft hA))

/-- **The morphism to `X₀`**: the forgetful functor of Stacks 0D3Y carries the polarized family of
a relatively ample object to the base change `X_T ⟶ T`, which maps to `X₀ ⟶ V₀` by a cartesian
square. -/
def ampleArrow : (forgetPolarization B).obj (amplePolarizedFamily hA) ⟶ X₀ :=
  ⟨ObjectProperty.homMk (ampleArrowComma hA), isStronglyCartesian_ampleArrowComma hA⟩

end Arrow

/-! ### Morphisms -/

section Hom

variable {A C : Space.PicardObject (properFlatPicardSituation X₀)}
  {hA : Space.picardAmple hc (properFlatPicardSituation X₀) A}
  {hC : Space.picardAmple hc (properFlatPicardSituation X₀) C}

variable (hA hC) in
/-- **The morphism of scheme models** over a morphism `T' ⟶ T` of test schemes: the morphism
`Z' ⟶ Z` the morphism `X_{T'} ⟶ X_T` of base changes induces. -/
def ampleModelBaseMap (g : A.T ⟶ C.T) : ampleModel hA ⟶ ampleModel hC :=
  yoneda.preimage ((ampleModelIso hA).hom ≫
    (Space.baseChangeMap (properFlatPicardSituation X₀).f g).hom ≫ (ampleModelIso hC).inv)

variable (hA hC) in
/-- The morphism of scheme models of a morphism of the Picard stack, which depends only on its
morphism of test schemes. -/
abbrev ampleModelMap (m : Space.PicardHom A C) : ampleModel hA ⟶ ampleModel hC :=
  ampleModelBaseMap hA hC m.base

/-- The morphism of scheme models over a morphism of test schemes, read on the represented
algebraic spaces, is the morphism of base changes up to the identifications. -/
theorem schemeSpaceMap_ampleModelBaseMap (g : A.T ⟶ C.T) :
    schemeSpaceMap (ampleModelBaseMap hA hC g) = (ampleModelSpaceIso hA).hom ≫
      Space.baseChangeMap (properFlatPicardSituation X₀).f g ≫ (ampleModelSpaceIso hC).inv :=
  ObjectProperty.hom_ext _ (yoneda.map_preimage _)

/-- The morphism of scheme models of a morphism of the Picard stack, read on the represented
algebraic spaces, is the morphism of base changes up to the identifications. -/
theorem schemeSpaceMap_ampleModelMap (m : Space.PicardHom A C) :
    schemeSpaceMap (ampleModelMap hA hC m) = (ampleModelSpaceIso hA).hom ≫
      Space.baseChangeMap (properFlatPicardSituation X₀).f m.base ≫ (ampleModelSpaceIso hC).inv :=
  schemeSpaceMap_ampleModelBaseMap m.base

/-- The square of represented algebraic spaces relating the morphism of scheme models over a
morphism of test schemes with the morphism of base changes. -/
theorem ampleModelBaseMap_comp_ampleModelSpaceIso (g : A.T ⟶ C.T) :
    Space.representedSpaceMap B integerBase B.contains_integerBase (ampleModelBaseMap hA hC g) ≫
        (ampleModelSpaceIso hC).hom =
      (ampleModelSpaceIso hA).hom ≫ Space.baseChangeMap (properFlatPicardSituation X₀).f g := by
  have h := schemeSpaceMap_ampleModelBaseMap (hA := hA) (hC := hC) g
  change schemeSpaceMap (ampleModelBaseMap hA hC g) ≫ (ampleModelSpaceIso hC).hom = _
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The square of represented algebraic spaces relating the morphism of scheme models with the
morphism of base changes. -/
theorem ampleModelMap_comp_ampleModelSpaceIso (m : Space.PicardHom A C) :
    Space.representedSpaceMap B integerBase B.contains_integerBase (ampleModelMap hA hC m) ≫
        (ampleModelSpaceIso hC).hom =
      (ampleModelSpaceIso hA).hom ≫ Space.baseChangeMap (properFlatPicardSituation X₀).f m.base :=
  ampleModelBaseMap_comp_ampleModelSpaceIso m.base

/-- The normal forms of the test schemes are natural, read on the represented algebraic spaces. -/
private theorem map_schemeOverIntegers_comp_integerNormIso_hom
    {A C : Space.PicardObject (properFlatPicardSituation X₀)} (g : A.T.left ⟶ C.T.left) :
    (schemeSpaceFunctor B integerBase B.contains_integerBase).map
        ((schemeOverIntegers B).map g.left) ≫
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map (integerNormIso C.T.left).hom =
    (schemeSpaceFunctor B integerBase B.contains_integerBase).map (integerNormIso A.T.left).hom ≫
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map g := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The square of scheme models over the morphism of test schemes is cartesian, as a square of
algebraic spaces: it is the square of base changes, up to the identifications. -/
theorem isPullback_schemeSpaceMap_ampleModelMap (m : Space.PicardHom A C) :
    IsPullback (schemeSpaceMap (ampleModelMap hA hC m)) (schemeSpaceMap (ampleModelHom hA))
      (schemeSpaceMap (ampleModelHom hC))
      (schemeSpaceMap ((schemeOverIntegers B).map m.base.left.left)) := by
  have hnat : (schemeSpaceFunctor B integerBase B.contains_integerBase).map m.base.left ≫
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map
        (integerNormIso C.T.left).inv =
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map
        (integerNormIso A.T.left).inv ≫
        (schemeSpaceFunctor B integerBase B.contains_integerBase).map
          ((schemeOverIntegers B).map m.base.left.left) := by
    rw [← Functor.mapIso_inv, ← Functor.mapIso_inv, Iso.comp_inv_eq, Category.assoc,
      Functor.mapIso_hom, map_schemeOverIntegers_comp_integerNormIso_hom, Functor.mapIso_inv,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  refine (Space.isPullback_baseChangeMap (properFlatPicardSituation X₀).f m.base).of_iso
    (ampleModelSpaceIso hA).symm (ampleModelSpaceIso hC).symm
    ((schemeSpaceFunctor B integerBase B.contains_integerBase).mapIso
      (integerNormIso A.T.left)).symm
    ((schemeSpaceFunctor B integerBase B.contains_integerBase).mapIso
      (integerNormIso C.T.left)).symm ?_ ?_ ?_ ?_
  · rw [schemeSpaceMap_ampleModelMap]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · rw [schemeSpaceMap_ampleModelHom]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · rw [schemeSpaceMap_ampleModelHom]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · exact hnat

variable (hA hC) in
/-- The square of scheme models over the morphism of test schemes is a cartesian square of
schemes. -/
theorem isPullback_ampleModelMap (m : Space.PicardHom A C) :
    IsPullback (B.inclusion.map (ampleModelMap hA hC m).left)
      (B.inclusion.map (ampleModelHom hA).left) (B.inclusion.map (ampleModelHom hC).left)
      (B.inclusion.map m.base.left.left) := by
  have h1 := AlgebraicSpaces.isPullback_hom B integerBase B.contains_integerBase
    (isPullback_schemeSpaceMap_ampleModelMap (hA := hA) (hC := hC) m)
  have h2 : IsPullback (ampleModelMap hA hC m) (ampleModelHom hA) (ampleModelHom hC)
      ((schemeOverIntegers B).map m.base.left.left) :=
    IsPullback.of_map yoneda (yoneda.map_injective
      ((yoneda.map_comp (ampleModelMap hA hC m) (ampleModelHom hC)).trans
        (h1.w.trans (yoneda.map_comp (ampleModelHom hA)
          ((schemeOverIntegers B).map m.base.left.left)).symm))) h1
  exact h2.map (BigFppfOver.toScheme B integerBase B.contains_integerBase)

/-- The comparison of modules of a morphism of the Picard stack, as an isomorphism. -/
def picardFibreIso (m : Space.PicardHom A C) :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.baseChangeMap (properFlatPicardSituation X₀).f m.base)).obj C.lineBundle ≅
      A.lineBundle :=
  @asIso _ _ _ _ m.fibre m.isIso_fibre

/-- The underlying morphism of `AlgebraicGeometry.picardFibreIso` is the comparison `m.fibre`. -/
@[simp]
theorem picardFibreIso_hom (m : Space.PicardHom A C) : (picardFibreIso m).hom = m.fibre :=
  rfl

variable (hA hC) in
/-- **The comparison of polarizations on the represented algebraic spaces** of a morphism of the
Picard stack: the inverse image along `Z' ⟶ Z` of the module of the target is the module of the
source, through the canonical comparison of the two iterated inverse images along the square of
`AlgebraicGeometry.ampleModelMap_comp_ampleModelSpaceIso` and the comparison `m.fibre` of the
Picard stack. -/
def ampleModuleComparison (m : Space.PicardHom A C) :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase
          (ampleModelMap hA hC m))).obj (ampleModelModule hC) ≅ ampleModelModule hA :=
  Space.QuasiCoherentDescent.canonicalComparison _ _ _ _
      (ampleModelMap_comp_ampleModelSpaceIso m) C.lineBundle ≪≫
    (Space.modulePullback B integerBase B.contains_integerBase
      (ampleModelSpaceIso hA).hom).mapIso (picardFibreIso m)

variable (hA hC) in
/-- **The comparison of polarizations** of a morphism of the Picard stack, on the scheme models:
the reading of modules on represented algebraic spaces as modules on schemes commutes with
inverse images (`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`), so the inverse
image along `Z' ⟶ Z` of the polarization of `Z` is the reading of the inverse image of the module
of the target, which is the module of the source by `AlgebraicGeometry.ampleModuleComparison`. -/
def ampleLineBundleIso (m : Space.PicardHom A C) :
    (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
        (ampleModelMap hA hC m).left)).obj (ampleModelLineBundle hC) ≅ ampleModelLineBundle hA :=
  Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
      (ampleModelMap hA hC m)
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      (ampleModelModule hC) (isQuasicoherentOnSite_ampleModelModule hC) ≪≫
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
        (ampleModel hA).left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        (ampleModel hA)).inverse.mapIso (ampleModuleComparison hA hC m))

variable (hA hC) in
/-- **The morphism of polarized families** of a morphism of the Picard stack between relatively
ample objects. -/
def amplePolarizedHom (m : Space.PicardHom A C) :
    amplePolarizedFamily hA ⟶ amplePolarizedFamily hC where
  baseMap := m.base.left.left
  totalMap := SmallEtale.schemeHom (associatedBigEtaleSite B) (ampleModelMap hA hC m).left
  cartesian := isPullback_ampleModelMap hA hC m
  lineBundleIso := ampleLineBundleIso hA hC m

variable (hA hC) in
/-- **The morphism of polarized families commutes with the two morphisms to `X₀`.** On the
algebraic spaces this is the compatibility of the morphism of base changes with the projections
to `X₀`, and on the bases it is the compatibility of the morphism of test schemes with their
structure morphisms. -/
theorem amplePolarizedHom_comp_ampleArrow (m : Space.PicardHom A C) :
    (forgetPolarization B).map (amplePolarizedHom hA hC m) ≫ ampleArrow hC = ampleArrow hA := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · have h : schemeSpaceMap (ampleModelMap hA hC m) ≫ ampleArrowLeft hC = ampleArrowLeft hA := by
      have e := ampleModelMap_comp_ampleModelSpaceIso (hA := hA) (hC := hC) m
      have e' := Space.baseChangeMap_comp_projection (properFlatPicardSituation X₀).f m.base
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e')))
    exact h
  · let F := schemeSpaceFunctor B integerBase B.contains_integerBase
    have e2 : ∀ D : Space.PicardObject (properFlatPicardSituation X₀),
        F.map (ampleBaseMap D) = F.map (integerNormIso D.T.left).hom ≫ D.T.hom :=
      schemeSpaceMap_ampleBaseMap
    have H : F.map ((schemeOverIntegers B).map m.base.left.left ≫ ampleBaseMap C) =
        F.map (ampleBaseMap A) := by
      rw [F.map_comp, e2, e2]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.T.hom)
        (map_schemeOverIntegers_comp_integerNormIso_hom m.base.left)).trans
          ((Category.assoc _ _ _).trans (congrArg _ m.base.w)))
    exact yoneda.map_injective (congrArg (fun k => k.hom) H)

end Hom

end AlgebraicGeometry

end
