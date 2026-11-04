module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleLocus
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback

/-!
# The polarized family attached to a relatively ample object of a Picard stack

Let `X₀ ⟶ V₀` be a finitely presented, flat and proper family of algebraic spaces over a scheme
`V₀` of the big fppf site of `Spec(ℤ)`, that is an object of `Spaces'_{fp, flat, proper}`. An
object of `Picardstack_{X₀/V₀}` is a scheme `T` over `V₀` together with an invertible module `L`
on `X_T = X₀ ×_{V₀} T`. When `L` is ample on `X_T/T` (Stacks 0D31), `X_T` is a scheme `Z` by
Stacks 0D32, and the restriction of `L` to `Z` is an invertible module, relatively ample for the
morphism `Z ⟶ T`; the structure morphism is proper, flat and of finite presentation because it is
a base change of `X₀ ⟶ V₀`. So `(Z ⟶ T, L|_Z)` is a polarized family of Stacks 0D1M.

This is the object half of the comparison, in the proof of Stacks 0D41, of the 2-fibre product
`(Sch/V₀) ×_{Spaces'} Polarized` with the relatively ample locus of `Picardstack_{X₀/V₀}`.

## Main definitions

* `AlgebraicGeometry.properFlatCoherentSituation`: the standing data of Situation 08KB attached
  to an object of `Spaces'_{fp, flat, proper}`, and
  `AlgebraicGeometry.properFlatPicardSituation` the Picard situation it determines.
* `AlgebraicGeometry.integerNormIso`: an object of the big fppf site of the terminal scheme is
  the object `AlgebraicGeometry.schemeOverIntegers` attaches to its underlying scheme.
* `AlgebraicGeometry.ampleModel` and `AlgebraicGeometry.ampleModelIso`: the scheme `Z` with
  `yoneda Z ≅ X_T`, normalized to the form `AlgebraicGeometry.schemeOverIntegers` produces.
* `AlgebraicGeometry.ampleModelModule`: the module on `yoneda Z` of an ample object, and
  `AlgebraicGeometry.ampleModelLineBundle` its reading on the scheme `Z`.
* `AlgebraicGeometry.amplePolarizedFamily`: the polarized family `(Z ⟶ T, L|_Z)`.

## Main results

* `AlgebraicGeometry.isProper_toScheme_map_of_isProperFlat_yoneda_map` and its companions: a
  morphism of the site whose Yoneda image is proper, flat and of finite presentation is so as a
  morphism of schemes.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}}

/-! ### Transferring properties from represented morphisms to morphisms of schemes -/

section Transfer

variable {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the site whose Yoneda image is of finite presentation and proper is of finite
presentation as a morphism of schemes: local finite presentation is a chart condition (Stacks
03MJ), and quasi-compactness and quasi-separatedness come from properness. -/
theorem finitePresentation_toScheme_map_of_yoneda_map {U V : BigFppfOver B S hS} (m : U ⟶ V)
    (hfp : Space.IsFinitePresentation B S hS (yoneda.map m))
    (hpr : Space.IsProper B S hS (yoneda.map m)) :
    FinitePresentation ((BigFppfOver.toScheme B S hS).map m) := by
  have hp : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) :=
    Space.isProper_toScheme_map_of_isProper_yoneda_map B S hS m hpr
  exact FinitePresentation.mk
    ((Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget m).1 hfp.1)
    inferInstance inferInstance

end Transfer

/-! ### The Picard situation of a family of `Spaces'_{fp, flat, proper}` -/

section Situation

/-- An object of the big fppf site of the terminal scheme is the object
`AlgebraicGeometry.schemeOverIntegers` attaches to its underlying scheme: two morphisms to the
terminal scheme agree. -/
def integerNormIso (V : BigFppfOver B integerBase B.contains_integerBase) :
    (schemeOverIntegers B).obj V.left ≅ V :=
  Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The underlying morphism of `AlgebraicGeometry.integerNormIso` is the identity. -/
@[simp]
theorem integerNormIso_hom_left (V : BigFppfOver B integerBase B.contains_integerBase) :
    (integerNormIso V).hom.left = 𝟙 _ :=
  rfl

/-- The underlying morphism of the inverse of `AlgebraicGeometry.integerNormIso` is the
identity. -/
@[simp]
theorem integerNormIso_inv_left (V : BigFppfOver B integerBase B.contains_integerBase) :
    (integerNormIso V).inv.left = 𝟙 _ :=
  rfl

variable (X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase)

/-- The standing data of Situation 08KB attached to an object `X₀ ⟶ V₀` of
`Spaces'_{fp, flat, proper}`: the morphism of algebraic spaces from `X₀` to the algebraic space
`V₀` represents. -/
def properFlatCoherentSituation : Space.CoherentSituation B integerBase B.contains_integerBase where
  X := X₀.obj.obj.left
  Y := schemeSpace X₀.obj.obj.right
  f := commaHomAsSpaceMap X₀.obj.obj
  finitePresentation := X₀.obj.property.1

/-- The structure morphism of the standing data is flat. -/
theorem properFlatCoherentSituation_isFlat :
    Space.IsFlat B integerBase B.contains_integerBase
      (properFlatCoherentSituation X₀).f.hom :=
  X₀.obj.property.2.1

/-- The structure morphism of the standing data is proper. -/
theorem properFlatCoherentSituation_isProper :
    Space.IsProper B integerBase B.contains_integerBase
      (properFlatCoherentSituation X₀).f.hom :=
  X₀.obj.property.2.2

/-- The Picard situation of an object `X₀ ⟶ V₀` of `Spaces'_{fp, flat, proper}`. -/
abbrev properFlatPicardSituation : Space.PicardSituation B integerBase B.contains_integerBase :=
  (properFlatCoherentSituation X₀).toPicardSituation

end Situation

/-! ### The scheme model of a relatively ample object -/

section Model

variable {X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase}

local notation "s₀" => properFlatPicardSituation X₀

/-- The base change `X_T ⟶ T` of the family along a test scheme is of finite presentation, flat
and proper. -/
theorem properFlat_baseChangeInclusion (T : (s₀).SchemesOver) :
    Space.IsFinitePresentation B integerBase B.contains_integerBase
        (Space.baseChangeInclusion (s₀).f T).hom ∧
      Space.IsFlat B integerBase B.contains_integerBase
        (Space.baseChangeInclusion (s₀).f T).hom ∧
      Space.IsProper B integerBase B.contains_integerBase
        (Space.baseChangeInclusion (s₀).f T).hom := by
  have hsq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
    (s₀).f ((Space.schemesOverToOver (s₀).base).obj T).hom)
  exact ⟨(Space.isFinitePresentation_isStableUnderBaseChange B integerBase
      B.contains_integerBase).of_isPullback hsq (properFlatCoherentSituation X₀).finitePresentation,
    (Space.isFlat_isStableUnderBaseChange B integerBase
      B.contains_integerBase).of_isPullback hsq (properFlatCoherentSituation_isFlat X₀),
    (Space.isProper_isStableUnderBaseChange B integerBase
      B.contains_integerBase).of_isPullback hsq (properFlatCoherentSituation_isProper X₀)⟩

variable {hc : Space.ModulePushforwardCoherence B integerBase B.contains_integerBase}

/-- The base change of a relatively ample object is representable. -/
theorem isRepresentable_baseChange_of_picardAmple {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) : ((s₀).baseChange A.T).1.IsRepresentable :=
  have : ((schemeSpaceFunctor B integerBase B.contains_integerBase).obj
      A.T.left).1.IsRepresentable :=
    inferInstanceAs (yoneda.obj A.T.left).IsRepresentable
  hA.isRepresentable

/-- **The scheme model of a relatively ample object**: the scheme representing `X_T`, normalized
to the form `AlgebraicGeometry.schemeOverIntegers` produces. -/
def ampleModel {A : Space.PicardObject s₀} (hA : Space.picardAmple hc s₀ A) :
    BigFppfOver B integerBase B.contains_integerBase :=
  haveI := isRepresentable_baseChange_of_picardAmple hA
  (schemeOverIntegers B).obj ((s₀).baseChange A.T).1.reprX.left

/-- The scheme model represents `X_T`. -/
def ampleModelIso {A : Space.PicardObject s₀} (hA : Space.picardAmple hc s₀ A) :
    yoneda.obj (ampleModel hA) ≅ ((s₀).baseChange A.T).1 :=
  haveI := isRepresentable_baseChange_of_picardAmple hA
  yoneda.mapIso (integerNormIso _) ≪≫ ((s₀).baseChange A.T).1.reprW

/-- The scheme model represents `X_T`, as an isomorphism of algebraic spaces. -/
def ampleModelSpaceIso {A : Space.PicardObject s₀} (hA : Space.picardAmple hc s₀ A) :
    schemeSpace (ampleModel hA) ≅ (s₀).baseChange A.T :=
  ObjectProperty.isoMk _ (ampleModelIso hA)

/-- The underlying morphism of presheaves of `AlgebraicGeometry.ampleModelSpaceIso`. -/
@[simp]
theorem ampleModelSpaceIso_hom_hom {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    (ampleModelSpaceIso hA).hom.hom = (ampleModelIso hA).hom :=
  rfl

/-- The underlying morphism of presheaves of the inverse of
`AlgebraicGeometry.ampleModelSpaceIso`. -/
@[simp]
theorem ampleModelSpaceIso_inv_hom {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    (ampleModelSpaceIso hA).inv.hom = (ampleModelIso hA).inv :=
  rfl

/-- The structure morphism `Z ⟶ T` of the scheme model, as a morphism of the site over the
terminal scheme. -/
def ampleModelHom {A : Space.PicardObject s₀} (hA : Space.picardAmple hc s₀ A) :
    ampleModel hA ⟶ (schemeOverIntegers B).obj A.T.left.left :=
  yoneda.preimage ((ampleModelIso hA).hom ≫ (Space.baseChangeInclusion (s₀).f A.T).hom ≫
    yoneda.map (integerNormIso A.T.left).inv)

/-- The Yoneda image of the structure morphism of the scheme model is the base change `X_T ⟶ T`
up to the two identifications. -/
theorem yoneda_map_ampleModelHom {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    yoneda.map (ampleModelHom hA) = (ampleModelIso hA).hom ≫
      (Space.baseChangeInclusion (s₀).f A.T).hom ≫ yoneda.map (integerNormIso A.T.left).inv :=
  yoneda.map_preimage _

/-- The structure morphism of the scheme model is, as a morphism of algebraic spaces, the base
change `X_T ⟶ T` up to the two identifications. -/
theorem schemeSpaceMap_ampleModelHom {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    schemeSpaceMap (ampleModelHom hA) = (ampleModelSpaceIso hA).hom ≫
      Space.baseChangeInclusion (s₀).f A.T ≫
        ((schemeSpaceFunctor B integerBase B.contains_integerBase).mapIso
          (integerNormIso A.T.left)).inv :=
  ObjectProperty.hom_ext _ (yoneda_map_ampleModelHom hA)

/-- A property of morphisms of algebraic spaces which is stable under base change holds for the
structure morphism of the scheme model as soon as it holds for the base change `X_T ⟶ T`. -/
theorem prop_schemeSpaceMap_ampleModelHom
    {P : MorphismProperty (AlgebraicSpaces B integerBase B.contains_integerBase)}
    (hP : P.IsStableUnderBaseChange) {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) (h : P (Space.baseChangeInclusion (s₀).f A.T)) :
    P (schemeSpaceMap (ampleModelHom hA)) := by
  have := hP.respectsIso
  rw [schemeSpaceMap_ampleModelHom]
  exact (MorphismProperty.cancel_left_of_respectsIso P (ampleModelSpaceIso hA).hom _).2
    ((MorphismProperty.cancel_right_of_respectsIso P (Space.baseChangeInclusion (s₀).f A.T)
      ((schemeSpaceFunctor B integerBase B.contains_integerBase).mapIso
        (integerNormIso A.T.left)).inv).2 h)

/-- The structure morphism of the scheme model is of finite presentation, flat and proper as a
morphism of algebraic spaces: it is the base change `X_T ⟶ T`, up to isomorphisms. -/
theorem properFlat_yoneda_map_ampleModelHom {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    Space.IsFinitePresentation B integerBase B.contains_integerBase
        (yoneda.map (ampleModelHom hA)) ∧
      Space.IsFlat B integerBase B.contains_integerBase (yoneda.map (ampleModelHom hA)) ∧
      Space.IsProper B integerBase B.contains_integerBase (yoneda.map (ampleModelHom hA)) := by
  obtain ⟨h1, h2, h3⟩ := properFlat_baseChangeInclusion A.T
  exact ⟨prop_schemeSpaceMap_ampleModelHom
      (Space.isFinitePresentation_isStableUnderBaseChange B integerBase B.contains_integerBase)
      hA h1,
    prop_schemeSpaceMap_ampleModelHom
      (Space.isFlat_isStableUnderBaseChange B integerBase B.contains_integerBase) hA h2,
    prop_schemeSpaceMap_ampleModelHom
      (Space.isProper_isStableUnderBaseChange B integerBase B.contains_integerBase) hA h3⟩

/-! ### The polarization of the scheme model -/

/-- The module of a relatively ample object on the algebraic space represented by its scheme
model: the inverse image of `L` along `yoneda Z ≅ X_T`. -/
abbrev ampleModelModule {A : Space.PicardObject s₀} (hA : Space.picardAmple hc s₀ A) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj (ampleModel hA))
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase _) :=
  (Space.modulePullback B integerBase B.contains_integerBase (ampleModelSpaceIso hA).hom).obj
    A.lineBundle

/-- The module of a relatively ample object on its scheme model is quasi-coherent. -/
theorem isQuasicoherentOnSite_ampleModelModule {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) : (ampleModelModule hA).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isInvertible _ A.lineBundle A.invertible

/-- **The polarization of the scheme model**: the module of a relatively ample object read on the
scheme `Z` with `yoneda Z ≅ X_T`. -/
abbrev ampleModelLineBundle {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA)).Modules :=
  Space.representedZariskiModule B integerBase B.contains_integerBase (ampleModel hA)
    (ampleModelModule hA)

/-- The module Stacks 0D31 reads on the scheme model is the polarization of the scheme model. -/
def baseChangeModuleIsoAmpleModelLineBundle {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    Space.baseChangeModule B integerBase B.contains_integerBase A.lineBundle (ampleModel hA)
        (ampleModelIso hA).hom ≅ ampleModelLineBundle hA :=
  Space.restrictToChartSchemeIdEtaleChartIso B integerBase B.contains_integerBase
    (ampleModel hA) (ampleModelModule hA)

/-- The square testing Stacks 0D31 at the scheme model: `yoneda Z ⟶ X_T` over the identification
of `T` with its normal form, two of whose sides are isomorphisms. -/
theorem isPullback_ampleModel {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    IsPullback (ampleModelIso hA).hom (yoneda.map (ampleModelHom hA))
      (Space.baseChangeInclusion (s₀).f A.T).hom (yoneda.mapIso (integerNormIso A.T.left)).hom :=
  @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (Iso.isIso_hom _) ⟨by
    have e1 : yoneda.map (integerNormIso A.T.left).inv ≫ yoneda.map (integerNormIso A.T.left).hom =
        𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [yoneda_map_ampleModelHom]
    exact ((Category.assoc _ _ _).trans (congrArg (fun k => (ampleModelIso hA).hom ≫ k)
      ((Category.assoc _ _ _).trans ((congrArg (fun k =>
        (Space.baseChangeInclusion (s₀).f A.T).hom ≫ k) e1).trans
          (Category.comp_id _))))).symm⟩

/-- The polarization of the scheme model is invertible and relatively ample for the structure
morphism of the scheme model: this is the clause of Stacks 0D31 at the square
`AlgebraicGeometry.isPullback_ampleModel`. -/
theorem exists_isRelativelyAmple_ampleModelLineBundle {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) :
    ∃ hL : Stacks.Ample.IsInvertibleModule
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
        (ampleModelLineBundle hA),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map (ampleModelHom hA))
        (ampleModelLineBundle hA) hL := by
  obtain ⟨hL, hamp⟩ := hA.2 _ _ _ _ _ (isPullback_ampleModel hA)
  have := hL
  have hL' : Stacks.Ample.IsInvertibleModule
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
      (ampleModelLineBundle hA) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
      (baseChangeModuleIsoAmpleModelLineBundle hA)
  exact ⟨hL', (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    (baseChangeModuleIsoAmpleModelLineBundle hA)).mp hamp⟩

/-- **The polarized family of a relatively ample object** of `Picardstack_{X₀/V₀}`: the scheme
model `Z ⟶ T` of `X_T ⟶ T`, polarized by the reading of `L` on `Z` (Stacks 0D1M). -/
def amplePolarizedFamily {A : Space.PicardObject s₀}
    (hA : Space.picardAmple hc s₀ A) : PolarizedFamily B where
  base := A.T.left.left
  total := (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA)
  toBase := B.inclusion.map (ampleModelHom hA).left
  proper := Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase
    B.contains_integerBase _ (properFlat_yoneda_map_ampleModelHom hA).2.2
  flat := Space.flat_of_isFlat_yoneda B integerBase B.contains_integerBase _ _ _
    (properFlat_yoneda_map_ampleModelHom hA).2.1
  finitePresentation := finitePresentation_toScheme_map_of_yoneda_map _
    (properFlat_yoneda_map_ampleModelHom hA).1 (properFlat_yoneda_map_ampleModelHom hA).2.2
  lineBundle := ampleModelLineBundle hA
  invertible := (exists_isRelativelyAmple_ampleModelLineBundle hA).1
  relativelyAmple := (exists_isRelativelyAmple_ampleModelLineBundle hA).2

end Model

end AlgebraicGeometry

end
