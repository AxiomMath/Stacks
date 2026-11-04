module

public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerCurveCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1783.CurveLift
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackDescent
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsLifting
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# First-order lifts of polarized curves

Let `T ⊂ T'` be a first-order thickening of affine schemes, `(X ⟶ T, ℒ)` a polarized curve over
`T` whose family of curves is identified with the restriction to `T` of a family of curves
`X' ⟶ T'`. Then `X'` is a scheme (Stacks 05ZR: it is a thickening of the scheme `X`), it is proper
over `T'` with fibres of dimension at most one (the fibres are homeomorphic to those of `X ⟶ T`),
and `ℒ` lifts to an invertible module `ℒ'` on `X'` ample relative to `T'`
(`AlgebraicGeometry.C1783.exists_lift_isRelativelyAmple_of_isFirstOrderThickening`,
the core of Stacks 0DPJ). So `(X' ⟶ T', ℒ')` is a polarized curve over `T'` restricting to the
given one, compatibly with the identifications of families of curves: the projection
`PolarizedCurves ⟶ 𝒞urves` has the first-order lifting property of Stacks 06D0.

## Main definitions

* `AlgebraicGeometry.C1783.polarizedFamilyOfRepresentableTotal`: the
  polarized family of a family of curves whose total space is a scheme, polarized by a relatively
  ample invertible module.
* `AlgebraicGeometry.C1783.forgetPolarizedFamilyOfRepresentableTotalIso`:
  its family of algebraic spaces is the family of curves.
* `AlgebraicGeometry.C1783.homToPolarizedFamilyOfRepresentableTotal`:
  the morphism into it from a polarized family over a morphism of families of algebraic spaces.

## Main results

* `AlgebraicGeometry.C1783.exists_firstOrderLift_polarizedCurve`: the
  first-order lift of a polarized curve.
* `AlgebraicGeometry.C1783.hasFirstOrderObjectLifts_polarizedCurvesToCurves`:
  `PolarizedCurves ⟶ 𝒞urves` solves every first-order lifting problem (Stacks 06D0).

## Implementation notes

The source (Stacks 0DQ0, via Stacks 0DPJ) deforms the pair (curve, polarization) by deformation
theory of the invertible module alone, the curve being given. Here the given curve over `T'` is an
algebraic space, and it is first shown to be a scheme by the closed-immersion form of Stacks 07VV.
The fibre-dimension hypothesis of the lifting statement is checked on `X ⟶ T` by the étale-chart
form of the relative dimension (Stacks 04NC on the identity charts) and transported along the
homeomorphisms of the thickening square.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1783

section Site

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Every object of the big fppf site of `Spec ℤ` is its underlying scheme read over `Spec ℤ`. -/
theorem schemeOverIntegers_obj_left (V : BigFppfOver B integerBase hZ) :
    (schemeOverIntegers B).obj V.left = V :=
  congrArg Over.mk ((isTerminal_obj_specULiftZ B hZ).hom_ext _ _)

/-- A morphism of the big fppf site of `Spec ℤ` is the morphism of underlying schemes read over
`Spec ℤ`, up to the identifications `AlgebraicGeometry.C1783.schemeOverIntegers_obj_left`. -/
private theorem schemeOverIntegers_map_left {V W : BigFppfOver B integerBase hZ} (g : V ⟶ W) :
    (schemeOverIntegers B).map g.left =
      eqToHom (schemeOverIntegers_obj_left V) ≫ g ≫
        eqToHom (schemeOverIntegers_obj_left W).symm := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  rfl

/-- `AlgebraicGeometry.C1783.schemeOverIntegers_map_left` for a
morphism out of a scheme read over `Spec ℤ`. -/
private theorem schemeOverIntegers_map_left' {X : B.Schemes} {V : BigFppfOver B integerBase hZ}
    (g : (schemeOverIntegers B).obj X ⟶ V) :
    (schemeOverIntegers B).map g.left = g ≫ eqToHom (schemeOverIntegers_obj_left V).symm := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  rfl

end Site

section Site

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A property of a morphism of schemes holds for the underlying morphism of schemes of every
morphism lying over it. -/
private theorem prop_toScheme_map_of_isHomLift {𝒳 : Type*} [Category 𝒳]
    (q : 𝒳 ⥤ BigFppfOver B integerBase hZ) {P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Prop}
    {R S : BigFppfOver B integerBase hZ} (f : R ⟶ S) {x y : 𝒳} (φ : x ⟶ y) [q.IsHomLift f φ]
    (hf : P ((BigFppfOver.toScheme B integerBase hZ).map f)) :
    P ((BigFppfOver.toScheme B integerBase hZ).map (q.map φ)) := by
  have h1 := IsHomLift.domain_eq q f φ
  have h2 := IsHomLift.codomain_eq q f φ
  subst h1 h2
  rwa [← IsHomLift.eq_of_isHomLift q f φ]

/-- `AlgebraicGeometry.C1783.schemeOverIntegers_map_left`, with the
identifications moved to the other side. -/
private theorem eqToHom_comp_eq_schemeOverIntegers_map_left_comp
    {V W : BigFppfOver B integerBase hZ} (g : V ⟶ W) :
    eqToHom (schemeOverIntegers_obj_left V) ≫ g =
      (schemeOverIntegers B).map g.left ≫ eqToHom (schemeOverIntegers_obj_left W) := by
  rw [schemeOverIntegers_map_left, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- A morphism lies over `g` for a composite functor as soon as its image lies over `g`. -/
theorem isHomLift_comp_of_isHomLift {𝒳 𝒴 𝒞 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒞]
    (F : 𝒳 ⥤ 𝒴) (P : 𝒴 ⥤ 𝒞) {R S : 𝒞} (g : R ⟶ S) {x y : 𝒳} (φ : x ⟶ y)
    (h : P.IsHomLift g (F.map φ)) : (F ⋙ P).IsHomLift g φ :=
  IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq P g (F.map φ)) (IsHomLift.codomain_eq P g (F.map φ))
    (IsHomLift.fac' P g (F.map φ))

/-- A morphism whose image is an `eqToHom` lies over an identity. -/
private theorem isHomLift_id_of_map_eq_eqToHom {𝒳 𝒞 : Type*} [Category 𝒳] [Category 𝒞] (q : 𝒳 ⥤ 𝒞)
    {x y : 𝒳} (φ : x ⟶ y) (h : q.obj x = q.obj y) (hφ : q.map φ = eqToHom h) :
    q.IsHomLift (𝟙 (q.obj y)) φ :=
  IsHomLift.of_fac' _ _ _ h rfl (by simp [hφ])

end Site

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

/-! ### A family of curves with scheme total space and a polarization -/

section RepresentableTotal

variable {B hZ} {C' : CurveFamily B hZ} (hrepC : C'.total.obj.IsRepresentable)

/-- The structure morphism of the scheme representing the total space of a family of curves. -/
abbrev representableTotalToBase :
    (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hrepC) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj C'.base :=
  (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase hrepC)

/-- The scheme representing the total space of a family of curves is proper over the base. -/
instance : IsProper (representableTotalToBase hrepC) :=
  CurveFamily.isProper_toScheme_map_totalSiteToBase hrepC

/-- The scheme representing the total space of a family of curves is flat over the base. -/
instance : Flat (representableTotalToBase hrepC) :=
  CurveFamily.flat_toScheme_map_totalSiteToBase hrepC

/-- The scheme representing the total space of a family of curves is locally of finite
presentation over the base. -/
instance : LocallyOfFinitePresentation (representableTotalToBase hrepC) :=
  CurveFamily.locallyOfFinitePresentation_toScheme_map_totalSiteToBase hrepC

variable (L' : ((BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hrepC)).Modules)
  [hL'inv : Stacks.Ample.IsInvertibleModule _ L']
  (hL'amp : Stacks.RelativeAmple.IsRelativelyAmple (representableTotalToBase hrepC) L')

/-- **The polarized family of a family of curves with scheme total space**, polarized by a
relatively ample invertible module on the scheme. -/
def polarizedFamilyOfRepresentableTotal : PolarizedFamily B where
  base := C'.base.left
  total := (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hrepC)
  toBase := representableTotalToBase hrepC
  proper := inferInstance
  flat := inferInstance
  finitePresentation := FinitePresentation.mk inferInstance inferInstance inferInstance
  lineBundle := L'
  invertible := hL'inv
  relativelyAmple := hL'amp

/-- The structure morphism of the polarized family, read over `Spec ℤ`, is the structure morphism
of the scheme representing the total space. -/
private theorem structureMapOverIntegers_polarizedFamilyOfRepresentableTotal :
    (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp).structureMapOverIntegers =
      eqToHom (schemeOverIntegers_obj_left _) ≫ CurveFamily.totalSiteToBase hrepC ≫
        eqToHom (schemeOverIntegers_obj_left C'.base).symm :=
  schemeOverIntegers_map_left (CurveFamily.totalSiteToBase hrepC)

/-- The comparison of total spaces underlying
`AlgebraicGeometry.C1783.forgetPolarizedFamilyOfRepresentableTotalIso`. -/
def polarizedFamilyOfRepresentableTotalTotalIso :
    yoneda.obj ((schemeOverIntegers B).obj
      (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp).totalObj) ≅ C'.total.obj :=
  yoneda.mapIso (eqToIso (schemeOverIntegers_obj_left _)) ≪≫ CurveFamily.totalSiteIso hrepC

/-- The comparison of total spaces is compatible with the structure morphisms. -/
theorem polarizedFamilyOfRepresentableTotalTotalIso_hom_comp :
    (polarizedFamilyOfRepresentableTotalTotalIso hrepC L' hL'amp).hom ≫ C'.toBase.hom =
      yoneda.map (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp).structureMapOverIntegers ≫
        yoneda.map (eqToHom (schemeOverIntegers_obj_left C'.base)) := by
  have h4 : eqToHom (schemeOverIntegers_obj_left _) ≫ CurveFamily.totalSiteToBase hrepC =
      (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp).structureMapOverIntegers ≫
        eqToHom (schemeOverIntegers_obj_left C'.base) :=
    eqToHom_comp_eq_schemeOverIntegers_map_left_comp (CurveFamily.totalSiteToBase hrepC)
  exact (Category.assoc _ _ _).trans
    ((congrArg (yoneda.map (eqToHom (schemeOverIntegers_obj_left _)) ≫ ·)
      (CurveFamily.yoneda_map_totalSiteToBase hrepC).symm).trans
      ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map h4).trans (yoneda.map_comp _ _))))

/-- The comparison of the families of algebraic spaces, in the comma category. -/
def forgetPolarizedFamilyOfRepresentableTotalCommaIso :
    ((forgetPolarization B).obj (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp)).obj.obj ≅
      ((curvesToCartesianProperFlat B hZ).obj C').obj.obj :=
  Comma.isoMk (ObjectProperty.isoMk _ (polarizedFamilyOfRepresentableTotalTotalIso hrepC L' hL'amp))
    (eqToIso (schemeOverIntegers_obj_left C'.base))
    (polarizedFamilyOfRepresentableTotalTotalIso_hom_comp hrepC L' hL'amp)

/-- **The family of algebraic spaces of the polarized family is the family of curves.** -/
def forgetPolarizedFamilyOfRepresentableTotalIso :
    (forgetPolarization B).obj (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp) ≅
      (curvesToCartesianProperFlat B hZ).obj C' :=
  WideSubcategory.isoMk
    (ObjectProperty.isoMk _ (forgetPolarizedFamilyOfRepresentableTotalCommaIso hrepC L' hL'amp))
    (Functor.IsStronglyCartesian.of_isIso (spacesProjection B integerBase hZ)
      ((spacesProjection B integerBase hZ).map
        (forgetPolarizedFamilyOfRepresentableTotalCommaIso hrepC L' hL'amp).hom)
      (forgetPolarizedFamilyOfRepresentableTotalCommaIso hrepC L' hL'amp).hom)
    (Functor.IsStronglyCartesian.of_isIso (spacesProjection B integerBase hZ)
      ((spacesProjection B integerBase hZ).map
        (forgetPolarizedFamilyOfRepresentableTotalCommaIso hrepC L' hL'amp).inv)
      (forgetPolarizedFamilyOfRepresentableTotalCommaIso hrepC L' hL'amp).inv)

/-- The comparison of families of algebraic spaces is vertical. -/
private theorem isHomLift_forgetPolarizedFamilyOfRepresentableTotalIso_hom :
    (cartesianProperFlatProjection B integerBase hZ).IsHomLift (𝟙 C'.base)
      (forgetPolarizedFamilyOfRepresentableTotalIso hrepC L' hL'amp).hom :=
  isHomLift_id_of_map_eq_eqToHom _ _ (schemeOverIntegers_obj_left C'.base) rfl

/-- The inverse comparison of families of algebraic spaces is vertical. -/
private theorem isHomLift_forgetPolarizedFamilyOfRepresentableTotalIso_inv :
    (cartesianProperFlatProjection B integerBase hZ).IsHomLift (𝟙 C'.base)
      (forgetPolarizedFamilyOfRepresentableTotalIso hrepC L' hL'amp).inv :=
  have : (cartesianProperFlatProjection B integerBase hZ).IsHomLift (Iso.refl C'.base).hom
      (forgetPolarizedFamilyOfRepresentableTotalIso hrepC L' hL'amp).hom :=
    isHomLift_forgetPolarizedFamilyOfRepresentableTotalIso_hom hrepC L' hL'amp
  IsHomLift.inv_lift_inv (cartesianProperFlatProjection B integerBase hZ) (Iso.refl C'.base) _

variable {p : PolarizedFamily B}
  (ψ : (forgetPolarization B).obj p ⟶ (curvesToCartesianProperFlat B hZ).obj C')

/-- The morphism of schemes from the total space of a polarized family to the scheme representing
the total space of a family of curves, underlying a morphism of families of algebraic spaces. -/
abbrev totalMapToRepresentableTotal :
    p.total ⟶ (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hrepC) :=
  (BigFppfOver.toScheme B integerBase hZ).map
    (Yoneda.fullyFaithful.preimage (ψ.1.hom.left.hom ≫ (CurveFamily.totalSiteIso hrepC).inv))

/-- The square of `AlgebraicGeometry.C1783.totalMapToRepresentableTotal`
is cartesian. -/
theorem isPullback_totalMapToRepresentableTotal :
    IsPullback (totalMapToRepresentableTotal hrepC ψ) p.toBase (representableTotalToBase hrepC)
      ((BigFppfOver.toScheme B integerBase hZ).map ψ.1.hom.right) := by
  have hpb :=
    PolarizedFamily.isPullback_of_forgetPolarization_hom B ψ (CurveFamily.totalSiteIso hrepC)
  have ht : Yoneda.fullyFaithful.preimage ((CurveFamily.totalSiteIso hrepC).hom ≫ C'.toBase.hom) =
      CurveFamily.totalSiteToBase hrepC :=
    yoneda.map_injective (by
      rw [Functor.FullyFaithful.map_preimage]
      exact (CurveFamily.yoneda_map_totalSiteToBase hrepC).symm)
  have e1 : representableTotalToBase hrepC = (BigFppfOver.toScheme B integerBase hZ).map
      (Yoneda.fullyFaithful.preimage ((CurveFamily.totalSiteIso hrepC).hom ≫ C'.toBase.hom)) :=
    congrArg (BigFppfOver.toScheme B integerBase hZ).map ht.symm
  rw [e1]
  exact hpb

variable {L' hL'amp} in
/-- The morphism of polarized families into the polarized family of a family of curves with
scheme total space, over a morphism of families of algebraic spaces. -/
def homToPolarizedFamilyOfRepresentableTotal
    (eL : (Scheme.Modules.pullback (totalMapToRepresentableTotal hrepC ψ)).obj L' ≅ p.lineBundle) :
    p ⟶ polarizedFamilyOfRepresentableTotal hrepC L' hL'amp where
  baseMap := ψ.1.hom.right.left
  totalMap := totalMapToRepresentableTotal hrepC ψ
  cartesian := isPullback_totalMapToRepresentableTotal hrepC ψ
  lineBundleIso := eL

variable {L' hL'amp} in
/-- The morphism of polarized families recovers the morphism of families of algebraic spaces. -/
private theorem forget_map_homToPolarizedFamilyOfRepresentableTotal_comp
    (eL : (Scheme.Modules.pullback (totalMapToRepresentableTotal hrepC ψ)).obj L' ≅ p.lineBundle) :
    (forgetPolarization B).map
        (homToPolarizedFamilyOfRepresentableTotal hrepC ψ (hL'amp := hL'amp) eL) ≫
      (forgetPolarizedFamilyOfRepresentableTotalIso hrepC L' hL'amp).hom = ψ := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · apply ObjectProperty.hom_ext
    let jV :=
      Yoneda.fullyFaithful.preimage (ψ.1.hom.left.hom ≫ (CurveFamily.totalSiteIso hrepC).inv)
    have hV := schemeOverIntegers_obj_left (CurveFamily.totalSite hrepC)
    have hJ' : PolarizedFamily.totalMapOverIntegers
        (homToPolarizedFamilyOfRepresentableTotal hrepC ψ (hL'amp := hL'amp) eL) =
        jV ≫ eqToHom hV.symm :=
      schemeOverIntegers_map_left' jV
    have k1 : yoneda.map (jV ≫ eqToHom hV.symm) ≫ yoneda.map (eqToHom hV) = yoneda.map jV := by
      rw [← yoneda.map_comp, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    have k2 : yoneda.map jV ≫ (CurveFamily.totalSiteIso hrepC).hom = ψ.1.hom.left.hom :=
      (congrArg (· ≫ (CurveFamily.totalSiteIso hrepC).hom)
        (Yoneda.fullyFaithful.map_preimage _)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (ψ.1.hom.left.hom ≫ ·) (CurveFamily.totalSiteIso hrepC).inv_hom_id).trans
            (Category.comp_id _)))
    exact (congrArg (fun k => yoneda.map k ≫
        (yoneda.map (eqToHom hV) ≫ (CurveFamily.totalSiteIso hrepC).hom)) hJ').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (CurveFamily.totalSiteIso hrepC).hom) k1).trans k2))
  · have hC := schemeOverIntegers_obj_left C'.base
    have h1 : (schemeOverIntegers B).map ψ.1.hom.right.left = ψ.1.hom.right ≫ eqToHom hC.symm :=
      schemeOverIntegers_map_left' ψ.1.hom.right
    exact (congrArg (· ≫ eqToHom hC) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (ψ.1.hom.right ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans
        (Category.comp_id _)))

end RepresentableTotal

/-- An object of PolarizedCurves: a polarized family, a family of curves and an identification of
their families of algebraic spaces. -/
abbrev PolarizedCurveObj :=
  TwoFibreProductOver (polarizedProjectionOver B hZ) (curvesProjectionOver B hZ)
    (cartesianProperFlatProjection B integerBase hZ) (forgetPolarizationUp B hZ)
    (curvesToCartesianProperFlat B hZ)

/-- The last step of the first-order lift: once the polarization has been lifted, assemble the
object of PolarizedCurves over the thickening and the morphism to it. -/
private theorem exists_polarizedCurveObj_lift (W : PolarizedCurveObj B hZ) (C' : CurveFamily B hZ)
    (i : W.base ⟶ C'.base) (a : W.y ⟶ C') (ha : (curvesProjectionOver B hZ).IsHomLift i a)
    (hψ : (cartesianProperFlatProjection B integerBase hZ).IsHomLift i
      (W.iso.hom ≫ (curvesToCartesianProperFlat B hZ).map a))
    (hrepC : C'.total.obj.IsRepresentable)
    (L' : ((BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hrepC)).Modules)
    [Stacks.Ample.IsInvertibleModule _ L']
    (hL'amp : Stacks.RelativeAmple.IsRelativelyAmple (representableTotalToBase hrepC) L')
    (eL : (Scheme.Modules.pullback (totalMapToRepresentableTotal hrepC
      (W.iso.hom ≫ (curvesToCartesianProperFlat B hZ).map a))).obj L' ≅
        (ULiftHom.objDown.{u + 1, u + 1} W.x).lineBundle) :
    ∃ (W' : PolarizedCurveObj B hZ) (_ : W'.base = C'.base) (b : W ⟶ W') (c : W'.y ⟶ C'),
      (TwoFibreProductOver.structureFunctor _ _ _ _ _).IsHomLift i b ∧
        (curvesProjectionOver B hZ).IsHomLift (𝟙 C'.base) c ∧ b.b ≫ c = a := by
  let ψ : (forgetPolarization B).obj (ULiftHom.objDown.{u + 1, u + 1} W.x) ⟶
      (curvesToCartesianProperFlat B hZ).obj C' :=
    W.iso.hom ≫ (curvesToCartesianProperFlat B hZ).map a
  let fpol := homToPolarizedFamilyOfRepresentableTotal hrepC ψ (hL'amp := hL'amp) eL
  have hw0 := forget_map_homToPolarizedFamilyOfRepresentableTotal_comp hrepC ψ (hL'amp := hL'amp) eL
  have hfpol : (cartesianProperFlatProjection B integerBase hZ).IsHomLift i
      ((forgetPolarization B).map fpol) := by
    rw [(Iso.eq_comp_inv _).2 hw0]
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ (cartesianProperFlatProjection B integerBase hZ)
      _ _ _ _ _ i ψ hψ C'.base _
      (isHomLift_forgetPolarizedFamilyOfRepresentableTotalIso_inv hrepC L' hL'amp)
  let W' : PolarizedCurveObj B hZ :=
    { base := C'.base
      x := ULiftHom.objUp.{u + 1, u + 1} (polarizedFamilyOfRepresentableTotal hrepC L' hL'amp)
      y := C'
      hx := schemeOverIntegers_obj_left C'.base
      hy := rfl
      iso := forgetPolarizedFamilyOfRepresentableTotalIso hrepC L' hL'amp
      vertical := isHomLift_forgetPolarizedFamilyOfRepresentableTotalIso_hom hrepC L' hL'amp }
  let b : W ⟶ W' :=
    { hbase := i
      a := ULift.up fpol
      b := a
      ha := isHomLift_comp_of_isHomLift (forgetPolarizationUp B hZ)
          (cartesianProperFlatProjection B integerBase hZ) i (ULift.up fpol) hfpol
      hb := ha
      w := hw0 }
  exact ⟨W', rfl, b, 𝟙 C', IsHomLift.map (TwoFibreProductOver.structureFunctor _ _ _ _ _) b,
    IsHomLift.id rfl, Category.comp_id a⟩

/-- **First-order lifts of polarized curves.** Let `W` be an object of PolarizedCurves over `U`
(a polarized curve together with an identification of its family of algebraic spaces with a
family of curves `W.y`), and `a : W.y ⟶ C'` a morphism of families of curves over a first-order
thickening `i : U ⟶ U'` of affine objects of the site. Then there are an object `W'` of
PolarizedCurves over `U'` with family of curves `C'` and a morphism `W ⟶ W'` over `i` whose
morphism of families of curves is `a`. -/
private theorem exists_firstOrderLift_polarizedCurve (W : PolarizedCurveObj B hZ)
    (C' : CurveFamily B hZ)
    (i : W.base ⟶ C'.base) (hU : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj W.base))
    (hU' : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj C'.base))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B integerBase hZ).map i))
    (a : W.y ⟶ C') (ha : (curvesProjectionOver B hZ).IsHomLift i a) :
    ∃ (W' : PolarizedCurveObj B hZ) (_ : W'.base = C'.base) (b : W ⟶ W') (c : W'.y ⟶ C'),
      (TwoFibreProductOver.structureFunctor _ _ _ _ _).IsHomLift i b ∧
        (curvesProjectionOver B hZ).IsHomLift (𝟙 C'.base) c ∧ b.b ≫ c = a := by
  let p : PolarizedFamily B := ULiftHom.objDown.{u + 1, u + 1} W.x
  let ψ : (forgetPolarization B).obj p ⟶ (curvesToCartesianProperFlat B hZ).obj C' :=
    W.iso.hom ≫ (curvesToCartesianProperFlat B hZ).map a
  have := W.vertical
  have ha' : (cartesianProperFlatProjection B integerBase hZ).IsHomLift i
      ((curvesToCartesianProperFlat B hZ).map a) :=
    IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq (curvesProjectionOver B hZ) i a)
      (IsHomLift.codomain_eq (curvesProjectionOver B hZ) i a)
      (IsHomLift.fac' (curvesProjectionOver B hZ) i a)
  have hψ : (cartesianProperFlatProjection B integerBase hZ).IsHomLift i ψ :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ (cartesianProperFlatProjection B integerBase hZ) _ _ _
      W.base W.iso.hom W.vertical _ _ i _ ha'
  have hσ : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map ψ.1.hom.right) :=
    prop_toScheme_map_of_isHomLift (cartesianProperFlatProjection B integerBase hZ)
      (P := fun g => Stacks.Thickenings.IsFirstOrderThickening g) i ψ hi
  have hia : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) :=
    prop_toScheme_map_of_isHomLift (curvesProjectionOver B hZ)
      (P := fun g => Stacks.Thickenings.IsFirstOrderThickening g) i a hi
  let Ftot : CartesianProperFlatSpaces B integerBase hZ ⥤
      ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
    wideSubcategoryInclusion _ ⋙ (isProperFlatSpace B integerBase hZ).ι ⋙ Comma.fst _ _ ⋙
      ObjectProperty.ι _
  have : (Ftot.obj ((forgetPolarizationUp B hZ).obj W.x)).IsRepresentable :=
    (inferInstance : (yoneda.obj ((schemeOverIntegers B).obj p.totalObj)).IsRepresentable)
  have hrepY : W.y.total.obj.IsRepresentable :=
    isRepresentable_of_natIso _ (Ftot.mapIso W.iso)
  have hrepC : C'.total.obj.IsRepresentable :=
    CurveFamily.isRepresentable_total_of_hom a hia.isThickening hrepY
  let J := totalMapToRepresentableTotal hrepC ψ
  let f'' := representableTotalToBase hrepC
  have hpb' := isPullback_totalMapToRepresentableTotal hrepC ψ
  have hJ : Stacks.Thickenings.IsFirstOrderThickening J :=
    Stacks.Thickenings.isFirstOrderThickening_of_isPullback hpb' hσ
  have hdim : ∀ t' : (BigFppfOver.toScheme B integerBase hZ).obj C'.base,
      topologicalKrullDim (f''.fiber t') ≤ 1 := fun t' ↦ by
    exact_mod_cast C1590Private.CurveFamilyScheme.topologicalKrullDim_fiber_totalSiteToBase_le
      hrepC t'
  let := p.invertible
  have hT : IsAffine (B.inclusion.obj p.base) := by
    rwa [← W.hx] at hU
  have hLample : Stacks.Ample.IsAmple p.total p.lineBundle :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple p.toBase _).1 p.relativelyAmple
  have hLJ : Stacks.RelativeAmple.IsRelativelyAmple (J ≫ f'') p.lineBundle :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (J ≫ f'') _).2 hLample
  obtain ⟨L', hL'inv, ⟨eL⟩, hL'amp⟩ :=
    exists_lift_isRelativelyAmple_of_isFirstOrderThickening J hJ f'' hdim p.lineBundle hLJ
  exact exists_polarizedCurveObj_lift B hZ W C' i a ha hψ hrepC L' hL'amp eL

/-- **`PolarizedCurves ⟶ 𝒞urves` has the first-order lifting property** of Stacks 06D0: every
first-order lifting problem over a thickening of affine objects of the site is solved, in the
form `AlgebraicGeometry.Stack.HasFirstOrderObjectLifts`. -/
theorem hasFirstOrderObjectLifts_polarizedCurvesToCurves :
    Stack.HasFirstOrderObjectLifts B integerBase hZ (polarizedCurvesSquare B hZ h3Z).snd := by
  rintro U U' i hU hU' hi ⟨W, hW⟩ ⟨C', hC'⟩ a ha
  change W.base = U at hW
  change C'.base = U' at hC'
  subst hW hC'
  obtain ⟨W', hW', b, c, hb, hc, hbc⟩ := exists_firstOrderLift_polarizedCurve B hZ W C' i hU hU'
    hi a ha
  exact ⟨⟨W', hW'⟩, b, c, hb, hc, hbc⟩

end AlgebraicGeometry.C1783
