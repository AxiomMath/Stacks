module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.WedgeLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections

/-!
# The wedge product with forms of degree zero

Let `f : X ⟶ S` be a morphism of schemes. The sheaf `Ω^0_{X/S}` of forms of degree zero is the
structure sheaf, by its unit `1`, and under this identification the wedge product
`Ω^0_{X/S} ⊗ Ω^b_{X/S} ⟶ Ω^b_{X/S}` is the left unitor `𝒪_X ⊗ Ω^b_{X/S} ≅ Ω^b_{X/S}`: `1` is a
left identity of the algebra of forms. Hence the wedge product with forms of degree zero is an
isomorphism, also in `D(𝒪_X)`, where `Ω^0_{X/S}` placed in degree zero is K-flat, and after any
shift.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mulSheaf_zero_comp_eqToHom`: the wedge product with forms of
  degree zero is the left unitor.
* `AlgebraicGeometry.Scheme.Hom.isIso_formsDerivedWedge_zero`: `Ω^0 ⊗^L Ω^b ⟶ Ω^b` is an
  isomorphism in `D(𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.isIso_formsDerivedWedgeShift_zero`: so is
  `Ω^0 ⊗^L Ω^b[n] ⟶ Ω^c[n]` for `0 + b = c`.
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The identification `Ω^0_{X/S} ≅ 𝒪_X` of forms of degree zero with the structure sheaf. -/
abbrev formsZeroIsoUnit :
    relativeDifferentialForms f 0 ≅
      SheafOfModules.unit (Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf) :=
  (SheafOfModules.algebras _ (relativeDifferentials f)).exteriorPieceZeroIsoUnit

/-- **The wedge product with forms of degree zero is the left unitor**: under
`Ω^0_{X/S} ≅ 𝒪_X`, the product `Ω^0 ⊗ Ω^b ⟶ Ω^{0+b} = Ω^b` is `𝒪_X ⊗ Ω^b ≅ Ω^b`, since a form
`r · 1` of degree zero acts on `η` as `r η`. -/
theorem mulSheaf_zero_comp_eqToHom (b : ℤ) :
    (relativeDifferentialFormsAlgebra f).mulSheaf 0 b ≫
        eqToHom (congrArg (relativeDifferentialFormsAlgebra f).piece (zero_add b)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
          (formsZeroIsoUnit f).hom).app (relativeDifferentialForms f b) ≫
        (AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace
          (relativeDifferentialForms f b)).hom := by
  refine (PresheafOfModules.tensorSheaf_hom_ext (J := Opens.grothendieckTopology X)
    (Osharp := X.sheaf) (F := relativeDifferentialForms f 0) (G := relativeDifferentialForms f b)
    (Q := relativeDifferentialForms f b) fun U x y => ?_).symm
  have h1 := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    (Osharp := X.sheaf) (F := relativeDifferentialForms f 0) (G := relativeDifferentialForms f b)
    (formsZeroIsoUnit f).hom (𝟙 (relativeDifferentialForms f b)) U x y
  have e1 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
      (formsZeroIsoUnit f).hom).app (relativeDifferentialForms f b) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
        (formsZeroIsoUnit f).hom).app (relativeDifferentialForms f b) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
          _).map (𝟙 (relativeDifferentialForms f b)) :=
    (Category.comp_id _).symm.trans (congrArg (fun k => _ ≫ k)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        _).map_id (relativeDifferentialForms f b)).symm)
  have h2 := AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso_hom_toTensorSheafSection
    X.toRingedSpace (relativeDifferentialForms f b) U ((formsZeroIsoUnit f).hom.val.app U x) y
  have h3 := (SheafOfModules.algebras _ (relativeDifferentials f)).exteriorPieceZeroIsoUnit_smul_one
    U x _ rfl
  have h4 := ((relativeDifferentialFormsAlgebra f).mul 0 b).map_smul_left U
    ((formsZeroIsoUnit f).hom.val.app U x) ((relativeDifferentialFormsAlgebra f).one.eval U) y
  set E := (eqToHom (congrArg (relativeDifferentialFormsAlgebra f).piece (zero_add b))).val.app U
  have h5 : E (((relativeDifferentialFormsAlgebra f).mul 0 b).app U
      ((relativeDifferentialFormsAlgebra f).one.eval U) y) = y :=
    eq_of_heq ((Stacks.TensorSheafWorld.heq_eqToHom_val_app _ (zero_add b) U _).trans
      ((relativeDifferentialFormsAlgebra f).one_mul b U y))
  have h1' := (congrArg (fun k => k.val.app U ((PresheafOfModules.tensorSheafUnit
    (relativeDifferentialForms f 0) (relativeDifferentialForms f b)).app U (x ⊗ₜ y))) e1).trans h1
  refine ((congrArg ((AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace
    (relativeDifferentialForms f b)).hom.val.app U) h1').trans h2).trans ?_
  refine Eq.trans ?_ (congrArg E (SheafOfModules.GradedAlgebra.mulSheaf_unit _ 0 b U x y)).symm
  refine Eq.trans ?_
    (congrArg (fun z => E (((relativeDifferentialFormsAlgebra f).mul 0 b).app U z y)) h3)
  refine Eq.trans ?_ (congrArg E h4).symm
  exact (congrArg _ h5).symm.trans (E.hom.map_smul _ _).symm

/-- **The wedge product with forms of degree zero is an isomorphism**
`Ω^0_{X/S} ⊗ Ω^b_{X/S} ≅ Ω^{0+b}_{X/S}`. -/
theorem isIso_mulSheaf_zero (b : ℤ) :
    IsIso ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b) := by
  have h : IsIso ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b ≫
      eqToHom (congrArg (relativeDifferentialFormsAlgebra f).piece (zero_add b))) :=
    (congrArg IsIso (mulSheaf_zero_comp_eqToHom f b)).mpr
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).mapIso
          (formsZeroIsoUnit f)).app (relativeDifferentialForms f b) ≪≫
        AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace
          (relativeDifferentialForms f b)).isIso_hom
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (eqToHom (congrArg
    (relativeDifferentialFormsAlgebra f).piece (zero_add b)))
    (eqToIso (congrArg (relativeDifferentialFormsAlgebra f).piece (zero_add b))).isIso_hom h

/-- `Ω^0_{X/S}` placed in degree zero is a K-flat complex: it is isomorphic to `𝒪_X` placed in
degree zero. -/
theorem kFlat_single_formsZero :
    Stacks.SheafOfModules.KFlat.KFlat X.sheaf
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (relativeDifferentialForms f 0)) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso _ (Stacks.SheafOfModules.isKFlat_single_unit X.sheaf)
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).mapIso (formsZeroIsoUnit f).symm)

/-- **The wedge product `Ω^0_{X/S} ⊗^L Ω^b_{X/S} ⟶ Ω^b_{X/S}` is an isomorphism in `D(𝒪_X)`**:
`Ω^0_{X/S}` in degree zero is K-flat, so the derived tensor product is the ordinary one, on which
the wedge product is an isomorphism. -/
theorem isIso_formsDerivedWedge_zero (b : ℤ) : IsIso (formsDerivedWedge f 0 b) := by
  have h₁ : IsIso ((canonicalDerivedTensorProduct X.sheaf).toTensor
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (relativeDifferentialForms f 0))
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (relativeDifferentialForms f b))) :=
    (congrArg IsIso ((canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonLeft _ _
      (kFlat_single_formsZero f))).mpr (Iso.isIso_hom _)
  have hm : IsIso ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map
      ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_mulSheaf_zero f b)
  have h₂ : IsIso (DerivedCategory.Q.map ((HomologicalComplex.mapBifunctorSingleSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) _ _ 0 0).hom ≫
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map
        ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hm)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- **The shifted wedge product `Ω^0_{X/S} ⊗^L Ω^b_{X/S}[n] ⟶ Ω^c_{X/S}[n]`, `0 + b = c`, is an
isomorphism in `D(𝒪_X)`.** -/
theorem isIso_formsDerivedWedgeShift_zero (n b c : ℤ) (h : 0 + b = c) :
    IsIso (formsDerivedWedgeShift f n 0 b c h) := by
  subst h
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right (formsInDegreeZero f 0)
  have h₂ : ∀ p : formsInDegreeZero f (0 + b) = formsInDegreeZero f (0 + b),
      IsIso ((formsDerivedWedge f 0 b ≫ eqToHom p)⟦n⟧') := fun p => by
    have e : formsDerivedWedge f 0 b ≫ eqToHom p = formsDerivedWedge f 0 b :=
      (congrArg _ (eqToHom_refl _ _)).trans (Category.comp_id _)
    exact (congrArg (fun k => IsIso ((shiftFunctor _ n).map k)) e).mpr
      (@Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_formsDerivedWedge_zero f b))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom (((((derivedTensorProductFunctor
    X.sheaf).obj (formsInDegreeZero f 0)).commShiftIso n).app (formsInDegreeZero f b)))) (h₂ _)

end AlgebraicGeometry.Scheme.Hom

end
