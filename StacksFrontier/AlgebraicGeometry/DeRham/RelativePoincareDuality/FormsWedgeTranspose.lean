module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.WedgeDegreeZero
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingIsoCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DerivedCurryKFlatSingles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandDerivedHom
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange

/-!
# The derived wedge product of differential forms is a perfect pairing

Let `f : X ⟶ S` be smooth of relative dimension `a + b`. The wedge product
`Ω^a_{X/S} ⊗^L Ω^b_{X/S} ⟶ Ω^{a+b}_{X/S}` in `D(𝒪_X)` determines, under the tensor–internal-Hom
adjunction of [Stacks, Tag 08J8], an isomorphism

`Ω^a_{X/S} ≅ R𝓗om(Ω^b_{X/S}, Ω^{a+b}_{X/S})`,

and so does its shift `Ω^a ⊗^L Ω^b[n] ⟶ Ω^{a+b}[n]`. This is the step of the proof of
[Stacks, Tag 0G8I] that reads the sheaf-level duality `Ω^p ≅ SheafHom(Ω^{n-p}, Ω^n)` in the
derived category, so that [Stacks, Tag 0G81] applies.

The proof identifies the map determined by the derived wedge product with the wedge pairing
`Ω^a ⟶ SheafHom(Ω^b, Ω^{a+b})` of `AlgebraicGeometry.Scheme.Hom.formsWedgeHom` followed by the
comparison of the internal Hom complex with the derived internal Hom: the forms are flat, so
the derived tensor product is computed by the total tensor complex, and on a local pure tensor
`ω ⊗ η` the transpose of the wedge pairing is `ω ∧ η`.

## Implementation notes

The objects are written `Q(Ω^a[0])` with the sheaves placed in degree zero by
`AlgebraicGeometry.RingedSite.sgl`, the spelling of the tensor–internal-Hom adjunction
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`. That
adjunction is a concrete term which the elaborator unfolds when it compares two of its
applications at different spellings of one object, so the proof keeps to this spelling and the
statement at `formsInDegreeZero` is obtained by rewriting along the equality of the two
bijections, which holds by `rfl`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_homEquiv_symm_formsDerivedWedge`, and
  `AlgebraicGeometry.Scheme.Hom.isIso_homEquiv_symm_formsDerivedWedge_sgl` in the spelling of
  the adjunction
* `AlgebraicGeometry.Scheme.Hom.isIso_homEquiv_symm_commShiftIso_comp_shift`

## References

* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.RingedSite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The ringed site of opens of `X`. -/
local notation "𝒳" => Stacks.SheafOfModules.ringedSite X.sheaf

/-- **The wedge pairing as a map into the internal Hom complex**: `Ω^a ⟶ SheafHom(Ω^b, Ω^{a+b})`,
`ω ↦ (η ↦ ω ∧ η)`, between the sheaves placed in degree zero. -/
def formsWedgeComplexHom (a b : ℤ) :
    sgl 𝒳 (relativeDifferentialForms f a) ⟶
      (sheafHomComplex 𝒳
        (sgl 𝒳 (relativeDifferentialForms f b))
        (sgl 𝒳 (relativeDifferentialForms f (a + b)))).obj :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (formsWedgeHom f a b) ≫
    (sheafHomComplexSingleIso 𝒳
      (relativeDifferentialForms f b) (relativeDifferentialForms f (a + b))).inv

/-- The wedge product `Tot(Ω^a[0] ⊗ Ω^b[0]) ⟶ Ω^{a+b}[0]` of complexes. -/
def formsWedgeTotal (a b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex (𝒳).O).obj
      (sgl 𝒳 (relativeDifferentialForms f a))).obj
      (sgl 𝒳 (relativeDifferentialForms f b)) ⟶
      sgl 𝒳 (relativeDifferentialForms f (a + b)) :=
  (HomologicalComplex.mapBifunctorSingleSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) _ _ 0 0).hom ≫
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map
      ((relativeDifferentialFormsAlgebra f).mulSheaf a b)

/-- The wedge product of complexes in degree zero is the wedge product of sheaves. -/
theorem ι_comp_formsWedgeTotal_f (a b : ℤ) :
    HomologicalComplex.ιMapBifunctor
        (sgl 𝒳 (relativeDifferentialForms f a))
        (sgl 𝒳 (relativeDifferentialForms f b))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ)
        0 0 (0 + 0) rfl ≫ (formsWedgeTotal f a b).f (0 + 0) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (relativeDifferentialForms f a)).hom).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj _).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (relativeDifferentialForms f b)).hom ≫
        (relativeDifferentialFormsAlgebra f).mulSheaf a b ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 + 0)
            (relativeDifferentialForms f (a + b))).inv := by
  have h1 := HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
    (relativeDifferentialForms f a) (relativeDifferentialForms f b) 0 0
  have h2 := HomologicalComplex.single_map_f_self (V := X.Modules) (c := ComplexShape.up ℤ)
    (j := 0 + 0) ((relativeDifferentialFormsAlgebra f).mulSheaf a b)
  refine (congrArg (_ ≫ ·) ((HomologicalComplex.comp_f _ _ _).trans
    (congrArg (_ ≫ ·) h2))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ?_)))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (Iso.inv_hom_id _)).trans
    (Category.id_comp _))

/-- **The transpose of the wedge pairing under the currying of [Stacks, Tag 0A90] is the wedge
product.** On a local pure tensor `ω ⊗ η` both sides are `ω ∧ η`. -/
theorem curryHomEquiv_formsWedgeComplexHom (a b : ℤ) :
    curryHomEquiv 𝒳 _ _ _ (formsWedgeComplexHom f a b) =
      formsWedgeTotal f a b := by
  refine tensorComplexSection_hom_ext 𝒳 _ _ _
    fun c t r htr W x y => ?_
  rw [curryHomEquiv_val_app_tensorComplexSection 𝒳
    _ _ _ _ c t r htr (by omega)]
  by_cases ht : t = 0
  · by_cases hr : r = 0
    · subst ht hr
      obtain rfl : c = 0 + 0 := htr.symm
      refine (applyHomSection_sheafHomComplexSingleIso_inv 𝒳
        _ _ W ((formsWedgeHom f a b).val.app (op W) x) y _).trans ?_
      refine (formsWedgeHom_eval f a b W x y).trans ?_
      have hι := congrArg (fun φ => φ.val.app (op W)
        (moduleTensorSection 𝒳 (op W)
          (relativeDifferentialForms f a) (relativeDifferentialForms f b) x y))
        (ι_comp_formsWedgeTotal_f f a b)
      refine Eq.trans ?_ hι.symm
      have k1 := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
        (Osharp := X.sheaf)
        (F := ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
          (relativeDifferentialForms f a)).X 0)
        (G := ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
          (relativeDifferentialForms f b)).X 0)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (relativeDifferentialForms f a)).hom
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (relativeDifferentialForms f b)).hom
        (op W) x y
      have k2 := SheafOfModules.GradedAlgebra.mulSheaf_unit (relativeDifferentialFormsAlgebra f) a b
        (op W) x y
      exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 + 0)
        (relativeDifferentialForms f (a + b))).inv.val.app (op W))
        ((congrArg (((relativeDifferentialFormsAlgebra f).mulSheaf a b).val.app (op W)) k1).trans
          k2)).symm
    · subst ht
      obtain rfl := eq_zero_of_isZero_sgl_X 𝒳 _ hr y
      refine (map_zero _).trans ?_
      rw [tensorComplexSection_zero_right, map_zero]
  · obtain rfl := eq_zero_of_isZero_sgl_X 𝒳 _ ht x
    refine (congrArg (fun z => applyHomSection _ _ W t r c (by omega) z y) (map_zero _)).trans ?_
    refine Eq.trans ?_ ((congrArg (((formsWedgeTotal f a b).f c).val.app (op W))
      (tensorComplexSection_zero_left 𝒳 t r c htr y)).trans
      (map_zero _)).symm
    have h := applyHomSection_add_left 𝒳
      (sheafHomComplex 𝒳
        (sgl 𝒳 (relativeDifferentialForms f b))
        (sgl 𝒳 (relativeDifferentialForms f (a + b))))
      W t r c (by omega) 0 0 y
    rw [add_zero] at h
    exact left_eq_add.mp h


/-- For `f` smooth, `Ω^p_{X/S}` placed in degree zero is K-flat: it is a flat module. -/
theorem kFlat_single_relativeDifferentialForms [Smooth f] (p : ℕ) :
    Stacks.SheafOfModules.KFlat.KFlat X.sheaf
      (sgl 𝒳 (relativeDifferentialForms f (p : ℤ))) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.sheaf _
    (AlgebraicGeometry.ProperSmoothDeRham.isFlat_relativeDifferentialForms f p) 0

/-- The derived wedge product is the canonical map to the total tensor complex followed by the
wedge product of complexes. -/
theorem formsDerivedWedge_eq_toTensor_comp (a b : ℤ) :
    formsDerivedWedge f a b = (canonicalDerivedTensorProduct X.sheaf).toTensor
      (sgl 𝒳 (relativeDifferentialForms f a))
      (sgl 𝒳 (relativeDifferentialForms f b)) ≫
        DerivedCategory.Q.map (formsWedgeTotal f a b) := rfl

/-- **The derived wedge product is a perfect pairing**: for `f` smooth of relative dimension
`a + b`, the map `Ω^a_{X/S} ⟶ R𝓗om(Ω^b_{X/S}, Ω^{a+b}_{X/S})` determined by
`Ω^a ⊗^L Ω^b ⟶ Ω^{a+b}` under the tensor–internal-Hom adjunction of [Stacks, Tag 08J8] is an
isomorphism. It is the wedge pairing `Ω^a ≅ SheafHom(Ω^b, Ω^{a+b})`, an isomorphism by
`AlgebraicGeometry.Scheme.Hom.isIso_formsWedgeHom`, followed by the comparison
`SheafHom(Ω^b, -) ⟶ RSheafHom(Ω^b, -)`, an isomorphism as `Ω^b` is finite locally free
([Stacks, Tag 08JH]). -/
theorem isIso_homEquiv_symm_formsDerivedWedge_sgl (a b : ℕ) [SmoothOfRelativeDimension (a + b) f] :
    IsIso (((Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        𝒳).homEquiv
          (DerivedCategory.Q.obj (sgl 𝒳
            (relativeDifferentialForms f (a : ℤ))))
          (DerivedCategory.Q.obj (sgl 𝒳
            (relativeDifferentialForms f (b : ℤ))))
          (DerivedCategory.Q.obj (sgl 𝒳
            (relativeDifferentialForms f ((a : ℤ) + (b : ℤ)))))).symm
      (formsDerivedWedge f a b)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (a + b) f
  have h := AlgebraicGeometry.RingedSite.homEquiv_Q_map_comp_strictlyPerfectHomComparison
    𝒳
    (sgl 𝒳 (relativeDifferentialForms f (a : ℤ)))
    (sgl 𝒳 (relativeDifferentialForms f (b : ℤ)))
    (sgl 𝒳
      (relativeDifferentialForms f ((a : ℤ) + (b : ℤ))))
    (kFlat_single_relativeDifferentialForms f a)
    (kFlat_single_relativeDifferentialForms f b) (formsWedgeComplexHom f a b)
  have h2 := (h.trans (congrArg (fun φ => _ ≫ DerivedCategory.Q.map φ)
    (curryHomEquiv_formsWedgeComplexHom f a b))).trans
      (formsDerivedWedge_eq_toTensor_comp f a b).symm
  have h3 := (Equiv.symm_apply_eq _).2 h2.symm
  have hσ := strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand
    𝒳
    (derivedInternalHomOfBifunctor 𝒳) 0
    (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree 𝒳
      (relativeDifferentialForms f (b : ℤ))
      (hA := ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f b))
    (sgl 𝒳 (relativeDifferentialForms f ((a : ℤ) + (b : ℤ))))
  have hu : IsIso (DerivedCategory.Q.map (formsWedgeComplexHom f a b)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_formsWedgeHom f a b)) (Iso.isIso_inv _))
  have hfin := @IsIso.comp_isIso _ _ _ _ _ _ _ hu hσ
  rw [h3]
  exact hfin

/-- **The derived wedge product is a perfect pairing**, with the objects written as
`AlgebraicGeometry.Scheme.Hom.formsInDegreeZero`: for `f` smooth of relative dimension `a + b`,
`Ω^a_{X/S} ⟶ R𝓗om(Ω^b_{X/S}, Ω^{a+b}_{X/S})` determined by the wedge product is an
isomorphism. -/
theorem isIso_homEquiv_symm_formsDerivedWedge (a b : ℕ) [SmoothOfRelativeDimension (a + b) f] :
    IsIso (((Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        𝒳).homEquiv (formsInDegreeZero f a) (formsInDegreeZero f b)
          (formsInDegreeZero f ((a : ℤ) + (b : ℤ)))).symm (formsDerivedWedge f a b)) := by
  have e : (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        𝒳).homEquiv (formsInDegreeZero f a) (formsInDegreeZero f b)
          (formsInDegreeZero f ((a : ℤ) + (b : ℤ))) =
      (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        𝒳).homEquiv (DerivedCategory.Q.obj (sgl 𝒳 (relativeDifferentialForms f a)))
          (DerivedCategory.Q.obj (sgl 𝒳 (relativeDifferentialForms f b)))
          (DerivedCategory.Q.obj (sgl 𝒳 (relativeDifferentialForms f ((a : ℤ) + (b : ℤ))))) :=
    rfl
  rw [e]
  exact isIso_homEquiv_symm_formsDerivedWedge_sgl f a b

/-- **Shifting the second factor and the target of a perfect pairing**: if
`w : P ⊗^L B ⟶ M` determines an isomorphism `P ≅ R𝓗om(B, M)`, so does the shifted pairing
`P ⊗^L B[n] ≅ (P ⊗^L B)[n] ⟶ M[n]`, for any tensor–internal-Hom adjunction `DX` on `D(𝒪_X)`. -/
theorem isIso_homEquiv_symm_commShiftIso_comp_shift
    (DX : TensorHomAdjunction
      (derivedTensorProductFunctor (𝒳).O)
      (𝒳).derivedSheafHomBifunctor) (n : ℤ)
    (P B M : Stacks.DerivedTensor.RingedSite.DerivedModules
      (𝒳).O)
    (w : ((derivedTensorProductFunctor (𝒳).O).obj P).obj B ⟶ M)
    (hw : IsIso ((DX.homEquiv P B M).symm w)) :
    letI := (canonicalDerivedTensorProduct (𝒳).O).commShift_right P
    IsIso ((DX.homEquiv P (B⟦n⟧) (M⟦n⟧)).symm
      ((((derivedTensorProductFunctor (𝒳).O).obj P).commShiftIso
        n).hom.app B ≫ w⟦n⟧')) := by
  let := (canonicalDerivedTensorProduct (𝒳).O).commShift_right P
  have hw' := (TensorHomAdjunction.isIso_homEquiv_symm_iff
    DX _).mp hw
  refine (TensorHomAdjunction.isIso_homEquiv_symm_iff
    DX _).mpr fun Z => ?_
  let := (canonicalDerivedTensorProduct (𝒳).O).commShift_right Z
  have key : (fun v : Z ⟶ P =>
      ((derivedTensorProductFunctor (𝒳).O).map v).app (B⟦n⟧) ≫
        (((derivedTensorProductFunctor (𝒳).O).obj P).commShiftIso
          n).hom.app B ≫ w⟦n⟧') =
      (fun k => (((derivedTensorProductFunctor (𝒳).O).obj
          Z).commShiftIso n).hom.app B ≫ k) ∘ (fun k => k⟦n⟧') ∘
        (fun v : Z ⟶ P =>
          ((derivedTensorProductFunctor (𝒳).O).map v).app B ≫
            w) := by
    funext v
    have := (canonicalDerivedTensorProduct
      (𝒳).O).commShift₂.commShift_map v
    have hc := NatTrans.shift_app_comm
      ((derivedTensorProductFunctor (𝒳).O).map v) n B
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)))
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (hw' Z))
  · exact (Iso.app (((derivedTensorProductFunctor (𝒳).O).obj
      Z).commShiftIso n) B).homFromEquiv.symm.bijective
  · exact ⟨(shiftFunctor _ n).map_injective, (shiftFunctor _ n).map_surjective⟩

end AlgebraicGeometry.Scheme.Hom

end
