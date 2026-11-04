module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomDegreeProjectionEvaluation

/-!
# The internal Hom complex out of a module in degree zero

Let `(C, O)` be a ringed site, `M` an `O`-module and `F` a complex of `O`-modules. The internal
Hom complex `𝓗om^•(M[0], F)` is the complex obtained by applying `𝓗om(M, -)` to `F` termwise:
its degree-`n` term has the single component `𝓗om(M, F^n)`, and its differential is
postcomposition with the differential of `F`.

## Main definitions

* `AlgebraicGeometry.RingedSite.homDegreeIsoSingleSource`: the degree-`n` term of
  `𝓗om^•(M[0], F)` is `𝓗om(M, F^n)`.
* `AlgebraicGeometry.RingedSite.sheafHomComplexSingleSourceIso`: the isomorphism of complexes
  `𝓗om^•(M[0], F) ≅ 𝓗om(M, -)(F)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (Y : RingedSite.{u, u, u}) [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The only nonvanishing component of a term of the internal Hom complex out of a module in
degree zero** is the one evaluating on that module. -/
theorem isIso_homDegreeProjection_singleSource (n : ℤ) :
    IsIso (homDegreeProjection Y
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj M) F n 0) :=
  Stacks.Limits.isIso_fan_proj_of_isZero (homDegreeIsLimit Y _ F n) 0 fun q hq =>
    internalHomSheaf_isZero_of_isZero Y
      (isZero_single_obj_X (ComplexShape.up ℤ) 0 M (-q) (by omega))

/-- **The degree-`n` term of the internal Hom complex out of a module in degree zero is
`𝓗om(M, F^n)`.** -/
def homDegreeIsoSingleSource (n : ℤ) :
    (sheafHomComplex Y ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj M) F).obj.X n ≅
      (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor Y.J Y.O M).obj (F.X n) :=
  haveI := isIso_homDegreeProjection_singleSource Y M F n
  asIso (homDegreeProjection Y _ F n 0) ≪≫
    (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor Y.J Y.O M).mapIso
      (F.XIsoOfEq (sub_zero n))

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The collapse `homDegreeIsoSingleSource` evaluated on a section of `M`. -/
theorem homDegreeIsoSingleSource_hom_app (n : ℤ) (U V : Y.C) (i : V ⟶ U)
    (s : ((sheafHomComplex Y
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj M) F).obj.X n).val.obj
        (op U))
    (y : M.val.obj (op V)) :
    ((homDegreeIsoSingleSource Y M F n).hom.val.app (op U) s).app (op (Over.mk i)) y =
      (F.XIsoOfEq (sub_zero n)).hom.val.app (op V)
        (applyHomSectionOver Y (sheafHomComplex Y _ F) U V i n (-0) (n - 0) (by omega) s y) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Through the collapse, the differential of `𝓗om^•(M[0], F)` is postcomposition with the
differential of `F`, on evaluations. -/
theorem d_homDegreeIsoSingleSource_hom_app (n : ℤ) (U V : Y.C) (i : V ⟶ U)
    (s : ((sheafHomComplex Y
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj M) F).obj.X n).val.obj
        (op U))
    (y : M.val.obj (op V)) :
    (F.d n (n + 1)).val.app (op V)
        (((homDegreeIsoSingleSource Y M F n).hom.val.app (op U) s).app (op (Over.mk i)) y) =
      ((homDegreeIsoSingleSource Y M F (n + 1)).hom.val.app (op U)
        (((sheafHomComplex Y _ F).obj.d n (n + 1)).val.app (op U) s)).app (op (Over.mk i)) y := by
  have hz : (((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ) 0).obj M).d (-0) (-0 + 1)).val.app (op V) y = 0 := by
    rw [HomologicalComplex.single_obj_d]
    rfl
  have key : F.d (n - 0) (n + 1 - 0) ≫ (F.XIsoOfEq (sub_zero (n + 1))).hom =
      (F.XIsoOfEq (sub_zero n)).hom ≫ F.d n (n + 1) := by
    rw [HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]
  rw [homDegreeIsoSingleSource_hom_app, homDegreeIsoSingleSource_hom_app,
    applyHomSectionOver_differential Y _ U V i n (-0) (n - 0) (n + 1 - 0) (by omega) (by omega)
      s y, hz, show applyHomSectionOver Y (sheafHomComplex Y _ F) U V i n (-0 + 1) (n + 1 - 0)
      (by omega) s 0 = 0 from map_zero _, smul_zero, add_zero]
  exact (congrArg (fun f : F.X (n - 0) ⟶ F.X (n + 1) => f.val.app (op V)
    (applyHomSectionOver Y (sheafHomComplex Y _ F) U V i n (-0) (n - 0) (by omega) s y))
    key).symm

/-- **The internal Hom complex out of a module in degree zero is `𝓗om(M, -)` applied
termwise.** -/
def sheafHomComplexSingleSourceIso :
    (sheafHomComplex Y ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj M) F).obj ≅
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor Y.J Y.O M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F :=
  Hom.isoOfComponents (homDegreeIsoSingleSource Y M F) (by
    rintro n _ rfl
    ext U s
    refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact d_homDegreeIsoSingleSource_hom_app Y M F n U.unop W.unop.left W.unop.hom s y)

end AlgebraicGeometry.RingedSite
