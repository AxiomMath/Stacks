module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomDegreeProjectionEvaluation

/-!
# The differential of the internal Hom complex into a module in degree zero

Let `(C, O)` be a ringed site, `E` a complex of `O`-modules and `M` an `O`-module. For the internal
Hom complex `𝓗om^•(E, M[0])`, whose degree-`n` term has a single component
`𝓗om(E^{-n}, M)`, the differential is `(-1)^{n+1}` times precomposition with the differential
`E^{-(n+1)} ⟶ E^{-n}`, on evaluations of local sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Evaluation of a degree-`n` section of `𝓗om^•(E, M[0])` over `U` on a section of `E^p`
over `V ⟶ U`, for `p + n = 0`, with value in `M`. -/
abbrev evalSingle (U V : X.C) (i : V ⟶ U) (n p : ℤ) (hp : p + n = 0)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X p).val.obj (op V)) : M.val.obj (op V) :=
  (eqToHom (by rw [hp]; rfl : ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) 0).obj M).X (p + n) = M)).val.app (op V)
    (applyHomSectionOver X (sheafHomComplex X E _) U V i n p (p + n) rfl s y)

/-- The evaluation, read in `M`, does not depend on how the target degree is written. -/
theorem eqToHom_single_applyHomSectionOver (U V : X.C) (i : V ⟶ U) (n p q₁ q₂ : ℤ)
    (h₁ : p + n = q₁) (h₂ : p + n = q₂) (hq₁ : q₁ = 0) (hq₂ : q₂ = 0)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X p).val.obj (op V)) :
    (eqToHom (by rw [hq₁]; rfl : ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj M).X q₁ = M)).val.app (op V)
        (applyHomSectionOver X (sheafHomComplex X E _) U V i n p q₁ h₁ s y) =
      (eqToHom (by rw [hq₂]; rfl : ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj M).X q₂ = M)).val.app (op V)
        (applyHomSectionOver X (sheafHomComplex X E _) U V i n p q₂ h₂ s y) := by
  subst h₁ h₂
  rfl

/-- **The differential of `𝓗om^•(E, M[0])` on evaluations**: evaluating `d s` on a section `y` of
`E^p`, `p + (n + 1) = 0`, is `(-1)^{n+1}` times evaluating `s` on the image of `y` under the
differential of `E`. -/
theorem evalSingle_d (U V : X.C) (i : V ⟶ U) (n p : ℤ) (hp : p + (n + 1) = 0)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X p).val.obj (op V)) :
    evalSingle X E M U V i (n + 1) p hp
        (((sheafHomComplex X E _).obj.d n (n + 1)).val.app (op U) s) y =
      (n + 1).negOnePow •
        evalSingle X E M U V i n (p + 1) (by omega) s ((E.d p (p + 1)).val.app (op V) y) := by
  rw [evalSingle, applyHomSectionOver_differential X _ U V i n p (p + n) (p + (n + 1)) rfl
    (by omega) s y, HomologicalComplex.single_obj_d,
    Stacks.SheafOfModules.zero_val_app_apply, zero_add, Units.smul_def, map_zsmul,
    Units.smul_def]
  exact congrArg _ (eqToHom_single_applyHomSectionOver X E M U V i n (p + 1) _ _ _ rfl
    (by omega) (by omega) s _)

/-- Transport of the target of an internal Hom sheaf along an equality, on evaluations. -/
theorem eqToHom_internalHomSheaf_target_app
    {A B₁ B₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : B₁ = B₂) (U : X.C) (t : (internalHomSheaf X A B₁).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (y : (A.over U).val.obj W) :
    ((eqToHom (congrArg (internalHomSheaf X A) h)).val.app (op U) t).app W y =
      (eqToHom (congrArg
        (fun N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) => N.over U)
        h)).val.app W
        (t.app W y) := by
  subst h
  rfl

/-- Transport along an equality, read on the slice. -/
theorem eqToHom_over_app
    {B₁ B₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : B₁ = B₂)
    (U V : X.C) (i : V ⟶ U) (b : (B₁.over U).val.obj (op (Over.mk i))) :
    (eqToHom (congrArg
        (fun N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) => N.over U)
        h)).val.app (op (Over.mk i)) b = (eqToHom h).val.app (op V) b := by
  subst h
  rfl

/-- Transport of the source of an internal Hom sheaf along an equality, on evaluations. -/
theorem eqToHom_internalHomSheaf_source_app
    {A₁ A₂ B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : A₁ = A₂) (U : X.C) (t : (internalHomSheaf X A₁ B).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (y : (A₂.over U).val.obj W) :
    ((eqToHom (congrArg (fun N => internalHomSheaf X N B) h)).val.app (op U) t).app W y =
      t.app W ((eqToHom (congrArg
        (fun N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) => N.over U)
        h.symm)).val.app W y) := by
  subst h
  rfl

/-- **The collapse of `𝓗om^•(E, M[0])^n` onto `𝓗om(E^{-n}, M)` on evaluations** is the evaluation
of the Hom section. -/
theorem homDegreeIsoSingle_hom_app (n : ℤ) (U V : X.C) (i : V ⟶ U)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X (-n)).val.obj (op V)) :
    ((homDegreeIsoSingle X E M n).hom.val.app (op U) s).app (op (Over.mk i)) y =
      evalSingle X E M U V i n (-n) (by omega) s y := by
  have e : ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
      0).obj M).X (n - n) = M := by rw [sub_self]; rfl
  refine (eqToHom_internalHomSheaf_target_app X e U
    ((homDegreeProjection X E _ n n).val.app (op U) s) (op (Over.mk i)) y).trans ?_
  refine (eqToHom_over_app X e U V i _).trans ?_
  refine (congrArg (fun z => (eqToHom e).val.app (op V) z)
    (homDegreeProjection_app_eq_applyHomSectionOver X E _ n n U V i s y)).trans ?_
  exact eqToHom_single_applyHomSectionOver X E M U V i n (-n) _ _ _ _ (by omega) (by omega) s y

/-- Evaluation does not depend on how the source degree is written. -/
theorem evalSingle_congr (U V : X.C) (i : V ⟶ U) (n p₁ p₂ : ℤ) (h : p₁ = p₂)
    (hp₁ : p₁ + n = 0) (hp₂ : p₂ + n = 0)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X p₁).val.obj (op V)) :
    evalSingle X E M U V i n p₁ hp₁ s y =
      evalSingle X E M U V i n p₂ hp₂ s ((eqToHom (congrArg E.X h)).val.app (op V) y) := by
  subst h
  rfl

/-- A map of single complexes in a degree written as zero, read through the transports to the
modules themselves. -/
theorem eqToHom_single_map_f_val_app
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : M ⟶ N) (q : ℤ)
    (hq : q = 0) (V : X.C)
    (a : (((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
      0).obj M).X q).val.obj (op V)) :
    (eqToHom (by rw [hq]; rfl : ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj N).X q = N)).val.app (op V)
      ((((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
        0).map g).f q).val.app (op V) a) =
      g.val.app (op V) ((eqToHom (by rw [hq]; rfl : ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
        0).obj M).X q = M)).val.app (op V) a) := by
  subst hq
  have key : ∀ {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (h₁ : A = B) (h₂ : B = A) (b : A.val.obj (op V)),
      (eqToHom h₂).val.app (op V) ((eqToHom h₁).val.app (op V) b) = b := by
    intro A B h₁ h₂ b
    subst h₁
    rfl
  rw [HomologicalComplex.single_map_f_self]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom, eqToIso.inv, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  exact key _ _ _

/-- **Evaluation is natural in the target module.** -/
theorem evalSingle_homMap
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : M ⟶ N) (U V : X.C)
    (i : V ⟶ U) (n p : ℤ) (hp : p + n = 0)
    (s : ((sheafHomComplex X E
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M)).obj.X n).val.obj (op U))
    (y : (E.X p).val.obj (op V)) :
    evalSingle X E N U V i n p hp (((homMap X (𝟙 E)
        ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          0).map g)).f n).val.app (op U) s) y =
      g.val.app (op V) (evalSingle X E M U V i n p hp s y) := by
  rw [evalSingle, applyHomSectionOver_homMap]
  exact eqToHom_single_map_f_val_app X g (p + n) hp V _

end AlgebraicGeometry.RingedSite
