module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPushforwardCompShift

/-!
# Single complexes under exact direct images and shifts

The inclusion `Rf_*Ω^n[n] ⟶ Rf_*(Ω^•[2n])` of the top piece of the de Rham complex
(`AlgebraicGeometry.RelativeDualitySituation.topInclusion`) is built from the identification
`Rf_*(F[0]) ≅ (f_*F)[0]` for an exact direct image and from the commutations of single complexes
with the shift. This file relates these to complexes: the identification `(f_*F)[0] ≅ Rf_*(F[0])`
is the comparison of the degreewise direct image with the derived one at `F[0]`, and an additive
functor commutes with the identifications of shifted single complexes.

## Main results

* `DerivedCategory.singleFunctorIsoCompQh_hom_app`,
  `DerivedCategory.singleFunctorIsoCompQh_inv_app`
* `CochainComplex.mapHomologicalComplex_singleShift`
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso_hom_app_eq`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open scoped Stacks.StandardDerivedModel

universe u

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The identification of the single functor of the derived category with that of the homotopy
category followed by `Qh`, at an object. -/
theorem singleFunctorIsoCompQh_hom_app (n : ℤ) (M : C) :
    (singleFunctorIsoCompQh C n).hom.app M =
      (quotientCompQhIso C).inv.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj M) := by
  change (((CochainComplex.singleFunctors C).postcompIsoOfIso (quotientCompQhIso C).symm).hom.hom
      n).app M ≫ (((CochainComplex.singleFunctors C).postcompPostcompIso _ _).inv.hom n).app M = _
  rw [SingleFunctors.postcompIsoOfIso_hom_hom_app, SingleFunctors.postcompPostcompIso_inv_hom_app]
  exact Category.comp_id _

/-- The inverse of `singleFunctorIsoCompQh`, at an object. -/
theorem singleFunctorIsoCompQh_inv_app (n : ℤ) (M : C) :
    (singleFunctorIsoCompQh C n).inv.app M =
      (quotientCompQhIso C).hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj M) := by
  change (((CochainComplex.singleFunctors C).postcompPostcompIso _ _).hom.hom n).app M ≫
    (((CochainComplex.singleFunctors C).postcompIsoOfIso (quotientCompQhIso C).symm).inv.hom
      n).app M = _
  rw [SingleFunctors.postcompIsoOfIso_inv_hom_app, SingleFunctors.postcompPostcompIso_hom_hom_app]
  exact Category.id_comp _

end DerivedCategory

namespace CochainComplex

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasZeroObject A] [HasZeroObject B] (F : A ⥤ B) [F.Additive]

/-- The components of the commutation of single complexes with the shift are identities of
equal objects. -/
theorem singleFunctors_shiftIso_hom_app_f (C : Type*) [Category* C] [Preadditive C]
    [HasZeroObject C] (n a a' : ℤ) (h : n + a = a') (X : C) (i : ℤ) :
    ∃ p, (((singleFunctors C).shiftIso n a a' h).hom.app X).f i = eqToHom p := by
  dsimp only [singleFunctors]
  simp only [NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
    eqToIso.hom]
  refine ⟨?_, trivial⟩
  change (if i + n = a' then X else 0) = (if i = a then X else 0)
  exact if_congr (show i + n = a' ↔ i = a by omega) rfl rfl

/-- The components of the inverse commutation of single complexes with the shift are identities
of equal objects. -/
theorem singleFunctors_shiftIso_inv_app_f (C : Type*) [Category* C] [Preadditive C]
    [HasZeroObject C] (n a a' : ℤ) (h : n + a = a') (X : C) (i : ℤ) :
    ∃ p, (((singleFunctors C).shiftIso n a a' h).inv.app X).f i = eqToHom p := by
  obtain ⟨p, hp⟩ := singleFunctors_shiftIso_hom_app_f C n a a' h X i
  refine ⟨p.symm, ?_⟩
  rw [← cancel_epi (((singleFunctors C).shiftIso n a a' h).hom.app X |>.f i),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id_app, hp]
  simp

/-- In its degree, the commutation of an additive functor with a single complex is an identity of
equal objects. -/
theorem singleMapHomologicalComplex_hom_app_f_eq {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (j i : ℤ) (h : i = j) (X : C) :
    ∃ p, ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) j).hom.app X).f i =
      eqToHom p := by
  subst h
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  refine ⟨by
    change G.obj (if i = i then X else 0) = (if i = i then G.obj X else 0)
    simp, ?_⟩
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]

/-- **An additive functor commutes with the shifted single complexes**: the two identifications
of `F` applied to `M` placed in degree `n` and shifted by `2n` with `F M` placed in degree `n`
and shifted by `2n`, one through `M` placed in degree `0` and shifted by `n`, agree. -/
theorem mapHomologicalComplex_singleShift (M : A) (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((singleFunctors A).shiftIso (2 * n) (-n) n (by omega)).hom.app M ≫
          ((singleFunctors A).shiftIso n (-n) 0 (by omega)).inv.app M) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app M)⟦n⟧' ≫
      ((singleFunctors B).shiftIso n (-n) 0 (by omega)).hom.app (F.obj M) ≫
      ((singleFunctors B).shiftIso (2 * n) (-n) n (by omega)).inv.app (F.obj M) =
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (2 * n)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) n).obj M) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app
        M)⟦2 * n⟧' := by
  ext i
  by_cases hi : i = -n
  · subst hi
    obtain ⟨p₁, h₁⟩ := singleFunctors_shiftIso_hom_app_f A (2 * n) (-n) n (by omega) M (-n)
    obtain ⟨p₂, h₂⟩ := singleFunctors_shiftIso_inv_app_f A n (-n) 0 (by omega) M (-n)
    obtain ⟨p₃, h₃⟩ := singleFunctors_shiftIso_hom_app_f B n (-n) 0 (by omega) (F.obj M) (-n)
    obtain ⟨p₄, h₄⟩ := singleFunctors_shiftIso_inv_app_f B (2 * n) (-n) n (by omega) (F.obj M) (-n)
    obtain ⟨p₅, h₅⟩ := singleMapHomologicalComplex_hom_app_f_eq F 0 (-n + n) (by omega) M
    obtain ⟨p₆, h₆⟩ := singleMapHomologicalComplex_hom_app_f_eq F n (-n + 2 * n) (by omega) M
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, shiftFunctor_map_f']
    rw [h₁, h₂, h₃, h₄, h₅, h₆]
    simp only [eqToHom_map, eqToHom_trans]
    refine (congrArg (_ ≫ ·) (Category.id_comp _)).trans
      (Eq.trans ?_ (Category.id_comp _).symm)
    rw [eqToHom_trans]
  · refine IsZero.eq_of_src ?_ _ _
    refine F.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) _ _ _ ?_)
    dsimp
    omega

end CochainComplex

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

open RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- `(f_*F)[0] ≅ Rf_*(F[0])` is the comparison of the degreewise direct image with the derived
one at `F[0]`, preceded by the commutation of `f_*` with `(-)[0]`. -/
theorem derivedPushforwardSingleIso_hom_app_eq [PreservesFiniteColimits (modulePushforward f)]
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedPushforwardSingleIso f).hom.app M =
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        (modulePushforward f) (ComplexShape.up ℤ) 0).inv.app M) ≫
      Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) := by
  have h1 := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := SheafOfModules.{u} (structureSheafRing Y))
    ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward f) (ComplexShape.up ℤ)
      0).inv.app M)
  rw [derivedPushforwardSingleIso_hom_app, DerivedCategory.singleFunctorIsoCompQh_hom_app,
    DerivedCategory.singleFunctorIsoCompQh_inv_app,
    Functor.mapHomotopyCategorySingleFunctorIso_inv_app,
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ]
  exact ((reassoc_of% h1) _).symm

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

