module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveLeftDerived
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution

/-!
# Total left derived functors along an exact functor preserving projectives

Let `Φ : A ⥤ A'` be an exact functor of abelian categories which preserves projective objects,
let `F : A ⥤ B` and `F' : A' ⥤ B` be additive functors with `Φ ⋙ F' ≅ F`, and let `LF` and `LF'`
be total left derived functors of `F` and `F'` on the unbounded derived categories, both computed
pointwise. Then for every object `X` of `A`

`LF(X) ≅ LF'(Φ X)`,

naturally in `X`, where both objects are placed in degree zero. This is the comparison by which a
derived functor computed on one model of an abelian category is read on another; the case in
view is an equivalence `Φ`, for instance the comparison of presheaves on a category with
presheaves on its small model `CategoryTheory.AsSmall`.

## The comparison

The functor `Φ.mapDerivedCategory ⋙ LF'` comes with a natural transformation
`Qh ⋙ (Φ.mapDerivedCategory ⋙ LF') ⟶ F.mapHomotopyCategory ⋙ Qh`, the comparison of `LF'` read
at `Φ`-images (`Stacks.Homology.precompLeftDerivedComparison`), so the universal property of the
left derived functor `LF` produces a natural transformation
`Φ.mapDerivedCategory ⋙ LF' ⟶ LF` (`Stacks.Homology.precompLeftDerivedLift`). At a bounded above
complex `P` of projectives it is invertible: the comparisons of `LF` at `P` and of `LF'` at `Φ P`
are invertible because both complexes are K-projective, `Φ` preserving projectives and zero
objects. An object placed in degree zero has a resolution by such a complex
(`Stacks.ProjectiveResolutionLemma.statement3`), which gives the invertibility there.

## Main definitions

* `Stacks.Homology.precompLeftDerivedComparison` and `Stacks.Homology.precompLeftDerivedLift`.
* `Stacks.Homology.singleLeftDerivedPrecompIso`: `LF'(Φ X) ≅ LF(X)`, naturally in `X`.

## Main results

* `Stacks.Homology.isIso_precompLeftDerivedLift_app_single`: the comparison is invertible at
  every object placed in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.Homology

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B] [Abelian A] [Abelian A']
  [Abelian B] [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B]
  (Φ : A ⥤ A') [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {F : A ⥤ B} {F' : A' ⥤ B} [F.Additive] [F'.Additive] (τ : Φ ⋙ F' ≅ F)
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (LF' : DerivedCategory A' ⥤ DerivedCategory B)
  (α' : DerivedCategory.Qh ⋙ LF' ⟶
    F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- **The comparison of `LF'` read at `Φ`-images**: the natural transformation
`Qh ⋙ (Φ.mapDerivedCategory ⋙ LF') ⟶ F.mapHomotopyCategory ⋙ Qh` obtained from the comparison
`α'` of `LF'`, the identification of `Φ.mapDerivedCategory` as the functor induced by
`Φ.mapHomotopyCategory`, and the isomorphism `Φ ⋙ F' ≅ F`. -/
def precompLeftDerivedComparison :
    DerivedCategory.Qh ⋙ Φ.mapDerivedCategory ⋙ LF' ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫ whiskerRight Φ.mapDerivedCategoryFactorsh.hom LF' ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft (Φ.mapHomotopyCategory _) α' ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Functor.mapHomotopyCategoryCompIso τ (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh

variable [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The comparison `Φ.mapDerivedCategory ⋙ LF' ⟶ LF`**, produced by the universal property of
the left derived functor `LF` from `Stacks.Homology.precompLeftDerivedComparison`. -/
def precompLeftDerivedLift : Φ.mapDerivedCategory ⋙ LF' ⟶ LF :=
  LF.leftDerivedLift α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
    (precompLeftDerivedComparison Φ τ LF' α')

variable [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  [LF'.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]

/-- **The comparison is invertible at a K-projective complex whose image is K-projective.** Its
composite with the comparison `α` of `LF` is `Stacks.Homology.precompLeftDerivedComparison`,
whose only factor that is not an isomorphism of functors is the comparison `α'` of `LF'` at the
image complex; both comparisons are invertible at K-projective complexes. -/
lemma isIso_precompLeftDerivedLift_app_of_isKProjective (P : CochainComplex A ℤ)
    [P.IsKProjective]
    [CochainComplex.IsKProjective ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)] :
    IsIso ((precompLeftDerivedLift Φ τ LF α LF' α').app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))) := by
  have hα := isIso_leftDerivedCounit_app_of_isKProjective LF α P
  have hfac := LF.leftDerived_fac_app α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
    (precompLeftDerivedComparison Φ τ LF' α')
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)
  have hβ : IsIso ((precompLeftDerivedComparison Φ τ LF' α').app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) := by
    have : IsIso (α'.app ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))) :=
      isIso_leftDerivedCounit_app_of_isKProjective LF' α'
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    dsimp only [precompLeftDerivedComparison, NatTrans.comp_app, whiskerRight_app,
      whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  have hβ' : IsIso ((precompLeftDerivedLift Φ τ LF α LF' α').app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) := by
    rw [precompLeftDerivedLift, hfac]
    exact hβ
  exact IsIso.of_isIso_comp_right _ (α.app ((HomotopyCategory.quotient A _).obj P))

variable [EnoughProjectives A] [Φ.PreservesProjectiveObjects]

/-- **The comparison is invertible at every object placed in degree zero.** Such an object has a
resolution by a bounded above complex of projectives, which is K-projective, and whose image
under `Φ` is again a bounded above complex of projectives. -/
lemma isIso_precompLeftDerivedLift_app_single (X : A) :
    IsIso ((precompLeftDerivedLift Φ τ LF α LF' α').app
      (DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X))) := by
  obtain ⟨R, -⟩ := ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) inferInstance
  have : ∀ n, Projective (R.complex.X n) := R.projective
  have : CochainComplex.IsStrictlyLE R.complex 0 := R.boundedAbove
  have : QuasiIso R.α := R.quasiIso
  have : R.complex.IsKProjective := CochainComplex.isKProjective_of_projective R.complex 0
  have : ∀ n, Projective (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.complex).X n) :=
    fun n => Φ.projective_obj_of_projective (R.projective n)
  have : CochainComplex.IsKProjective
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.complex) :=
    CochainComplex.isKProjective_of_projective _ 0
  have h := isIso_precompLeftDerivedLift_app_of_isKProjective Φ τ LF α LF' α' R.complex
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      R.complex) ≅
        DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) :=
    (DerivedCategory.quotientCompQhIso A).app R.complex ≪≫ asIso (DerivedCategory.Q.map R.α)
  have : IsIso ((Φ.mapDerivedCategory ⋙ LF').map e.hom ≫
      (precompLeftDerivedLift Φ τ LF α LF' α').app
        (DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X))) := by
    rw [(precompLeftDerivedLift Φ τ LF α LF' α').naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Φ.mapDerivedCategory ⋙ LF').map e.hom) _

/-- **`LF'(Φ X) ≅ LF(X)`, naturally in `X`**, both objects placed in degree zero: the comparison
`Stacks.Homology.precompLeftDerivedLift` restricted to objects placed in degree zero, where it is
invertible, composed with the identification of `Φ.mapDerivedCategory` on such objects. -/
def singleLeftDerivedPrecompIso :
    Φ ⋙ HomologicalComplex.single A' (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙ LF' ≅
      HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙ LF :=
  have : ∀ X : A, IsIso ((whiskerLeft (HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙
      DerivedCategory.Q) (precompLeftDerivedLift Φ τ LF α LF' α')).app X) :=
    fun X => isIso_precompLeftDerivedLift_app_single Φ τ LF α LF' α' X
  have : IsIso (whiskerLeft (HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙
      DerivedCategory.Q) (precompLeftDerivedLift Φ τ LF α LF' α')) :=
    NatIso.isIso_of_isIso_app _
  isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ)
        0).symm DerivedCategory.Q ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
        Φ.mapDerivedCategoryFactors.symm ≪≫ (Functor.associator _ _ _).symm) LF' ≪≫
    asIso (whiskerLeft (HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q)
      (precompLeftDerivedLift Φ τ LF α LF' α'))

end Stacks.Homology
