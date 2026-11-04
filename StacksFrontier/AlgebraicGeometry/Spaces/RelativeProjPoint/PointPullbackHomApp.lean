module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackPointAlgebra

/-!
# The comparison `f^*(g^*𝒜) ⟶ (g ∘ f)^*𝒜` at a scheme point, degreewise

For a morphism `g : X' ⟶ X` of algebraic spaces, a sheaf of graded algebras `𝒜` on the small
étale site of `X` and a scheme point `x : T ⟶ X'`, the comparison
`AlgebraicGeometry.Space.pointPullbackHom` is defined as the adjoint transpose, along the
adjunction of graded algebras of `x`, of the restriction map of pulled-back graded algebras.  This
file shows that in degree `n` it is the composition comparison of Stacks 03LU,
`x^*(g^*𝒜_n) ≅ (g ∘ x)^*𝒜_n`, followed by the transport along `x ≫ g = g ∘ x`.

## Main results

* `AlgebraicGeometry.Space.gradedPullRestriction_app_comp_rfl_eq_homEquiv`: the restriction map
  in degree `n` is the transpose of the composition comparison along the module adjunction.
* `AlgebraicGeometry.Space.gradedAdj_homEquiv_symm_gradedPullRestriction_app_eq`: the transpose
  along the graded adjunction of the restriction map, in degree `n`, is the composition
  comparison followed by the transport.
* `AlgebraicGeometry.Space.pointPullbackHom_app_eq`: the same for
  `AlgebraicGeometry.Space.pointPullbackHom`.

## Implementation notes

The declarations of `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleCoherence` and
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackPointAlgebra` are elaborated in an
environment without `Mathlib.Algebra.Category.Grp.Adjunctions`, those of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonModule` in one with it.
That file declares the instance `(forget AddCommGrpCat).IsRightAdjoint`
(`AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier`), through which instance search proves
`PreservesLimitsOfShape` for `forget AddCommGrpCat` by
`CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint` instead of
`CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`; the sheaf conditions and
sheafifications on the small étale sites, and so the module adjunctions
`RingedToposHom.pullbackAdjPushforwardModulesViaComparison`, are then spelled with other instance
terms.  Comparing the two spellings is costly, so each statement below is elaborated in the
spelling of the lemmas it is proved from: the instance is removed (`attribute [-instance] … in`)
from every statement after `…homEquiv_symm_gradedPullRestriction_app_comp_rfl`, and the two
spellings meet once, in `…gradedAdj_homEquiv_symm_gradedPullRestriction_comp_rfl_app`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P P' X : AlgebraicSpaces B S hS}

/-- **The restriction map of pulled-back graded algebras in degree `n` is the transpose of the
composition comparison of Stacks 03LU** along the module adjunction `φ^* ⊣ φ_*`:
`f^*𝒜_n ⟶ φ_*((f ∘ φ)^*𝒜_n)` corresponds to `φ^*f^*𝒜_n ≅ (f ∘ φ)^*𝒜_n`. -/
theorem gradedPullRestriction_app_comp_rfl_eq_homEquiv (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (gradedPullRestriction φ f (φ ≫ f) rfl A).app n =
      (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv
        ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
          (A.piece n)) ((modulePullback B S hS (φ ≫ f)).obj (A.piece n))
        ((modulePullbackCompIso B S hS φ f).hom.app (A.piece n)) :=
  (gradedPullRestrictionApp_comp_rfl_eq φ f A n).trans
    ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv_unit
      ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
        (A.piece n)) ((modulePullback B S hS (φ ≫ f)).obj (A.piece n))
      ((modulePullbackCompIso B S hS φ f).hom.app (A.piece n))).symm

/-- The transpose back along the module adjunction `φ^* ⊣ φ_*` of the restriction map in degree
`n` is the composition comparison `φ^*f^*𝒜_n ≅ (f ∘ φ)^*𝒜_n`. -/
theorem homEquiv_symm_gradedPullRestriction_app_comp_rfl (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv
        _ _).symm ((gradedPullRestriction φ f (φ ≫ f) rfl A).app n) =
      (modulePullbackCompIso B S hS φ f).hom.app (A.piece n) :=
  (congrArg ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv
      _ _).symm (gradedPullRestriction_app_comp_rfl_eq_homEquiv φ f A n)).trans
    (Equiv.symm_apply_apply _ _)

attribute [-instance] AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier in
/-- `AlgebraicGeometry.Space.gradedAdj_homEquiv_symm_app` at the restriction map of pulled-back
graded algebras along `φ ≫ f = φ ≫ f`: the transpose along the graded adjunction, in degree `n`,
is the transpose along the module adjunction of the degree-`n` component. -/
theorem gradedAdj_homEquiv_symm_gradedPullRestriction_app (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).homEquiv _ _).symm
        (gradedPullRestriction φ f (φ ≫ f) rfl A)).app n =
      ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv
        _ _).symm ((gradedPullRestriction φ f (φ ≫ f) rfl A).app n) :=
  (gradedAdj_homEquiv_symm_app φ (gradedPullRestriction φ f (φ ≫ f) rfl A) n).symm

attribute [-instance] AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier in
/-- **The transpose along the graded adjunction of the restriction map along `φ ≫ f = φ ≫ f` is,
in degree `n`, the composition comparison of Stacks 03LU** `φ^*f^*𝒜_n ≅ (f ∘ φ)^*𝒜_n`. -/
theorem gradedAdj_homEquiv_symm_gradedPullRestriction_comp_rfl_app (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).homEquiv _ _).symm
        (gradedPullRestriction φ f (φ ≫ f) rfl A)).app n =
      (modulePullbackCompIso B S hS φ f).hom.app (A.piece n) :=
  (gradedAdj_homEquiv_symm_gradedPullRestriction_app φ f A n).trans
    (homEquiv_symm_gradedPullRestriction_app_comp_rfl φ f A n)

attribute [-instance] AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier in
/-- **The transpose along the graded adjunction of the restriction map along `h : φ ≫ f = f'`
is, in degree `n`, the composition comparison of Stacks 03LU followed by the transport along
`h`.** -/
theorem gradedAdj_homEquiv_symm_gradedPullRestriction_app_eq (φ : P' ⟶ P) (f : P ⟶ X)
    (f' : P' ⟶ X) (h : φ ≫ f = f')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).homEquiv _ _).symm
        (gradedPullRestriction φ f f' h A)).app n =
      (modulePullbackCompIso B S hS φ f).hom.app (A.piece n) ≫ pullbackTransport (A.piece n) h := by
  subst h
  exact (gradedAdj_homEquiv_symm_gradedPullRestriction_comp_rfl_app φ f A n).trans
    (Category.comp_id _).symm

attribute [-instance] AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier in
/-- `AlgebraicGeometry.Space.pointPullbackHom` is, by definition, the transpose along the graded
adjunction of the point of the restriction map along `x ≫ g = g ∘ x`. -/
theorem pointPullbackHom_eq {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) :
    pointPullbackHom g A T x =
      ((gradedAdj (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
        (Y := smallEtaleRingedTopos B S hS X')
          (smallEtaleRingedToposHom B S hS (pointHom x))).homEquiv _ _).symm
        (gradedPullRestriction (pointHom x) g (pointHom (x ≫ g.hom)) rfl A) :=
  rfl

attribute [-instance] AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier in
/-- **The comparison `x^*(g^*𝒜) ⟶ (g ∘ x)^*𝒜` at a scheme point `x`, in degree `n`**, is the
composition comparison of Stacks 03LU `x^*(g^*𝒜_n) ≅ (x ≫ g)^*𝒜_n` followed by the transport
along `x ≫ g = g ∘ x`. -/
theorem pointPullbackHom_app_eq {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) (n : ℤ) :
    (pointPullbackHom g A T x).app n =
      (modulePullbackCompIso B S hS (pointHom x) g).hom.app (A.piece n) ≫
        pullbackTransport (A.piece n) (rfl : pointHom x ≫ g = pointHom (x ≫ g.hom)) :=
  (congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) (pointPullbackHom_eq g A T x)).trans
    (gradedAdj_homEquiv_symm_gradedPullRestriction_app_eq (pointHom x) g (pointHom (x ≫ g.hom)) rfl
      A n)

end AlgebraicGeometry.Space
