module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIsoNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-!
# The transition map of a derived tensor tower, read through the comparisons of Tag 0BZ2

Let `φ : A ⟶ A'` be a homomorphism of differential graded algebras, `P` a differential graded
`(A, B)`-bimodule, `P'` a differential graded `(A', B)`-bimodule, `τ` a comparison of the plain
tensor functors and `v : X ⟶ X'|_A` a homomorphism of differential graded modules.
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap` identifies the derived tensor
product of `v` followed by the derived comparison of `τ` with the plain homomorphism
`P ⊗_A X ⟶ P' ⊗_{A'} X'`, when `X` and `X'` are orthogonal on the left to the acyclic modules. The
identity behind it does not use that orthogonality: it is a statement about the comparisons
`M ⊗^𝐋 - ⟶ M ⊗ -` of Tag 0BZ2, which exist at every module. This file records it in that form,
so that it applies whenever those comparisons are invertible — for instance for a bimodule that
is the flip of a module orthogonal on the left to the acyclic modules
(`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_flip_of_leftOrthogonal`), at every
module whatsoever.

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorPlainComparison`: the comparison of Tag 0BZ2 at the
  class of a module, followed by the comparison of Tag 09LM.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap_comparison`: the derived
  transition map, read through the comparisons, is the plain transition homomorphism.
* `DifferentialGraded.Bimodule.isIso_towerMap_iff_quasiIso`: when the two comparisons are
  invertible, the derived transition map is an isomorphism exactly when the plain one is a
  quasi-isomorphism.

## References

* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) and
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A A' B : DifferentialGradedAlgebra.{u, u} R}

/-- The comparison `X ⊗^𝐋_A P ⟶ X ⊗_A P` of Tag 0BZ2 at the class of a differential graded
module, followed by the comparison of Tag 09LM of the plain tensor product on homotopy classes. -/
def derivedTensorPlainComparison (P : Bimodule A B) (X : DifferentialGradedModule.{u, u, u} A) :
    (derivedTensorFunctor P).obj ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ⟶
      (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (tensorObj P X)) :=
  (derivedTensorFunctorCounit P).app ((toHomotopyCategory A).obj X) ≫
    (quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient P).inv.app X)

/-- The comparison, as an isomorphism, when the comparison of Tag 0BZ2 is invertible. -/
def derivedTensorPlainIso (P : Bimodule A B) (X : DifferentialGradedModule.{u, u, u} A)
    (h : IsIso ((derivedTensorFunctorCounit P).app ((toHomotopyCategory A).obj X))) :
    (derivedTensorFunctor P).obj ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ≅
      (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (tensorObj P X)) :=
  asIso ((derivedTensorFunctorCounit P).app ((toHomotopyCategory A).obj X)) ≪≫
    ((quasiIsomorphisms' B).Q.mapIso ((tensorCompFunctor_quotient P).app X)).symm

/-- The underlying map of `DifferentialGraded.Bimodule.derivedTensorPlainIso` is the
comparison. -/
theorem derivedTensorPlainIso_hom (P : Bimodule A B) (X : DifferentialGradedModule.{u, u, u} A)
    (h : IsIso ((derivedTensorFunctorCounit P).app ((toHomotopyCategory A).obj X))) :
    (derivedTensorPlainIso P X h).hom = derivedTensorPlainComparison P X :=
  rfl

/-- **The transition map of a derived tensor tower, read through the comparisons of Tag 0BZ2, is
the plain transition homomorphism.** This is
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap` without its orthogonality
hypotheses, which that statement uses only to make the comparisons invertible. -/
theorem derivedTensorRestrictTrans_towerMap_comparison (φ : A.Hom A') (P : Bimodule A B)
    (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    {X : DifferentialGradedModule.{u, u, u} A} {X' : DifferentialGradedModule.{u, u, u} A'}
    (v : X ⟶ restrictScalars φ X')
    (w : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X) ⟶
      (derivedRestriction φ).obj
        ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')))
    (hw : w = (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map v) ≫
      (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory A').obj X')) :
    ((derivedTensorFunctor P).map w ≫
          (derivedTensorRestrictTrans φ P P' τ).app
            ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X'))) ≫
        derivedTensorPlainComparison P' X' =
      derivedTensorPlainComparison P X ≫
        (quasiIsomorphisms' B).Q.map
          ((toHomotopyCategory B).map ((tensorCompFunctor P).map v ≫ τ.app X')) := by
  subst hw
  have hb : (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory A').obj X') ≫
      (derivedRestrictionFactorization φ).hom.app ((toHomotopyCategory A').obj X') =
        𝟙 ((quasiIsomorphisms' A).Q.obj
          ((restrictScalarsHomotopyFunctor φ).obj ((toHomotopyCategory A').obj X'))) :=
    (derivedRestrictionFactorization φ).inv_hom_id_app _
  have hc : (derivedTensorRestrictTrans φ P P' τ).app
          ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')) ≫
        (derivedTensorFunctorCounit P').app ((toHomotopyCategory A').obj X') =
      (derivedTensorFunctor P).map
          ((derivedRestrictionFactorization φ).hom.app ((toHomotopyCategory A').obj X')) ≫
        (derivedTensorFunctorCounit P).app
            ((restrictScalarsHomotopyFunctor φ).obj ((toHomotopyCategory A').obj X')) ≫
          (quasiIsomorphisms' B).Q.map
            ((restrictTensorHomotopyTrans φ P P' τ).app ((toHomotopyCategory A').obj X')) :=
    (derivedTensorRestrictTrans_app_comp_counit φ P P' τ
      ((toHomotopyCategory A').obj X')).trans
      (derivedTensorRestrictTransQuotient_app φ P P' τ ((toHomotopyCategory A').obj X'))
  have hk : (tensorCompFunctor_quotient P').hom.app X' ≫
      (tensorCompFunctor_quotient P').inv.app X' =
        𝟙 ((toHomotopyCategory B).obj ((tensorCompFunctor P').obj X')) :=
    (tensorCompFunctor_quotient P').hom_inv_id_app X'
  have hg : (toHomotopyCategory B).map ((tensorCompFunctor P).map v) ≫
      (toHomotopyCategory B).map (τ.app X') =
        (toHomotopyCategory B).map ((tensorCompFunctor P).map v ≫ τ.app X') :=
    ((toHomotopyCategory B).map_comp _ _).symm
  exact towerMap_aux (derivedTensorFunctor P) (quasiIsomorphisms' B).Q _ _ _ hb
    _ _ _ _ _ _ _ _ _ _ _ _ hc (restrictTensorHomotopyTrans_app φ P P' τ X') hk
    (localizedComparison_naturality_aux (derivedTensorFunctorCounit P)
      (tensorCompFunctor_quotient P) v) hg

/-- **The derived transition map is invertible exactly when the plain one is a
quasi-isomorphism**, when the comparisons of Tag 0BZ2 at the source and the target are
invertible. -/
theorem isIso_towerMap_iff_quasiIso (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    {X : DifferentialGradedModule.{u, u, u} A} {X' : DifferentialGradedModule.{u, u, u} A'}
    (v : X ⟶ restrictScalars φ X')
    (w : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X) ⟶
      (derivedRestriction φ).obj
        ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')))
    (hw : w = (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map v) ≫
      (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory A').obj X'))
    (hX : IsIso ((derivedTensorFunctorCounit P).app ((toHomotopyCategory A).obj X)))
    (hX' : IsIso ((derivedTensorFunctorCounit P').app ((toHomotopyCategory A').obj X'))) :
    IsIso ((derivedTensorFunctor P).map w ≫
        (derivedTensorRestrictTrans φ P P' τ).app
          ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X'))) ↔
      QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor P).map v ≫ τ.app X')) := by
  have h := derivedTensorRestrictTrans_towerMap_comparison φ P P' τ v w hw
  rw [← derivedTensorPlainIso_hom P X hX, ← derivedTensorPlainIso_hom P' X' hX'] at h
  rw [← isIso_q_map_toHomotopyCategory_map_iff]
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (derivedTensorPlainIso P X hX) (derivedTensorPlainIso P' X' hX') h.symm) : _)

end DifferentialGraded.Bimodule

end
