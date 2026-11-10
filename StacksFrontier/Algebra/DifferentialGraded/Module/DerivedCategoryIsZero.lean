module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestrictionDerived
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction

/-!
# Zero objects of the derived category of a differential graded algebra

An object of the derived category `D(A, d)` of a differential graded algebra is zero exactly when
a differential graded module representing it is acyclic. This file records that criterion in the
form of the zero endomorphism: a differential graded module `X` is acyclic exactly when its zero
endomorphism is a quasi-isomorphism, and that is invariant under regarding `X` over a smaller base
ring, under restriction of scalars and under isomorphism.

## Main definitions

* `DifferentialGradedModule.QuasiIsoZero`: the zero endomorphism of a differential graded module
  is a quasi-isomorphism.

## Main results

* `DifferentialGradedModule.isZero_q_obj_iff`: **the class of `X` in `D(A, d)` is zero exactly when
  the zero endomorphism of `X` is a quasi-isomorphism.**
* `DifferentialGradedModule.quasiIsoZero_restrictBase_iff`,
  `DifferentialGradedModule.quasiIsoZero_restrictScalars_iff` and
  `DifferentialGradedModule.quasiIsoZero_iff_of_iso`: the criterion is invariant under regarding
  over `S`, under restriction of scalars and under isomorphism.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- The zero endomorphism of a differential graded module is a quasi-isomorphism: the
differential graded module is acyclic. -/
def QuasiIsoZero (X : DifferentialGradedModule.{u, u, u} A) : Prop :=
  QuasiIso ((forgetToCochainComplex A).map (0 : X ⟶ X))

/-- Every endomorphism of a zero object is an isomorphism. -/
theorem isIso_of_isZero_endo {C : Type*} [Category C] {X : C} (h : IsZero X) (f : X ⟶ X) :
    IsIso f :=
  ⟨⟨𝟙 X, h.eq_of_src _ _, h.eq_of_src _ _⟩⟩

/-- An object with an invertible zero endomorphism is zero. -/
theorem isZero_of_isIso_zero {C : Type*} [Category C] [Preadditive C] {X : C} {z : X ⟶ X}
    (hz : z = 0) (h : IsIso z) : IsZero X := by
  subst hz
  rw [IsZero.iff_id_eq_zero]
  simpa only [zero_comp] using (IsIso.hom_inv_id (0 : X ⟶ X)).symm

/-- **The class of `X` in `D(A, d)` is zero exactly when the zero endomorphism of `X` is a
quasi-isomorphism.** -/
theorem isZero_q_obj_iff (X : DifferentialGradedModule.{u, u, u} A) :
    IsZero ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ↔ QuasiIsoZero X :=
  ⟨fun h => (isIso_q_map_toHomotopyCategory_map_iff A (0 : X ⟶ X)).1 (isIso_of_isZero_endo h _),
    fun h => isZero_of_isIso_zero (by rw [Functor.map_zero, Functor.map_zero])
      ((isIso_q_map_toHomotopyCategory_map_iff A (0 : X ⟶ X)).2 h)⟩

/-- The criterion only depends on the isomorphism class of the module. -/
theorem quasiIsoZero_iff_of_iso {X Y : DifferentialGradedModule.{u, u, u} A} (e : X ≅ Y) :
    QuasiIsoZero X ↔ QuasiIsoZero Y :=
  quasiIso_iff_of_arrow_mk_iso _ _ ((forgetToCochainComplex A).mapArrow.mapIso
    (Arrow.isoMk (f := Arrow.mk (0 : X ⟶ X)) (g := Arrow.mk (0 : Y ⟶ Y)) e e (by simp)))

/-- The criterion is invariant under restriction of scalars, which does not change the underlying
complex. -/
theorem quasiIsoZero_restrictScalars_iff {B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B)
    (X : DifferentialGradedModule.{u, u, u} B) :
    QuasiIsoZero (restrictScalars φ X) ↔ QuasiIsoZero X := by
  have h : @Eq (X.toCochainComplex ⟶ X.toCochainComplex)
      (restrictScalarsHom φ (0 : X ⟶ X)).toCochainMap (0 : X ⟶ X).toCochainMap :=
    restrictScalarsHom_toCochainMap φ 0
  have h0 : (0 : restrictScalars φ X ⟶ restrictScalars φ X) = restrictScalarsHom φ (0 : X ⟶ X) :=
    DifferentialGradedModule.Hom.ext rfl
  unfold QuasiIsoZero
  rw [h0]
  change QuasiIso (restrictScalarsHom φ (0 : X ⟶ X)).toCochainMap ↔
    QuasiIso (0 : X ⟶ X).toCochainMap
  rw [h]
  exact Iff.rfl

/-- The criterion is invariant under regarding over a smaller base ring. -/
theorem quasiIsoZero_restrictBase_iff (S : Type u) [CommRing S] [Algebra S R]
    (X : DifferentialGradedModule.{u, u, u} A) :
    QuasiIsoZero (restrictBaseObj S X) ↔ QuasiIsoZero X := by
  have h0 : (0 : restrictBaseObj S X ⟶ restrictBaseObj S X) = (restrictBase S A).map (0 : X ⟶ X) :=
    DifferentialGradedModule.Hom.ext rfl
  unfold QuasiIsoZero
  rw [h0]
  exact quasiIso_restrictBase_map_iff S (0 : X ⟶ X)

end DifferentialGradedModule

end
