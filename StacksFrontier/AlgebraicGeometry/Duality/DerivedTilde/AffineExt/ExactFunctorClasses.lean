module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.KInjectiveSections
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exact functors on cohomology classes of Hom complexes

An exact functor `F` carries the derived morphism attached to a cocycle of a Hom complex into a
K-injective complex to the derived morphism attached to the image cocycle.

## Main results

* `CochainComplex.HomComplex.cohomologyClassAddEquivShiftedHom_map`: the derived morphism of the
  class of `a ≫ F(z) ≫ b` is obtained from that of `z` by applying the derived functor of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The image of a cocycle under an additive functor. -/
def Cocycle.map' {A J : CochainComplex C ℤ} {n : ℤ} (z : Cocycle A J n) :
    Cocycle ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) n :=
  Cocycle.mk ((z : Cochain A J n).map F) (n + 1) rfl
    (by rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- The morphism `F(A) ⟶ F(J)[n]` attached to the image cocycle `F(z)` is the image under `F` of
the morphism `A ⟶ J[n]` attached to `z`, composed with the commutation isomorphism
`F(J[n]) ≅ F(J)[n]`. -/
lemma equivHomShift_symm_map' {A J : CochainComplex C ℤ} {n : ℤ} (z : Cocycle A J n) :
    Cocycle.equivHomShift.symm (Cocycle.map' F z) =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Cocycle.equivHomShift.symm z) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app J := by
  ext p
  simp only [Cocycle.map', Cocycle.equivHomShift_symm_apply, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.mk_coe,
    Cochain.rightShift_v _ _ _ _ p p (add_zero p) (p + n) rfl, Cochain.map_v, Functor.map_comp]
  congr 1
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- An exact functor carries the derived morphism of a morphism `X ⟶ Y[n]` of complexes to the
derived morphism of its image. -/
@[reassoc]
lemma mapDerivedCategory_map_shiftedHom {X Y : CochainComplex C ℤ} {n : ℤ}
    (g : X ⟶ Y⟦n⟧) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map g ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj Y) =
    F.mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app Y) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app ((F.mapHomologicalComplex (ComplexShape.up
          ℤ)).obj Y) ≫
      (F.mapDerivedCategoryFactors.inv.app Y)⟦n⟧' := by
  have h₁ := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n Y
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h₁
  have h₂ : F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app Y) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj Y) =
      F.mapDerivedCategoryFactors.hom.app (Y⟦n⟧) ≫
        DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
            n).hom.app Y) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
            (F.mapDerivedCategoryFactors.inv.app Y)⟦n⟧' := by
    rw [← reassoc_of% h₁, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  rw [Functor.map_comp, Category.assoc, h₂, Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    Functor.map_comp, Category.assoc]

/-- For a natural isomorphism `e : G ≅ H` and a functor `S`, the composite
`S(e⁻¹_Y) ≫ S(e_Y) ≫ h` equals `h`. -/
lemma map_inv_app_map_hom_app_assoc {X E E' : Type*} [Category X] [Category E] [Category E']
    (S : E ⥤ E') {G H : X ⥤ E} (e : G ≅ H) (Y : X) {W : E'} (h : S.obj (H.obj Y) ⟶ W) :
    S.map (e.inv.app Y) ≫ S.map (e.hom.app Y) ≫ h = h := by
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Exact functors act on cohomology classes of Hom complexes as on derived morphisms.** For
an exact functor `F`, cocycles `z : A ⟶ J[n]`, and morphisms of complexes `a : A' ⟶ F(A)`,
`b : F(J) ⟶ J'` with `J`, `J'` K-injective, the derived morphism of the class of `a ≫ F(z) ≫ b`
is obtained from the derived morphism of the class of `z` by applying the derived functor of `F`
and composing with the images of `a` and `b`. -/
lemma cohomologyClassAddEquivShiftedHom_map {A J : CochainComplex C ℤ} [J.IsKInjective]
    {A' J' : CochainComplex D ℤ} [J'.IsKInjective] {n : ℤ}
    (a : A' ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
    (b : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J ⟶ J') (z : Cocycle A J n) :
    cohomologyClassAddEquivShiftedHom A' J' n
        (CohomologyClass.mk (((Cocycle.map' F z).precomp a).postcomp b)) =
      DerivedCategory.Q.map a ≫ F.mapDerivedCategoryFactors.inv.app A ≫
        F.mapDerivedCategory.map (cohomologyClassAddEquivShiftedHom A J n (CohomologyClass.mk z)) ≫
          (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj J) ≫
            (F.mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map b)⟦n⟧' := by
  rw [cohomologyClassAddEquivShiftedHom_mk, cohomologyClassAddEquivShiftedHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp,
    equivHomShift_symm_map', mapDerivedCategory_map_shiftedHom_assoc]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.commShiftIso_hom_naturality, map_inv_app_map_hom_app_assoc]

end CochainComplex.HomComplex
