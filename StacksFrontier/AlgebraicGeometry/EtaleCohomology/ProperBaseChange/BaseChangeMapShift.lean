module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap

/-!
# The étale base change map is compatible with the shift

For a commutative square of schemes, the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap` is compatible with
the shift, for the canonical commutation of the two composite functors with the shift.

## Main results

* `Stacks.EtaleCohomology.natTransCommShift_etaleAbelianDerivedBaseChange`: the base change map
  is compatible with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-! ### Compatibility with the shift -/

/-- The derived-functor unit of `Rf_* ⋙ g^{-1}` is compatible with the shift: it is the unit of
`Rf_*` whiskered with the derived inverse image, and the unit of `Rf_*` is compatible with the
shift. -/
private theorem natTransCommShift_bcUnit : NatTrans.CommShift (bcUnit.{u, v} f g) ℤ := by
  dsimp only [bcUnit]
  infer_instance

/-- The identification of the source of the descent is compatible with the shift, because the
exactness comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` for `g^{-1}` is. -/
private theorem natTransCommShift_bcSourceIso_hom :
    NatTrans.CommShift (bcSourceIso.{u, v} f g).hom ℤ := by
  refine ⟨fun a => ?_⟩
  ext K
  have hc := NatTrans.shift_app_comm
    (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv a
    (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc, bcSourceIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_comp,
    NatTrans.comp_app, Functor.map_comp, Functor.whiskerRight_app, Functor.associator_hom_app,
    CategoryTheory.Functor.map_id, Functor.whiskerLeft_app, Category.comp_id, Category.id_comp,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_twice, Functor.associator_inv_app] at hc ⊢
  rw [hc]
  have hn := (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.naturality
    ((Functor.commShiftIso ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
      (ComplexShape.up ℤ)) a).hom.app K)
  dsimp at hn
  rw [reassoc_of% hn]

/-- The transformation descended to the base change map is compatible with the shift: each of
its factors is, the degreewise ones by `CategoryTheory.commShift_mapHomotopyCategory` and
`CategoryTheory.commShift_mapHomotopyCategoryCompIso`. -/
private theorem natTransCommShift_bcBeta : NatTrans.CommShift (bcBeta.{u, v} f g g' f' h) ℤ := by
  have := natTransCommShift_bcSourceIso_hom.{u, v} f g
  dsimp only [bcBeta, bcBetaOrig, etaleAbelianHomotopyBaseChange]
  infer_instance

/-- **The base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` is compatible with the shift**, for the
canonical commutation of the two composite functors with the shift. It is the descent, along the
right derived functor `Rf_* ⋙ g^{-1}` whose unit is compatible with the shift, of a
transformation compatible with the shift, and such a descent inherits the compatibility
(`Stacks.Triangulated.natTransCommShift_rightDerivedDesc`). -/
public instance natTransCommShift_etaleAbelianDerivedBaseChange :
    NatTrans.CommShift (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h) ℤ := by
  have := natTransCommShift_bcUnit.{u, v} f g
  have := natTransCommShift_bcBeta.{u, v} f g g' f' h
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc
    (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)
    (bcUnit.{u, v} f g)
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)) ℤ
    (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')
    (bcBeta.{u, v} f g g' f' h)

end Stacks.EtaleCohomology

end
