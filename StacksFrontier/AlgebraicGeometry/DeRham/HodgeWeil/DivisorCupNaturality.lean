module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.PullbackCup

/-!
# Naturality of the cup product of sheaves concentrated in degree zero

Let `A` be a sheaf of commutative rings on a ringed space and let `m : F ⊗_A G ⟶ H` be a morphism
of sheaves of `A`-modules. The cup product of Section 0FKU followed by `m`,

`H^q(X, F) × H^{q'}(X, G) ⟶ H^{q + q'}(X, H)`, `(x, y) ↦ m_*(x ∪ y)`,

is the pairing through which the Hodge cup product is computed
(`Stacks.HodgeWeil.hodgeComponentCup_eq_totalCupPairing`). This file records that it is natural
in the two sheaves: if `u : F ⟶ F'` and `v : G ⟶ G'` satisfy `m' ∘ (u ⊗ v) = m`, then
`m'_*(u_* x ∪ v_* y) = m_*(x ∪ y)`.

## Main results

* `Stacks.HodgeWeil.mapBifunctorMap_single_comp_singleIntMultiplication`: the identity of
  morphisms of complexes behind the naturality.
* `Stacks.HodgeWeil.cohomologyMap_singleIntMultiplication_totalCupPairing_map`: **the naturality
  of the cup product along a multiplication**, on elements.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap totalCupPairing)
open AlgebraicGeometry.SheafOfModules (baseRingedSpace)
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  {F F' G G' H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}

/-- **The multiplication of complexes concentrated in degree `0` is natural**: if
`m' ∘ (u ⊗ v) = m`, then `Tot(u[0] ⊗ v[0])` followed by the multiplication along `m'` is the
multiplication along `m`. -/
theorem mapBifunctorMap_single_comp_singleIntMultiplication (u : F ⟶ F') (v : G ⟶ G')
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H)
    (m' : ((sheafTensor.{u, u, u, u, u} A).obj F').obj G' ⟶ H)
    (h : ((sheafTensor.{u, u, u, u, u} A).map u).app G ≫
      ((sheafTensor.{u, u, u, u, u} A).obj F').map v ≫ m' = m) :
    HomologicalComplex.mapBifunctorMap ((HomologicalComplex.single _ (up ℤ) 0).map u)
        ((HomologicalComplex.single _ (up ℤ) 0).map v) (sheafTensor.{u, u, u, u, u} A) (up ℤ) ≫
      singleIntMultiplication m' = singleIntMultiplication m := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
  by_cases hi : i = 0
  · subst hi
    obtain rfl : j = 0 := by simpa using hij
    rw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_singleIntMultiplication_f, ι_singleIntMultiplication_f,
      HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self, ← h]
    rw [NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
      ← Functor.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Functor.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc, Category.assoc,
      ← NatTrans.naturality_assoc]
  · have hZ : IsZero (((sheafTensor.{u, u, u, u, u} A).obj
        (((HomologicalComplex.single _ (up ℤ) 0).obj F).X i)).obj
          (((HomologicalComplex.single _ (up ℤ) 0).obj G).X j)) :=
      ((sheafTensor.{u, u, u, u, u} A).map_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).obj _
    exact hZ.eq_of_src _ _


/-- **The cup product along a multiplication is natural in the two sheaves**: if
`m' ∘ (u ⊗ v) = m`, then `m'_*(u_* x ∪ v_* y) = m_*(x ∪ y)` for `x ∈ H^q(X, F)` and
`y ∈ H^{q'}(X, G)`, the cup product being the one of Section 0FKU. -/
theorem cohomologyMap_singleIntMultiplication_totalCupPairing_map (u : F ⟶ F') (v : G ⟶ G')
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H)
    (m' : ((sheafTensor.{u, u, u, u, u} A).obj F').obj G' ⟶ H)
    (h : ((sheafTensor.{u, u, u, u, u} A).map u).app G ≫
      ((sheafTensor.{u, u, u, u, u} A).obj F').map v ≫ m' = m) (q q' : ℤ)
    (x : cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj (singleInt F)) q)
    (y : cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj (singleInt G)) q') :
    (cohomologyMap (S := baseRingedSpace A) (singleIntMultiplication m') (q + q')).hom
        ((totalCupPairing (S := baseRingedSpace A) (singleInt F') (singleInt G') q q').hom
          ((cohomologyMap (S := baseRingedSpace A)
              ((HomologicalComplex.single _ (up ℤ) 0).map u) q).hom x ⊗ₜ
            (cohomologyMap (S := baseRingedSpace A)
              ((HomologicalComplex.single _ (up ℤ) 0).map v) q').hom y)) =
      (cohomologyMap (S := baseRingedSpace A) (singleIntMultiplication m) (q + q')).hom
        ((totalCupPairing (S := baseRingedSpace A) (singleInt F) (singleInt G) q q').hom
          (x ⊗ₜ y)) := by
  refine (congrArg (cohomologyMap (S := baseRingedSpace A) (singleIntMultiplication m')
    (q + q')).hom (totalCupPairing_naturality_apply (S := baseRingedSpace A)
      ((HomologicalComplex.single _ (up ℤ) 0).map u)
      ((HomologicalComplex.single _ (up ℤ) 0).map v) q q' x y)).trans ?_
  refine (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply
    (S := baseRingedSpace A) _ _ _ _).trans ?_
  exact congrArg (fun φ => (cohomologyMap (S := baseRingedSpace A) φ (q + q')).hom
    ((totalCupPairing (S := baseRingedSpace A) (singleInt F) (singleInt G) q q').hom (x ⊗ₜ y)))
    (mapBifunctorMap_single_comp_singleIntMultiplication u v m m' h)

end Stacks.HodgeWeil

end
