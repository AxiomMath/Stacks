module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The two restriction maps on étale cohomology agree

The library has two constructions of the restriction map `H^q(X, F) ⟶ H^q(Y, i⁻¹F)` on the
cohomology `CategoryTheory.Sheaf.H` of the small étale site along a morphism of schemes
`i : Y ⟶ X`:

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`, for abelian sheaves of the universe
  `max (u + 1) v`, with `i⁻¹` the inverse image `Stacks.EtaleCohomology.etaleAbelianInverseImage`
  built as a left Kan extension followed by sheafification;
* `Stacks.EtaleCohomology.etaleCohomologyPullback`, for abelian sheaves of the universe `u + 1`,
  with `i⁻¹` the inverse image `Stacks.EtaleCohomology.smallEtalePullbackAb`, the abstract left
  adjoint of direct image.

At `v = 0` and cohomology universe `w = u + 1` both are defined on the same groups, the two inverse
images being the two models `CategoryTheory.Functor.sheafPullback` and
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` of the left adjoint of direct
image, identified by `Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage`
of `StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedGeometricStalkSections.lean` (both are
left adjoint to the same direct image). This file shows that under that identification the two
maps differ only by composition with isomorphisms, so that one is bijective exactly when the
other is.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_eq_mk₀_comp_etaleCohomologyPullback`:
  `etaleCohomologyRestrictionMap` is `etaleCohomologyPullback` along the identification of the
  inverse images, followed by an automorphism of the constant sheaf `ℤ`.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_iff`: one map is bijective
  exactly when the other is.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_iff_of_iso`: bijectivity of
  `etaleCohomologyPullback` is invariant under replacing the coefficient sheaf by an isomorphic
  one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- **`etaleCohomologyRestrictionMap` is `etaleCohomologyPullback` up to an automorphism of `ℤ`.**
At the coefficient universe `u + 1` and the cohomology universe `u + 1`, the restriction map of
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is the pull back map with the
identification `smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse images,
precomposed with the automorphism of the constant sheaf `ℤ` on `Y` comparing the two
identifications of the inverse image of `ℤ` with `ℤ`. -/
public theorem etaleCohomologyRestrictionMap_eq_mk₀_comp_etaleCohomologyPullback (i : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q x =
      (Ext.mk₀ (((etaleAbelianInverseImageConstantIso.{u, 0} i).app
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (smallEtalePullbackAbIsoEtaleAbelianInverseImage i).inv.app _ ≫
          (smallEtalePullbackAbConstantIso i).hom.app (AddCommGrpCat.of (ULift ℤ)))).comp
        (etaleCohomologyPullback i ((smallEtalePullbackAbIsoEtaleAbelianInverseImage i).hom.app F)
          q x) (zero_add q) := by
  let α := smallEtalePullbackAbIsoEtaleAbelianInverseImage i
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor α.hom _ q x
  have hx : x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} i) =
      (Ext.mk₀ (α.inv.app _)).comp
        ((x.mapExactFunctor (smallEtalePullbackAb i)).comp (Ext.mk₀ (α.hom.app F)) (add_zero q))
        (zero_add q) := by
    rw [← key, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app, Ext.mk₀_id_comp]
  rw [etaleCohomologyRestrictionMap_apply, etaleCohomologyPullback_apply, hx]
  simp only [Ext.mk₀_comp_mk₀_assoc, Category.assoc, Iso.hom_inv_id_app]
  rfl

/-- **`etaleCohomologyRestrictionMap` is bijective exactly when `etaleCohomologyPullback` is**, at
the coefficient universe `u + 1` and the cohomology universe `u + 1`. -/
public theorem bijective_etaleCohomologyRestrictionMap_iff (i : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q) ↔
      Function.Bijective (etaleCohomologyPullback i (𝟙 ((smallEtalePullbackAb i).obj F)) q) := by
  let α := smallEtalePullbackAbIsoEtaleAbelianInverseImage i
  let e := ((etaleAbelianInverseImageConstantIso.{u, 0} i).app (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
    α.symm.app _ ≪≫ (smallEtalePullbackAbConstantIso i).app (AddCommGrpCat.of (ULift ℤ))
  have pre : Function.Bijective
      (fun y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj F) q =>
        (Ext.mk₀ e.hom).comp y (zero_add q)) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun z => (Ext.mk₀ e.inv).comp z (zero_add q), fun z => ?_, fun z => ?_⟩ <;>
      simp [Ext.mk₀_comp_mk₀_assoc]
  have h : (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q : _ → _) =
      (fun y => (Ext.mk₀ e.hom).comp y (zero_add q)) ∘
        etaleCohomologyPullback i (α.hom.app F) q :=
    funext (etaleCohomologyRestrictionMap_eq_mk₀_comp_etaleCohomologyPullback i F q)
  rw [h, Function.Bijective.of_comp_iff' pre]
  exact bijective_etaleCohomologyPullback_iff_of_isIso_sheaf i (α.hom.app F) q

/-- **Bijectivity of pulling back is invariant under isomorphism of the coefficient sheaf.** -/
public theorem bijective_etaleCohomologyPullback_iff_of_iso (i : Y ⟶ X)
    {F F' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (β : F ≅ F') (q : ℕ) :
    Function.Bijective (etaleCohomologyPullback i (𝟙 ((smallEtalePullbackAb i).obj F)) q) ↔
      Function.Bijective (etaleCohomologyPullback i (𝟙 ((smallEtalePullbackAb i).obj F')) q) := by
  have post : ∀ {Z : Scheme.{u}} {A B : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} (e : A ≅ B)
      {T : Sheaf (smallEtaleTopology Z) Ab.{u + 1}},
      Function.Bijective (fun z : Ext.{u + 1} T A q => z.comp (Ext.mk₀ e.hom) (add_zero q)) := by
    intro Z A B e T
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun z => z.comp (Ext.mk₀ e.inv) (add_zero q), fun z => ?_, fun z => ?_⟩ <;>
      simp [Ext.mk₀_comp_mk₀]
  have h : (etaleCohomologyPullback i (𝟙 ((smallEtalePullbackAb i).obj F')) q : _ → _) ∘
        (fun z : Sheaf.H.{u + 1} F q => z.comp (Ext.mk₀ β.hom) (add_zero q)) =
      (fun z => z.comp (Ext.mk₀ ((smallEtalePullbackAb i).mapIso β).hom) (add_zero q)) ∘
        etaleCohomologyPullback i (𝟙 ((smallEtalePullbackAb i).obj F)) q := by
    funext z
    simp only [Function.comp_apply, etaleCohomologyPullback_mk₀_comp,
      etaleCohomologyPullback_comp_mk₀, Functor.mapIso_hom, Category.comp_id, Category.id_comp]
  rw [← Function.Bijective.of_comp_iff' (post ((smallEtalePullbackAb i).mapIso β)), ← h]
  exact Function.Bijective.of_comp_iff _ (post β)

end Stacks.EtaleCohomology

end
