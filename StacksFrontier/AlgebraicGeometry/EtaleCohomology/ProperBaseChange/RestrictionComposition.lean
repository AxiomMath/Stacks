module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The composition law for restriction on étale cohomology

Restriction on étale cohomology, `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`, is the
action of the exact inverse-image functor on an `Ext` class out of the constant sheaf `ℤ`,
transported along the constant-sheaf comparison
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`.  This file proves that it is
compatible with composition of morphisms of schemes: restricting along `a : Y ⟶ X` and then
along `b : Z ⟶ Y` is restricting along the composite, read through the comparison
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` of the inverse image along the
composite with the composite of the inverse images.

The proof has two halves.  On the `Ext` side the action of a composite of exact functors is the
composite of the actions, `Stacks.ExtFunctorial.mapExactFunctor_comp_functor`, and the
comparison of two exact functors intertwines their actions,
`Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor`; both need enough injectives in the source
category, which the small étale site of a scheme supplies because its sheaves of abelian groups
form a Grothendieck abelian category.  What is left after those two rewrites is an identity
between morphisms of sheaves on the small étale site of `Z`, and that is the composition
coherence of the constant-sheaf comparison,
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_comp`, with its three isomorphisms
inverted.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_inv_comp` — the composition
  coherence of the constant-sheaf comparison, in inverted form.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp` — **the composition law for
  restriction on étale cohomology.**

## References

* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Composition

variable {X Y Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- **The composition coherence of the constant-sheaf comparison, inverted.**  The inverse of the
comparison for a composite `ba = b ≫ a` is the inverse of the comparison for `b`, followed by the
inverse image along `b` of the inverse of the comparison for `a`, followed by the comparison of
the composite of the inverse images with the inverse image along the composite.  This is
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_comp` with all three isomorphisms
inverted. -/
public theorem etaleAbelianInverseImageConstantIso_inv_comp (a : Y ⟶ X) (b : Z ⟶ Y) (ba : Z ⟶ X)
    (hba : ba = b ≫ a) (A : AddCommGrpCat.{max (u + 1) v}) :
    (((etaleAbelianInverseImageConstantIso.{u, v} b).app A).inv ≫
          (etaleAbelianInverseImage.{u, v} b).map
            ((etaleAbelianInverseImageConstantIso.{u, v} a).app A).inv) ≫
        (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) =
      ((etaleAbelianInverseImageConstantIso.{u, v} ba).app A).inv := by
  have hc := etaleAbelianInverseImageConstantIso_comp.{u, v} a b ba hba A
  simp only [← Iso.app_hom] at hc
  refine (Iso.comp_hom_eq_id ((etaleAbelianInverseImageConstantIso.{u, v} ba).app A)).mp ?_
  rw [Category.assoc, ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id]

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on étale cohomology composes.**  For `a : Y ⟶ X`, `b : Z ⟶ Y` and a named
composite `ba = b ≫ a`, restriction along `a` followed by restriction along `b` is restriction
along `ba`, once the inverse image along `ba` is identified with the composite of the two inverse
images by `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'`. -/
public theorem etaleCohomologyRestrictionMap_comp (a : Y ⟶ X) (b : Z ⟶ Y) (ba : Z ⟶ X)
    (hba : ba = b ≫ a) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app F) q
        (etaleCohomologyRestrictionMap.{u, v, w} b
          ((etaleAbelianInverseImage.{u, v} a).obj F) q
          (etaleCohomologyRestrictionMap.{u, v, w} a F q x)) =
      etaleCohomologyRestrictionMap.{u, v, w} ba F q x := by
  let : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _
  let : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    CategoryTheory.IsGrothendieckAbelian.enoughInjectives
  rw [Sheaf.H.map_apply,
    etaleCohomologyRestrictionMap_apply.{u, v, w} b
      ((etaleAbelianInverseImage.{u, v} a).obj F) q
      (etaleCohomologyRestrictionMap.{u, v, w} a F q x),
    etaleCohomologyRestrictionMap_apply.{u, v, w} a F q x,
    etaleCohomologyRestrictionMap_apply.{u, v, w} ba F q x,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor (etaleAbelianInverseImage.{u, v} a)
      (etaleAbelianInverseImage.{u, v} b) _ q x,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
      (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv _ q x,
    Ext.mk₀_comp_mk₀_assoc,
    etaleAbelianInverseImageConstantIso_inv_comp.{u, v} a b ba hba
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))]

end Composition

end Stacks.EtaleCohomology

end
