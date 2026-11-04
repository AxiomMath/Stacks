module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedAdjunctionCounit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionStructure
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorDerivedNaturality

/-!
# The two sheaf identities of Stacks 0D9K, in derived form

Let `S` be a simplicial-site situation. For abelian sheaves, the comparison map of Stacks 0D9E (1)
in degree `q` followed by the structure map of the integral resolution of Stacks 09WI at a simplex
map is a transpose along the adjunction `g_{q!} ⊣ g_q^{-1}`, and the comparison in degree zero
followed by the augmentation is the counit of `g_{0!} ⊣ g_0^{-1}`. This file carries both
identities into the derived category, where the Postnikov system of Stacks 0D9I lives.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `integerProjection_comp_derivedTensorFace`: **the comparison of Stacks 0D9E in degree `q`,
  followed by the derived tensor product with the structure map of the integral resolution at
  `φ : p ⟶ q`, is the derived functor of the sheaf-level composite** of the comparison with the
  structure map of the resolution.
* `derivedNatTrans_integerProjectionSheaf_comp_integerTensorAugmentation`: the derived functor of
  the sheaf-level composite of the comparison in degree zero with the augmentation is the counit of
  the derived adjunction `g_{0!} ⊣ g_0^{-1}`.
* `integerProjection_comp_derivedAugmentation`: **the comparison of Stacks 0D9E in degree zero,
  followed by the derived functor of the augmentation of the integral resolution, is the counit of
  the derived adjunction `g_{0!} ⊣ g_0^{-1}`.**

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.DerivedTensor.AbelianSheaves
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialSiteSituation

/-- Exchanging the two inner factors of a fourfold composite along `h : v ≫ u = z ≫ t`. -/
private theorem comp_swap_inner {C : Type*} [Category C] {W X Y Z Z' A : C}
    (x : W ⟶ X) (y : X ⟶ Y) {z : Y ⟶ Z} {t : Z ⟶ Z'} {v : Y ⟶ A} {u : A ⟶ Z'}
    (h : v ≫ u = z ≫ t) :
    (x ≫ y ≫ z) ≫ t = x ≫ (y ≫ v) ≫ u := by
  simp only [Category.assoc, h]

/-- A fourfold composite whose two inner factors cancel, `x ≫ x' = 𝟙 P` and `z ≫ z' = 𝟙 R`, reduced
through a given reading `h` of its tail. -/
private theorem comp_cancel_two {C : Type*} [Category C] {P Q R R' A B : C}
    (x : P ⟶ Q) (x' : Q ⟶ P) (y : Q ⟶ R) (z : R ⟶ R') (z' : R' ⟶ R) (a : R ⟶ A) (b : A ⟶ B)
    (cnt : P ⟶ B) (hx : x ≫ x' = 𝟙 P) (hz : z ≫ z' = 𝟙 R)
    (h : y ≫ a ≫ b = x' ≫ cnt) :
    (x ≫ y ≫ z) ≫ z' ≫ a ≫ b = cnt := by
  simp only [Category.assoc]
  rw [reassoc_of% hz, h, reassoc_of% hx]

section Face

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- **The comparison of Stacks 0D9E in degree `q`, followed by the derived tensor product with the
structure map of the integral resolution at `φ : p ⟶ q`, is the derived functor of the sheaf-level
composite of the comparison with the structure map of the resolution.** This is the first of the
two sheaf identities of Stacks 0D9K in derived form. -/
theorem integerProjection_comp_derivedTensorFace
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    {p q : SimplexCategory} (φ : p ⟶ q) :
    S.integerProjection K q ≫
        ((derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerFace S φ))).app K =
      (derivedCompIso (S.restrictAb q) (componentLowerShriekAb S q) _ (Iso.refl _)).inv.app K ≫
        (derivedNatTrans (S.restrictAb q ⋙ componentLowerShriekAb S q) (integerTensorAb S p)
          (integerProjectionSheaf S q ≫ integerTensorFace S φ)).app K ≫
        (S.integerTensorAbDerivedIso p).hom.app K := by
  have hnat := congr_app (integerTensorAbDerivedIso_naturality S φ) K
  simp only [NatTrans.comp_app] at hnat
  rw [integerProjection, derivedNatTrans_comp]
  simp only [NatTrans.comp_app]
  exact comp_swap_inner _ _ hnat

end Face

section Augmentation

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- **The derived functor of the sheaf-level composite of the comparison of Stacks 0D9E in degree
zero with the augmentation of the integral resolution is the counit of the derived adjunction
`g_{0!} ⊣ g_0^{-1}`.** This is the second of the two sheaf identities of Stacks 0D9K in derived
form, stated at the level of the transformations of derived functors. -/
theorem derivedNatTrans_integerProjectionSheaf_comp_integerTensorAugmentation :
    derivedNatTrans (S.restrictAb ⦋0⦌ ⋙ componentLowerShriekAb S ⦋0⦌) (integerTensorAb S ⦋0⦌)
          (integerProjectionSheaf S ⦋0⦌) ≫
        derivedNatTrans (integerTensorAb S ⦋0⦌) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (integerTensorAugmentation S) ≫
        (derivedIdIso (A := Sheaf S.totalTopology Ab.{u})).hom =
      (derivedCompIso (S.restrictAb ⦋0⦌) (componentLowerShriekAb S ⦋0⦌)
          (S.restrictAb ⦋0⦌ ⋙ componentLowerShriekAb S ⦋0⦌) (Iso.refl _)).hom ≫
        (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit := by
  rw [← Category.assoc, ← derivedNatTrans_comp,
    integerProjectionSheaf_comp_integerTensorAugmentation]
  exact derivedNatTrans_counit (S.componentLowerShriekAbAdjunction' ⦋0⦌)

end Augmentation

section AugmentationProjection

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- **The comparison of Stacks 0D9E in degree zero, followed by the derived functor of the
augmentation of the integral resolution, is the counit of the derived adjunction
`g_{0!} ⊣ g_0^{-1}` at `K`.** -/
theorem integerProjection_comp_derivedAugmentation
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    S.integerProjection K ⦋0⦌ ≫ (S.integerTensorAbDerivedIso ⦋0⦌).inv.app K ≫
        (derivedNatTrans (integerTensorAb S ⦋0⦌) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (integerTensorAugmentation S)).app K ≫
        (derivedIdIso (A := Sheaf S.totalTopology Ab.{u})).hom.app K =
      (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit.app K := by
  have hid := congr_app
    (derivedNatTrans_integerProjectionSheaf_comp_integerTensorAugmentation S) K
  simp only [NatTrans.comp_app] at hid
  rw [integerProjection]
  exact comp_cancel_two _ _ _ _ _ _ _ _ (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) hid

end AugmentationProjection

end CategoryTheory.SimplicialSiteSituation

end
