module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal

/-!
# Axiom (A5) for an arbitrary fibre product

Axiom (A5) of Section 45.14 of the Stacks Project (Tag 0FID) is
`Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`: `H^*(Spec k) = F`, and the Künneth map
`H^*(X) ⊗_F H^*(Y) → H^*(X × Y)` is bijective for the product `X × Y`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.prod`). This file transports it to any fibre
product `P` of `X` and `Y` over `Spec(k)`, along the comparison isomorphism `P ≅ X × Y`.

## Main results

* `Stacks.WeilDeRham.isPullback_fst_snd`: `X × Y` with its projections is a fibre product of `X`
  and `Y` over `Spec(k)` in schemes.
* `Stacks.WeilDeRham.bijective_kunneth_of_isPullback`: for a fibre product `P` with projections
  `p`, `q`, the map `a ⊗ b ↦ p^*a ∪ q^*b` is bijective, and
  `Stacks.WeilDeRham.kunnethEquivOfIsPullback` is the resulting isomorphism.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

/-- `X ×_k Y` with its two projections is a fibre product of `X` and `Y` over `Spec(k)`. -/
theorem isPullback_fst_snd (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback ((toScheme k).map (fst X Y)) ((toScheme k).map (snd X Y)) X.obj.hom
      Y.obj.hom :=
  IsPullback.of_hasPullback X.obj.hom Y.obj.hom

section Kunneth

variable {X Y P : (SmoothProjectiveScheme k).FullSubcategory} (p : P ⟶ X) (q : P ⟶ Y)
  (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom)

/-- The comparison `P ⟶ X × Y` of a fibre product `P` of `X` and `Y` over `Spec(k)` with the
product. -/
def toProdOfIsPullback : P ⟶ prod X Y :=
  prodLift p q

/-- The inverse comparison `X × Y ⟶ P`. -/
def ofProdOfIsPullback : prod X Y ⟶ P :=
  homMk (hP.lift ((toScheme k).map (fst X Y)) ((toScheme k).map (snd X Y))
      (by rw [w, w]))
    (by rw [← w p, ← Category.assoc, IsPullback.lift_fst, w])

/-- The composite `X × Y ⟶ P ⟶ X × Y` of the two comparisons is the identity. -/
theorem ofProdOfIsPullback_toProdOfIsPullback :
    ofProdOfIsPullback p q hP ≫ toProdOfIsPullback p q = 𝟙 _ :=
  prod_hom_ext
    (by rw [Category.assoc, toProdOfIsPullback, prodLift_fst, Category.id_comp]
        exact hom_ext' (hP.lift_fst _ _ _))
    (by rw [Category.assoc, toProdOfIsPullback, prodLift_snd, Category.id_comp]
        exact hom_ext' (hP.lift_snd _ _ _))

/-- The composite `P ⟶ X × Y ⟶ P` of the two comparisons is the identity. -/
theorem toProdOfIsPullback_ofProdOfIsPullback :
    toProdOfIsPullback p q ≫ ofProdOfIsPullback p q hP = 𝟙 _ :=
  hom_ext' (hP.hom_ext
    (by
      rw [Functor.map_comp, Category.assoc, ofProdOfIsPullback, map_homMk, IsPullback.lift_fst,
        ← Functor.map_comp, toProdOfIsPullback, prodLift_fst, CategoryTheory.Functor.map_id,
        Category.id_comp])
    (by
      rw [Functor.map_comp, Category.assoc, ofProdOfIsPullback, map_homMk, IsPullback.lift_snd,
        ← Functor.map_comp, toProdOfIsPullback, prodLift_snd, CategoryTheory.Functor.map_id,
        Category.id_comp]))

variable (𝔇) in
/-- The Künneth map of `P` is the pullback along `P ⟶ X × Y` of the Künneth map of `X × Y`. -/
theorem lift_mul_pull_pull_eq :
    TensorProduct.lift ((LinearMap.mul F (𝔇.H P)).compl₁₂ (𝔇.pull p).toLinearMap
        (𝔇.pull q).toLinearMap) =
      (𝔇.pull (toProdOfIsPullback p q)).toLinearMap ∘ₗ 𝔇.kunnethMap X Y := by
  refine TensorProduct.ext' fun a b => ?_
  simp only [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    FirstChernClassData.kunnethMap_tmul, map_mul]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← 𝔇.pull_comp, ← 𝔇.pull_comp,
    toProdOfIsPullback, prodLift_fst, prodLift_snd]

/-- If `f ≫ g = 𝟙`, then `f^*` undoes `g^*`. -/
private theorem pull_pull_eq_of_comp_eq_id (𝔇 : FirstChernClassData k F)
    {A B : (SmoothProjectiveScheme k).FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 _) (x : 𝔇.H A) : 𝔇.pull f (𝔇.pull g x) = x := by
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, h, 𝔇.pull_id, AlgHom.id_apply]

include hP in
/-- **(A5) for an arbitrary fibre product**: if `P` with projections `p`, `q` is a fibre product
of `X` and `Y` over `Spec(k)`, then `H^*(X) ⊗_F H^*(Y) → H^*(P)`, `a ⊗ b ↦ p^*a ∪ q^*b`, is
bijective. -/
theorem bijective_kunneth_of_isPullback (hA5 : 𝔇.KunnethAxiom) :
    Function.Bijective (TensorProduct.lift ((LinearMap.mul F (𝔇.H P)).compl₁₂
      (𝔇.pull p).toLinearMap (𝔇.pull q).toLinearMap)) := by
  rw [lift_mul_pull_pull_eq, LinearMap.coe_comp]
  refine Function.Bijective.comp ?_ (hA5.2 X Y)
  exact Function.bijective_iff_has_inverse.mpr
    ⟨𝔇.pull (ofProdOfIsPullback p q hP),
      pull_pull_eq_of_comp_eq_id 𝔇 _ _ (ofProdOfIsPullback_toProdOfIsPullback p q hP),
      pull_pull_eq_of_comp_eq_id 𝔇 _ _ (toProdOfIsPullback_ofProdOfIsPullback p q hP)⟩

/-- The Künneth isomorphism `H^*(X) ⊗_F H^*(Y) ≅ H^*(P)`, `a ⊗ b ↦ p^*a ∪ q^*b`, of (A5), for a
fibre product `P` of `X` and `Y` over `Spec(k)`. -/
def kunnethEquivOfIsPullback (hA5 : 𝔇.KunnethAxiom) : 𝔇.H X ⊗[F] 𝔇.H Y ≃ₗ[F] 𝔇.H P :=
  LinearEquiv.ofBijective _ (bijective_kunneth_of_isPullback p q hP hA5)

/-- The Künneth isomorphism of a fibre product sends `a ⊗ b` to `p^*a ∪ q^*b`. -/
theorem kunnethEquivOfIsPullback_tmul (hA5 : 𝔇.KunnethAxiom) (a : 𝔇.H X) (b : 𝔇.H Y) :
    kunnethEquivOfIsPullback p q hP hA5 (a ⊗ₜ b) = 𝔇.pull p a * 𝔇.pull q b := rfl

end Kunneth

end Stacks.WeilDeRham

end
