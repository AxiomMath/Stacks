module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.PseudoCoherent.Products

@[expose] public section

/-!
# Pseudo-coherent tensor products and derived inverse limits

Let `R` be a commutative ring, let `K` be a pseudo-coherent object of `D(R)`, and let
`(Mₙ)` be an inverse system of `R`-modules. The derived tensor product with `K` commutes
with the derived inverse limit of `(Mₙ)`.

## Main definitions

* `Stacks.PseudoCoherent.DerivedInverseLimit.derivedTensorProductComparison` is the canonical map
  from the tensor product
  of a product to the product of the tensor products.

## Main results

* `Stacks.PseudoCoherent.DerivedInverseLimit.derivedLimit_tensor_iso` identifies the derived limit
  of `(K ⊗ᴸ Mₙ)` with
  `K ⊗ᴸ Rlim Mₙ` by the canonical comparison isomorphism.

## Implementation notes

A derived inverse limit is represented by its Milnor distinguished triangle. Countable
products in that triangle are chosen by the same product data used for the tensor-product
comparison. Modules are regarded as complexes concentrated in degree zero. The coefficient
ring is replaced by its canonically equivalent small copy, as for Tag 0CYB.

## References

* [Stacks Project, Tag 0D2L](https://stacks.math.columbia.edu/tag/0D2L)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

universe u v w x

namespace Stacks.PseudoCoherent.DerivedInverseLimit

variable (R : Type u) [CommRing R] [Small.{max v w} R]

/-- The countable products determined by a simultaneous choice of products in `D(R)`. -/
theorem hasProductsOfShapeNat (P : DerivedProducts.{u, v, w} R) :
    HasProductsOfShape ℕ (D.{u, v, w} R) := by
  have : HasProductsOfShape (ULift.{max v w} ℕ) (D.{u, v, w} R) :=
    ⟨fun F => by
      have := P.hasProduct (ULift.{max v w} ℕ) (F.obj ∘ Discrete.mk)
      exact hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm⟩
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-- The canonical morphism `K ⊗ᴸ (∏ a, E a) ⟶ ∏ a, (K ⊗ᴸ E a)`. -/
noncomputable def derivedTensorProductComparison
    (T : DerivedTensorProduct.{u, v, w} R) (K : D.{u, v, w} R) {A : Type x}
    (E : A → D.{u, v, w} R)
    [HasProduct E] [HasProduct (fun a => (T.tensor.obj K).obj (E a))] :
    (T.tensor.obj K).obj (∏ᶜ E) ⟶ ∏ᶜ fun a => (T.tensor.obj K).obj (E a) :=
  Pi.lift fun a => (T.tensor.obj K).map (Pi.π E a)

/-- The component of `derivedTensorProductComparison` at `a` is `K ⊗ᴸ` applied to the
projection `∏ a, E a ⟶ E a`. -/
@[reassoc]
theorem derivedTensorProductComparison_π
    (T : DerivedTensorProduct.{u, v, w} R) (K : D.{u, v, w} R) {A : Type x}
    (E : A → D.{u, v, w} R)
    [HasProduct E] [HasProduct (fun a => (T.tensor.obj K).obj (E a))] (a : A) :
    derivedTensorProductComparison R T K E ≫ Pi.π _ a =
      (T.tensor.obj K).map (Pi.π E a) := by
  simp [derivedTensorProductComparison]

/-- For modules in degree zero, the Milnor-triangle comparison is exactly the comparison
of Tag 0CYB, using the same products in the derived category. -/
theorem derivedTensorProductComparison_single
    (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R)
    (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    let S := DerivedCategory.singleFunctor
      (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
    letI := P.hasProduct A (fun a => S.obj (Q a))
    letI := P.hasProduct A (fun a => (T.tensor.obj K).obj (S.obj (Q a)))
    derivedTensorProductComparison R T K (fun a => S.obj (Q a)) =
      tensorProductComparison T P K A Q := by
  rfl

/-- A countable product is isomorphic to the product over `ULift ℕ` of the same family. -/
private noncomputable def productULiftIso {C : Type*} [Category C] (X : ℕ → C) [HasProduct X]
    [HasProduct fun a : ULift.{w} ℕ => X a.down] :
    (∏ᶜ X) ≅ ∏ᶜ fun a : ULift.{w} ℕ => X a.down where
  hom := Pi.lift fun a => Pi.π X a.down
  inv := Pi.lift fun n => Pi.π (fun a : ULift.{w} ℕ => X a.down) (ULift.up n)
  hom_inv_id := by apply Pi.hom_ext; intro n; simp
  inv_hom_id := by apply Pi.hom_ext; intro a; obtain ⟨n⟩ := a; simp

/-- For pseudo-coherent `K`, the functor `K ⊗ᴸ -` commutes with countable products of
modules in degree zero. -/
theorem isIso_derivedTensorProductComparison_nat
    (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (hK : IsPseudoCoherent K)
    (M : ℕ → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    letI := hasProductsOfShapeNat R P
    let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
    IsIso (derivedTensorProductComparison R T K fun n => S.obj (M n)) := by
  have := hasProductsOfShapeNat R P
  dsimp only
  let S := DerivedCategory.singleFunctor
    (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
  let F := T.tensor.obj K
  let c := derivedTensorProductComparison R T K (fun n => S.obj (M n))
  show IsIso c
  obtain ⟨E, hE, ⟨eK⟩⟩ := id hK
  obtain ⟨b, hb⟩ := hE.upperBound
  let Kminus : DerivedCategory.Minus
      (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :=
    ⟨K, ⟨b, DerivedCategory.TStructure.t.isLE_of_iso eK b⟩⟩
  let A := ULift.{max v w} ℕ
  let EU : A → D.{u, v, w} R := fun a => S.obj (M a.down)
  let := P.hasProduct A EU
  let := P.hasProduct A (fun a => F.obj (EU a))
  let cU := derivedTensorProductComparison R T K EU
  have : IsIso cU := by
    show IsIso (derivedTensorProductComparison R T K (fun a : A => S.obj (M a.down)))
    rw [derivedTensorProductComparison_single R T P K A (fun a => M a.down)]
    have hprod := (pseudoCoherent_iff_derivedTensor_preserves_products T P Kminus 0).1.out 1 2
    exact hprod.mp hK A (fun a => M a.down)
  let eE := productULiftIso (fun n => S.obj (M n))
  let eFE := productULiftIso (fun n => F.obj (S.obj (M n)))
  have hc_eq : c = F.map eE.hom ≫ cU ≫ eFE.inv := by
    apply Pi.hom_ext
    intro n
    have heFE : eFE.inv ≫ Pi.π (fun n => F.obj (S.obj (M n))) n =
        Pi.π (fun a => F.obj (EU a)) (ULift.up n) :=
      Pi.lift_π _ _
    have heE : eE.hom ≫ Pi.π EU (ULift.up n) = Pi.π (fun n => S.obj (M n)) n :=
      Pi.lift_π _ _
    have hcUπ : cU ≫ Pi.π (fun a => F.obj (EU a)) (ULift.up n) =
        F.map (Pi.π EU (ULift.up n)) := by
      simpa [cU, F] using derivedTensorProductComparison_π R T K EU (ULift.up n)
    rw [derivedTensorProductComparison_π, Category.assoc, Category.assoc, heFE,
      hcUπ, ← F.map_comp, heE]
  let : IsIso eE.hom := eE.isIso_hom
  let : IsIso eFE.inv := eFE.isIso_inv
  rw [hc_eq]
  infer_instance

/-- The comparison `derivedTensorProductComparison` intertwines the Milnor maps of `(Eₙ)` and
of `(K ⊗ᴸ Eₙ)`. -/
theorem derivedTensorProductComparison_milnorMap
    (T : DerivedTensorProduct.{u, v, w} R) (K : D.{u, v, w} R)
    [HasProductsOfShape ℕ (D.{u, v, w} R)] (E : ℕ → D.{u, v, w} R)
    (f : ∀ n, E (n + 1) ⟶ E n) :
    (T.tensor.obj K).map (milnorMap E f) ≫ derivedTensorProductComparison R T K E =
      derivedTensorProductComparison R T K E ≫
        milnorMap (fun n => (T.tensor.obj K).obj (E n)) (fun n => (T.tensor.obj K).map (f n)) := by
  let F := T.tensor.obj K
  let : F.CommShift ℤ := T.commShift K
  let : F.IsTriangulated := T.triangulated K
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, derivedTensorProductComparison_π, ← F.map_comp]
  simp only [milnorMap, Pi.lift_π, F.map_sub, F.map_comp]
  rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    derivedTensorProductComparison_π, derivedTensorProductComparison_π_assoc]

/-- **Stacks Project, Tag 0D2L.** Let `K` be pseudo-coherent and `(Mₙ)` an inverse
system of modules. If `L` and `L'` are derived inverse limits of `(Mₙ)` and
`(K ⊗ᴸ Mₙ)`, respectively, then the canonical comparison
`L' ⟶ K ⊗ᴸ L` is an isomorphism. Its displayed equation characterizes it as the
comparison induced by the two Milnor triangles. -/
@[stacks 0D2L]
theorem derivedLimit_tensor_iso
    (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (hK : IsPseudoCoherent K)
    (M : ℕ → ModuleCat.{max v w} (SmallRing.{u, v, w} R))
    (t : ∀ n, M (n + 1) ⟶ M n) :
    letI := hasProductsOfShapeNat R P
    let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
    ∀ (L : D.{u, v, w} R) (ι : L ⟶ ∏ᶜ fun n => S.obj (M n))
      (δ : (∏ᶜ fun n => S.obj (M n)) ⟶ L⟦(1 : ℤ)⟧)
      (_ : IsMilnorTriangle (A := SmallRing.{u, v, w} R) (fun n => S.obj (M n))
        (fun n => S.map (t n)) L ι δ)
      (L' : D.{u, v, w} R)
      (ι' : L' ⟶ ∏ᶜ fun n => (T.tensor.obj K).obj (S.obj (M n)))
      (δ' : (∏ᶜ fun n => (T.tensor.obj K).obj (S.obj (M n))) ⟶ L'⟦(1 : ℤ)⟧)
      (_ : IsMilnorTriangle (A := SmallRing.{u, v, w} R)
        (fun n => (T.tensor.obj K).obj (S.obj (M n)))
        (fun n => (T.tensor.obj K).map (S.map (t n))) L' ι' δ'),
      ∃ e : L' ≅ (T.tensor.obj K).obj L,
        e.hom ≫ (T.tensor.obj K).map ι ≫
          derivedTensorProductComparison R T K (fun n => S.obj (M n)) = ι' := by
  let := hasProductsOfShapeNat R P
  dsimp only
  intro L ι δ hL L' ι' δ' hL'
  let S := DerivedCategory.singleFunctor
    (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
  let F := T.tensor.obj K
  let c := derivedTensorProductComparison R T K (fun n => S.obj (M n))
  have hc : IsIso c := isIso_derivedTensorProductComparison_nat R T P K hK M
  obtain ⟨cinv, hc₁, hc₂⟩ := hc.out
  let ci : _ ≅ _ := ⟨c, cinv, hc₁, hc₂⟩
  let : F.CommShift ℤ := T.commShift K
  let : F.IsTriangulated := T.triangulated K
  have hcomm :
      F.map (milnorMap (fun n => S.obj (M n)) (fun n => S.map (t n))) ≫ c =
        c ≫ milnorMap (fun n => F.obj (S.obj (M n))) (fun n => F.map (S.map (t n))) :=
    derivedTensorProductComparison_milnorMap R T K _ _
  let tri := Triangle.mk ι
    (milnorMap (fun n => S.obj (M n)) (fun n => S.map (t n))) δ
  let tri' := Triangle.mk ι'
    (milnorMap (fun n => F.obj (S.obj (M n))) (fun n => F.map (S.map (t n)))) δ'
  have hmap : F.mapTriangle.obj tri ∈ distinguishedTriangles := F.map_distinguished tri hL
  have hsquare : tri'.mor₂ ≫ ci.inv = ci.inv ≫ (F.mapTriangle.obj tri).mor₂ := by
    change
      milnorMap (fun n => F.obj (S.obj (M n))) (fun n => F.map (S.map (t n))) ≫ cinv =
        cinv ≫ F.map (milnorMap (fun n => S.obj (M n)) (fun n => S.map (t n)))
    rw [← cancel_epi c, ← Category.assoc, ← hcomm, Category.assoc, reassoc_of% hc₁, hc₁,
      Category.comp_id]
  obtain ⟨f, hf, hf'⟩ :=
    complete_distinguished_triangle_morphism₁ tri' (F.mapTriangle.obj tri) hL' hmap
      ci.inv ci.inv hsquare
  unfold Functor.mapTriangle at f
  change L' ⟶ F.obj L at f
  let φ : tri' ⟶ F.mapTriangle.obj tri :=
    Triangle.homMk tri' (F.mapTriangle.obj tri) f ci.inv ci.inv hf hsquare hf'
  have : IsIso f := isIso₁_of_isIso₂₃ φ hL' hmap ci.isIso_inv ci.isIso_inv
  refine ⟨asIso f, ?_⟩
  unfold Functor.mapTriangle at hf
  change ι' ≫ cinv = f ≫ F.map ι at hf
  show f ≫ F.map ι ≫ c = ι'
  rw [← Category.assoc, ← hf, Category.assoc, hc₂, Category.comp_id]

end Stacks.PseudoCoherent.DerivedInverseLimit

end
