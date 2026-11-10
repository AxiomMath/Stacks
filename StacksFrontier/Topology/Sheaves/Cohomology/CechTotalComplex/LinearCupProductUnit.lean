module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductAugmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProductRefinement

/-!
# The Čech cup product with an augmented class in degree zero

Let `W : ι → C` be a family of objects of a category with finite products and a terminal object
`Z`, let `R` be a commutative ring and let `μ : P ⊗_R Q ⟶ P` be a pairing of presheaves of
`R`-modules. If a section `σ` of `Q` over `Z` acts as the identity — `μ(x ⊗ σ|_V) = x` for every
local section `x` of `P` — then the Alexander--Whitney product of [Stacks, Tag 07MB] of a Čech
cochain of `P` with the augmentation of `σ` is that cochain: a unit for the pairing gives a unit
for the cup product.

## Main definitions

* `Stacks.Cech.LinearCupProduct.rightUnitMap`: the map `M ⊗_R R ⟶ M`, `x ⊗ r ↦ r • x`.

## Main results

* `Stacks.Cech.LinearCupProduct.cechAlexanderWhitney_augmentation_right`: the Alexander--Whitney
  product of a Čech cochain with the augmentation of a unit is the cochain.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap tensorModulesMap_comp)
open scoped TensorProduct

universe u w uC vC uR

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

section Unit

variable {R : Type u} [CommRing R]

/-- The right unit map `M ⊗_R R ⟶ M`, `x ⊗ r ↦ r • x`. -/
noncomputable def rightUnitMap (M : ModuleCat.{u} R) :
    ((tensorModules R).obj M).obj (ModuleCat.of R R) ⟶ M :=
  ModuleCat.ofHom (TensorProduct.rid R M).toLinearMap

/-- The right unit map on a pure tensor. -/
@[simp]
theorem rightUnitMap_tmul (M : ModuleCat.{u} R) (x : M) (r : R) :
    (rightUnitMap M).hom (x ⊗ₜ r) = r • x :=
  TensorProduct.rid_tmul x r

/-- The inclusion `M ⟶ M ⊗_R R`, `x ↦ x ⊗ 1`. -/
noncomputable def rightUnitInv (M : ModuleCat.{u} R) :
    M ⟶ ((tensorModules R).obj M).obj (ModuleCat.of R R) :=
  ModuleCat.ofHom (TensorProduct.rid R M).symm.toLinearMap

/-- The inverse of the right unit map is a left inverse. -/
@[simp]
theorem rightUnitInv_rightUnitMap (M : ModuleCat.{u} R) :
    rightUnitInv M ≫ rightUnitMap M = 𝟙 M := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (TensorProduct.rid R M).apply_symm_apply x

/-- The inclusion `x ↦ x ⊗ 1` is natural. -/
@[reassoc]
theorem rightUnitInv_tensorModulesMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    rightUnitInv M ≫ tensorModulesMap R f (𝟙 (ModuleCat.of R R)) = f ≫ rightUnitInv N := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change TensorProduct.map f.hom LinearMap.id ((TensorProduct.rid R M).symm x) =
    (TensorProduct.rid R N).symm (f x)
  rw [TensorProduct.rid_symm_apply, TensorProduct.rid_symm_apply, TensorProduct.map_tmul]
  rfl

/-- The right unit map is natural. -/
theorem tensorModulesMap_rightUnitMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorModulesMap R f (𝟙 (ModuleCat.of R R)) ≫ rightUnitMap N = rightUnitMap M ≫ f := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x r => ?_)
  change (rightUnitMap N).hom (f x ⊗ₜ r) = f ((rightUnitMap M).hom (x ⊗ₜ r))
  rw [rightUnitMap_tmul, rightUnitMap_tmul, map_smul]

end Unit

section Total

variable {A : Type*} [Category* A] [Preadditive A]

/-- **A bicomplex concentrated in second degree zero**: the inclusion of the summand `(n, 0)`
into the total complex in degree `n` is an isomorphism. -/
theorem isIso_ιTotal_of_isZero (B : HomologicalComplex₂ A (up ℤ) (up ℤ))
    [B.HasTotal (up ℤ)] (hB : ∀ p q : ℤ, q ≠ 0 → IsZero ((B.X p).X q)) (n : ℤ) :
    IsIso (B.ιTotal (up ℤ) n 0 n (add_zero n)) := by
  refine ⟨B.totalDesc (fun p q h => if hq : q = 0 then
    eqToHom (by
      obtain rfl := hq
      obtain rfl : p = n := by simpa using h
      rfl) else 0), ?_, ?_⟩
  · rw [HomologicalComplex₂.ι_totalDesc, dite_eq_left rfl, eqToHom_refl]
  · refine HomologicalComplex₂.total.hom_ext (up ℤ) (fun p q h => ?_)
    rw [HomologicalComplex₂.ι_totalDesc_assoc, Category.comp_id]
    by_cases hq : q = 0
    · subst hq
      obtain rfl : p = n := by simpa using h
      rw [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · exact (hB p q hq).eq_of_src _ _

end Total

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type u) [CommRing R]
  {Z : C} (hZ : IsTerminal Z)

/-- Restricting along the identity reindexing is the projection. -/
theorem cechFaceRestriction_id (P : PresheafModules.{u} C R) {p : ℕ} (t : Fin (p + 1) → ι) :
    cechFaceRestriction W R P (id : Fin (p + 1) → Fin (p + 1)) t = π W P p t := by
  dsimp only [cechFaceRestriction]
  rw [interMap_id, op_id]
  exact (congrArg (fun g => π W P p (t ∘ id) ≫ g) (P.map_id _)).trans (Category.comp_id _)

/-- **The Alexander--Whitney product with the augmentation of a unit.** If a section `σ` of `Q`
over the terminal object acts as the identity under `μ`, then pairing a Čech cochain of `P` with
the augmentation of `σ` returns the cochain. -/
theorem cechAlexanderWhitney_augmentation_right {P Q : PresheafModules.{u} C R}
    (μ : Pairing.{u} R P Q P) (σ : ModuleCat.of R R ⟶ Q.obj (op Z))
    (hμ : ∀ V : C, tensorModulesMap R (𝟙 (P.obj (op V))) (σ ≫ Q.map (hZ.from V).op) ≫
      μ.app (op V) = rightUnitMap (P.obj (op V))) (r : ℕ) :
    tensorModulesMap R (𝟙 (cechCochains W R P r)) (σ ≫ cechAugmentationCochains W R hZ Q) ≫
        cechAlexanderWhitney W R μ r 0 = rightUnitMap (cechCochains W R P r) := by
  refine hom_ext W P fun t => ?_
  rw [Category.assoc, cechAlexanderWhitney_comp_π]
  dsimp only [awTerm]
  rw [← Category.assoc, tensorModulesMap_comp, Category.id_comp, Category.assoc,
    cechAugmentationCochains_comp_cechFaceRestriction]
  have hfront : frontIdx r (r + 0) (by omega) = (id : Fin (r + 1) → Fin (r + 1)) := rfl
  rw [hfront, cechFaceRestriction_id]
  have := hμ (inter W t)
  rw [← Category.comp_id (π W P r t), ← Category.id_comp (σ ≫ _), ← tensorModulesMap_comp,
    Category.assoc, this, tensorModulesMap_rightUnitMap]
  rfl

/-- The Čech cochains with coefficients in a zero presheaf vanish. -/
theorem isZero_cechCochains {P : PresheafModules.{u} C R} (hP : IsZero P) (r : ℕ) :
    IsZero (cechCochains W R P r) := by
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext W P fun t => ?_
  exact ((hP.obj (op (inter W t))).eq_of_tgt _ _)

omit [UnivLE.{w, u}] in
/-- The sign of the Alexander--Whitney summand whose back face is a single vertex is `+1`. -/
theorem cupProductSign_back_zero (p : ℕ) :
    Stacks.Cech.CupProduct.cupProductSign ((p : ℤ) + 0) ((p : ℤ) + (0 : ℕ)) (p : ℤ) = 1 := by
  simp only [Stacks.Cech.CupProduct.cupProductSign, Nat.cast_zero, add_zero]
  rw [Int.negOnePow_even _ ?_, Units.val_one]
  have h := Int.even_mul_succ_self (p : ℤ)
  have e : ((p : ℤ) + p) * p + p * p + p = 2 * (p * p) + p * (p + 1) := by ring
  rw [e]
  exact (even_two_mul _).add h

/-- **The augmentation commutes with refinement**: a section over the terminal object restricted
to the members of `W` and then refined to `W'` is its restriction to the members of `W'`. -/
theorem cechAugmentationCochains_comp_cechRefinement [Quiver.IsThin C] {ι' : Type w} (W' : ι' → C)
    (c : ι' → ι)
    (ρ : ∀ j, W' j ⟶ W (c j)) (P : PresheafModules.{u} C R) :
    cechAugmentationCochains W R hZ P ≫ (cechRefinement W W' R c ρ P).f 0 =
      cechAugmentationCochains W' R hZ P := by
  refine hom_ext W' P fun x => ?_
  rw [Category.assoc, cechRefinement_f_comp_π, ← Category.assoc, cechAugmentationCochains_comp_π,
    ← Functor.map_comp, ← op_comp, cechAugmentationCochains_comp_π]
  exact congrArg (fun g => P.map g.op) (hZ.hom_ext _ _)

variable {K L : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **The Čech cup product with the augmentation of a unit in degree zero is the identity**, at
the level of total Čech complexes: for a pairing `D` of `K` and `L` into `K`, with `K`
concentrated in degree zero, and a section `σ` of `L⁰` over the terminal object acting as the
identity under `D` in bidegree `(0, 0)`, the cup product of any cochain with the augmentation of
`σ` is that cochain. -/
theorem cechCupProduct_augmentation_right (D : ComplexPairing R K L K)
    (hK : ∀ a : ℤ, a ≠ 0 → IsZero (K.X a)) (σ : ModuleCat.of R R ⟶ (L.X 0).obj (op Z))
    (hμ : ∀ V : C, tensorModulesMap R (𝟙 ((K.X 0).obj (op V)))
        (σ ≫ (L.X 0).map (hZ.from V).op) ≫ (D.μ 0 0 0 rfl).app (op V) =
      rightUnitMap ((K.X 0).obj (op V))) (n : ℤ) :
    rightUnitInv _ ≫ tensorModulesMap R (𝟙 (((totalCechComplexFunctor W R).obj K).X n))
        (σ ≫ cechAugmentationCochains W R hZ (L.X 0) ≫ ιTotalCech W R L 0 0) ≫
      HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) n 0 n (add_zero n) ≫
      (cechCupProduct W R D).f n = 𝟙 _ := by
  refine totalCech_hom_ext W R K fun p a hpa => ?_
  by_cases ha : a = 0
  · subst ha
    subst hpa
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hι := cechCupProduct_ι W R D p 0 0 0
    have hAW := cechAlexanderWhitney_augmentation_right W R hZ (D.μ 0 0 0 rfl) σ hμ p
    have hsign := cupProductSign_back_zero p
    have hAW' : tensorModulesMap R (𝟙 (cechCochains W R (K.X 0) p))
        (σ ≫ cechAugmentationCochains W R hZ (L.X 0)) ≫
          cechAlexanderWhitney W R (D.μ 0 0 (0 + 0) rfl) p 0 =
        rightUnitMap (cechCochains W R (K.X 0) p) := hAW
    calc ιTotalCech W R K p 0 ≫ rightUnitInv _ ≫
          tensorModulesMap R (𝟙 _) (σ ≫ cechAugmentationCochains W R hZ (L.X 0) ≫
            ιTotalCech W R L 0 0) ≫
          HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
            ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) _ 0 _ (add_zero _) ≫
          (cechCupProduct W R D).f _
        = rightUnitInv _ ≫ tensorModulesMap R (𝟙 _) (σ ≫ cechAugmentationCochains W R hZ (L.X 0)) ≫
          (tensorModulesMap R (ιTotalCech W R K p 0) (ιTotalCech W R L 0 0) ≫
          HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
            ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)
            ((p : ℤ) + 0) (((0 : ℕ) : ℤ) + 0) (((p : ℤ) + 0) + (((0 : ℕ) : ℤ) + 0)) rfl ≫
          (cechCupProduct W R D).f (((p : ℤ) + 0) + (((0 : ℕ) : ℤ) + 0))) := by
          rw [← rightUnitInv_tensorModulesMap_assoc, tensorModulesMap_comp_assoc,
            tensorModulesMap_comp_assoc]
          simp only [Category.id_comp, Category.comp_id, Category.assoc]
          rfl
      _ = rightUnitInv _ ≫ tensorModulesMap R (𝟙 _) (σ ≫ cechAugmentationCochains W R hZ (L.X 0)) ≫
          (Stacks.Cech.CupProduct.cupProductSign ((p : ℤ) + 0) ((p : ℤ) + (0 : ℕ)) (p : ℤ) •
            (cechAlexanderWhitney W R (D.μ 0 0 (0 + 0) rfl) p 0 ≫
              ιTotalCech W R K (p + 0) (0 + 0) ≫
              eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X)
                (by push_cast; ring)))) := by rw [hι]
      _ = ιTotalCech W R K p 0 := by
          rw [hsign, one_smul, ← Category.assoc (tensorModulesMap R _ _), hAW',
            ← Category.assoc, rightUnitInv_rightUnitMap, Category.id_comp]
          rfl
  · exact (isZero_cechCochains W R (hK a ha) p).eq_of_src _ _

end Stacks.Cech.LinearCupProduct
