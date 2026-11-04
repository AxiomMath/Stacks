module

public import StacksFrontier.Cotangent.IdealTensorSquare
public import StacksFrontier.Cotangent.NaiveComparisonExplicitArrow
public import StacksFrontier.Cotangent.StandardResolutionExactness
public import StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy
public import StacksFrontier.Cotangent.Surjection
import all StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy

/-!
# Products of augmentation ideals in low degrees of the standard resolution

Let `P_• → B` be the standard resolution of an `A`-algebra `B` and `J_n = Ker(P_n → B)`. This
file studies the elements of `J₁²` modulo the boundaries `(d₀ - d₁ + d₂)(J₂²)`: they are
described by `Ker(J₀ ⊗ J₀ → J₀²)`, through the map `H̄ : J₀ ⊗ J₀ → P₁ / (d₀ - d₁ + d₂)(J₂²)`,
`a ⊗ b ↦ ([a] - [0]) ([b] - [0])`, and this map is invariant under homotopies of maps from a
polynomial algebra into `P₀`.

These are the simplicial inputs of the computation of `H^{-2}` in [Stacks, Tag 09CG].

## Main definitions

* `CommAlgCat.standardResolutionContract`: the map `p ↦ [p] - [0]` from `P_n` to `P_{n+1}`.
* `CommAlgCat.faceSumTwo`: the alternating sum `d₀ - d₁ + d₂ : P₂ → P₁`.
* `CommAlgCat.boundaryOfSquares`: the subgroup `(d₀ - d₁ + d₂)(J₂²)` of `P₁`.
* `CommAlgCat.squareClass`: the map `H̄`.

## Main results

* `CommAlgCat.exists_squareClass_eq`: every element of `J₁²` is, modulo
  `(d₀ - d₁ + d₂)(J₂²)`, a value of `H̄` on a tensor whose product is `d₀ z - d₁ z`.
* `CommAlgCat.squareClass_idealTensorMap_eq`: two maps `A[V] → P₀` with the same composite to `B`
  induce the same map through `H̄` on `Ker(I ⊗ I → I²)`.
* `CommAlgCat.squareClass_antisymm`: `H̄` kills antisymmetric tensors.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial TensorProduct Stacks.Cotangent

universe u v w

noncomputable section

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### Elementary identities -/

/-- The augmentation is compatible with every degeneracy. -/
theorem standardResolution_augmentation_σ (n : ℕ) (i : Fin (n + 1))
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).hom.app (op ⦋n + 1⦌) ((standardResolution A B).left.σ i p) =
      (standardResolution A B).hom.app (op ⦋n⦌) p := by
  have hnat : (standardResolution A B).left.σ i ≫ (standardResolution A B).hom.app (op ⦋n + 1⦌) =
      (standardResolution A B).hom.app (op ⦋n⦌) :=
    (standardResolution A B).hom.naturality (SimplexCategory.σ i).op
  rw [← hnat, CommAlgCat.comp_apply]

/-- Every degeneracy maps `J_n` into `J_{n+1}`. -/
theorem σ_mem_augmentationIdeal (n : ℕ) (i : Fin (n + 1))
    (p : (standardResolution A B).left.obj (op ⦋n⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋n⦌)) :
    (standardResolution A B).left.σ i p ∈ augmentationIdeal A B (op ⦋n + 1⦌) :=
  (standardResolution_augmentation_σ A B n i p).trans hp

/-- The augmentation of the variable `[q]` is the augmentation of `q`. -/
theorem standardResolution_augmentation_standardResolutionX (n : ℕ)
    (q : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).hom.app (op ⦋n + 1⦌) (standardResolutionX A B n q) =
      (standardResolution A B).hom.app (op ⦋n⦌) q := by
  rw [← standardResolution_augmentation_δ A B n 0, standardResolution_δ_zero_X]

variable {A B} in
/-- If `f ≫ g = h`, then `g (f x) = h x`. -/
theorem apply_of_comp_eq {X Y Z : CommAlgCat.{max u v} A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e, CommAlgCat.comp_apply]

/-- `d₀ (s_i p) = p` for the face `d_{castSucc i}`. -/
private theorem δ_castSucc_σ_apply (n : ℕ) (i : Fin (n + 1))
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.δ i.castSucc ((standardResolution A B).left.σ i p) = p :=
  apply_of_comp_eq (standardResolution A B).left.δ_comp_σ_self p

/-- `d_{i+1} (s_i p) = p`. -/
private theorem δ_succ_σ_apply (n : ℕ) (i : Fin (n + 1))
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.δ i.succ ((standardResolution A B).left.σ i p) = p :=
  apply_of_comp_eq (standardResolution A B).left.δ_comp_σ_succ p

/-! ### The contraction `p ↦ [p] - [0]` -/

/-- The element `[p] - [0]` of `P_{n+1}`. -/
def standardResolutionContract (n : ℕ) (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.obj (op ⦋n + 1⦌) :=
  standardResolutionX A B n p - standardResolutionX A B n 0

/-- `d₀ ([p] - [0]) = p`. -/
theorem δ_zero_standardResolutionContract (n : ℕ)
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.δ (0 : Fin (n + 2)) (standardResolutionContract A B n p) = p := by
  rw [standardResolutionContract, map_sub, standardResolution_δ_zero_X,
    standardResolution_δ_zero_X, sub_zero]

/-- For `p ∈ J₀`, `d₁ ([p] - [0]) = 0` in `P₀`. -/
theorem δ_one_standardResolutionContract_zero (p : (standardResolution A B).left.obj (op ⦋0⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋0⦌)) :
    (standardResolution A B).left.δ (1 : Fin 2) (standardResolutionContract A B 0 p) = 0 := by
  rw [standardResolutionContract, map_sub, standardResolution_δ_one_X, standardResolution_δ_one_X]
  have : standardResolutionAugmentationHom A B (op ⦋0⦌) p =
      standardResolutionAugmentationHom A B (op ⦋0⦌) 0 := by
    rwa [map_zero]
  rw [this, sub_self]

/-- For `x ∈ P₁` and `i ∈ {0, 1}`, `d_{i+1} ([x] - [0]) = [d_i x] - [0]`. -/
theorem δ_succ_standardResolutionContract_one (i : Fin 2)
    (x : (standardResolution A B).left.obj (op ⦋1⦌)) :
    (standardResolution A B).left.δ i.succ (standardResolutionContract A B 1 x) =
      standardResolutionContract A B 0 ((standardResolution A B).left.δ i x) := by
  rw [standardResolutionContract, map_sub, standardResolution_δ_succ_X,
    standardResolution_δ_succ_X, map_zero, standardResolutionContract]

/-- For `p ∈ J_n`, the element `[p] - [0]` lies in `J_{n+1}`. -/
theorem standardResolutionContract_mem (n : ℕ) (p : (standardResolution A B).left.obj (op ⦋n⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋n⦌)) :
    standardResolutionContract A B n p ∈ augmentationIdeal A B (op ⦋n + 1⦌) := by
  show (standardResolution A B).hom.app (op ⦋n + 1⦌) _ = 0
  rwa [standardResolutionContract, map_sub, standardResolution_augmentation_standardResolutionX,
    standardResolution_augmentation_standardResolutionX, map_zero, sub_zero]

/-! ### The alternating sum of the faces out of degree two -/

/-- The alternating sum `d₀ - d₁ + d₂ : P₂ → P₁`. -/
def faceSumTwo :
    (standardResolution A B).left.obj (op ⦋2⦌) →+ (standardResolution A B).left.obj (op ⦋1⦌) :=
  ((standardResolution A B).left.δ (0 : Fin 3)).hom.toRingHom.toAddMonoidHom -
    ((standardResolution A B).left.δ (1 : Fin 3)).hom.toRingHom.toAddMonoidHom +
    ((standardResolution A B).left.δ (2 : Fin 3)).hom.toRingHom.toAddMonoidHom

/-- `(d₀ - d₁ + d₂) y = d₀ y - d₁ y + d₂ y`. -/
theorem faceSumTwo_apply (y : (standardResolution A B).left.obj (op ⦋2⦌)) :
    faceSumTwo A B y = (standardResolution A B).left.δ (0 : Fin 3) y -
      (standardResolution A B).left.δ (1 : Fin 3) y +
      (standardResolution A B).left.δ (2 : Fin 3) y := rfl

/-- `(d₀ - d₁ + d₂)(([a] - [0])([b] - [0])) = ab - ([d₀ a] - [0])([d₀ b] - [0]) +
([d₁ a] - [0])([d₁ b] - [0])`. -/
theorem faceSumTwo_contract_mul (a b : (standardResolution A B).left.obj (op ⦋1⦌)) :
    faceSumTwo A B (standardResolutionContract A B 1 a * standardResolutionContract A B 1 b) =
      a * b - standardResolutionContract A B 0 ((standardResolution A B).left.δ 0 a) *
          standardResolutionContract A B 0 ((standardResolution A B).left.δ 0 b) +
        standardResolutionContract A B 0 ((standardResolution A B).left.δ 1 a) *
          standardResolutionContract A B 0 ((standardResolution A B).left.δ 1 b) := by
  rw [faceSumTwo_apply, map_mul, map_mul, map_mul, δ_zero_standardResolutionContract,
    δ_zero_standardResolutionContract,
    show (1 : Fin 3) = (0 : Fin 2).succ from rfl, show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    δ_succ_standardResolutionContract_one, δ_succ_standardResolutionContract_one,
    δ_succ_standardResolutionContract_one, δ_succ_standardResolutionContract_one]

/-- The shuffle identity: for `d` with both faces zero and `y` with `d₁ y = 0`,
`(d₀ - d₁ + d₂)(s₁ d · s₀ y) = -d y`. -/
theorem faceSumTwo_σ_mul (d y : (standardResolution A B).left.obj (op ⦋1⦌))
    (hd₀ : (standardResolution A B).left.δ 0 d = 0) (hd₁ : (standardResolution A B).left.δ 1 d = 0)
    (hy : (standardResolution A B).left.δ 1 y = 0) :
    faceSumTwo A B ((standardResolution A B).left.σ 1 d * (standardResolution A B).left.σ 0 y) =
      -(d * y) := by
  let X := (standardResolution A B).left
  have h00 : X.δ (0 : Fin 3) (X.σ 0 y) = y :=
    δ_castSucc_σ_apply A B 1 0 y
  have h10 : X.δ (1 : Fin 3) (X.σ 0 y) = y :=
    δ_succ_σ_apply A B 1 0 y
  have h20 : X.δ (2 : Fin 3) (X.σ 0 y) = X.σ 0 (X.δ 1 y) :=
    (apply_of_comp_eq (X.δ_comp_σ_of_gt (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide))
      y).trans (CommAlgCat.comp_apply _ _ _)
  have h01 : X.δ (0 : Fin 3) (X.σ 1 d) = X.σ 0 (X.δ 0 d) :=
    (apply_of_comp_eq (X.δ_comp_σ_of_le (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide))
      d).trans (CommAlgCat.comp_apply _ _ _)
  have h11 : X.δ (1 : Fin 3) (X.σ 1 d) = d :=
    δ_castSucc_σ_apply A B 1 1 d
  have h21 : X.δ (2 : Fin 3) (X.σ 1 d) = d :=
    δ_succ_σ_apply A B 1 1 d
  rw [faceSumTwo_apply, map_mul, map_mul, map_mul]
  show X.δ 0 (X.σ 1 d) * X.δ 0 (X.σ 0 y) - X.δ 1 (X.σ 1 d) * X.δ 1 (X.σ 0 y) +
    X.δ 2 (X.σ 1 d) * X.δ 2 (X.σ 0 y) = _
  rw [h00, h10, h20, h01, h11, h21]
  show X.σ 0 (X.δ 0 d) * y - d * y + d * X.σ 0 (X.δ 1 y) = _
  rw [hd₀, hy, map_zero, zero_mul, mul_zero, zero_sub, add_zero]

/-- The subgroup `(d₀ - d₁ + d₂)(J₂²)` of `P₁`. -/
def boundaryOfSquares : AddSubgroup ((standardResolution A B).left.obj (op ⦋1⦌)) :=
  ((augmentationIdeal A B (op ⦋2⦌) ^ 2).toAddSubgroup).map (faceSumTwo A B)

/-- For `y ∈ J₂²`, the element `(d₀ - d₁ + d₂) y` lies in `(d₀ - d₁ + d₂)(J₂²)`. -/
theorem faceSumTwo_mem_boundaryOfSquares (y : (standardResolution A B).left.obj (op ⦋2⦌))
    (hy : y ∈ augmentationIdeal A B (op ⦋2⦌) ^ 2) :
    faceSumTwo A B y ∈ boundaryOfSquares A B :=
  ⟨y, hy, rfl⟩

/-- A product `d y` with `d` a cycle killed by both faces and `d₁ y = 0` is a boundary of a
square. -/
theorem mul_mem_boundaryOfSquares (d y : (standardResolution A B).left.obj (op ⦋1⦌))
    (hd : d ∈ augmentationIdeal A B (op ⦋1⦌)) (hy : y ∈ augmentationIdeal A B (op ⦋1⦌))
    (hd₀ : (standardResolution A B).left.δ 0 d = 0) (hd₁ : (standardResolution A B).left.δ 1 d = 0)
    (hy₁ : (standardResolution A B).left.δ 1 y = 0) :
    d * y ∈ boundaryOfSquares A B := by
  rw [← neg_neg (d * y), ← faceSumTwo_σ_mul A B d y hd₀ hd₁ hy₁]
  refine neg_mem (faceSumTwo_mem_boundaryOfSquares A B _ ?_)
  rw [pow_two]
  exact Ideal.mul_mem_mul (σ_mem_augmentationIdeal A B 1 1 d hd)
    (σ_mem_augmentationIdeal A B 1 0 y hy)

/-! ### The map `H̄` -/

/-- `J₀ = Ker(P₀ → B)`. -/
abbrev augmentationIdealZero := augmentationIdeal A B (op ⦋0⦌)

/-- For `a, b ∈ J₀`, the element `([a + b] - [0]) - ([a] - [0]) - ([b] - [0])` of `P₁` lies in
`J₁` and is killed by both faces `d₀` and `d₁`. -/
theorem contract_add_sub (a b : (standardResolution A B).left.obj (op ⦋0⦌))
    (ha : a ∈ augmentationIdeal A B (op ⦋0⦌)) (hb : b ∈ augmentationIdeal A B (op ⦋0⦌)) :
    standardResolutionContract A B 0 (a + b) - standardResolutionContract A B 0 a -
        standardResolutionContract A B 0 b ∈ augmentationIdeal A B (op ⦋1⦌) ∧
      (standardResolution A B).left.δ 0 (standardResolutionContract A B 0 (a + b) -
        standardResolutionContract A B 0 a - standardResolutionContract A B 0 b) = 0 ∧
      (standardResolution A B).left.δ 1 (standardResolutionContract A B 0 (a + b) -
        standardResolutionContract A B 0 a - standardResolutionContract A B 0 b) = 0 := by
  have hab := Ideal.add_mem _ ha hb
  refine ⟨Ideal.sub_mem _ (Ideal.sub_mem _ (standardResolutionContract_mem A B 0 _ hab)
    (standardResolutionContract_mem A B 0 _ ha)) (standardResolutionContract_mem A B 0 _ hb),
    ?_, ?_⟩
  · rw [map_sub, map_sub, δ_zero_standardResolutionContract, δ_zero_standardResolutionContract,
      δ_zero_standardResolutionContract]
    abel
  · rw [map_sub, map_sub, δ_one_standardResolutionContract_zero A B _ hab,
      δ_one_standardResolutionContract_zero A B _ ha,
      δ_one_standardResolutionContract_zero A B _ hb, sub_zero, sub_zero]

/-- For `r ∈ P₀` and `a ∈ J₀`, the element `([r a] - [0]) - s₀ r ([a] - [0])` of `P₁` lies in
`J₁` and is killed by both faces `d₀` and `d₁`. -/
theorem contract_smul_sub (r a : (standardResolution A B).left.obj (op ⦋0⦌))
    (ha : a ∈ augmentationIdeal A B (op ⦋0⦌)) :
    standardResolutionContract A B 0 (r * a) - (standardResolution A B).left.σ 0 r *
        standardResolutionContract A B 0 a ∈ augmentationIdeal A B (op ⦋1⦌) ∧
      (standardResolution A B).left.δ 0 (standardResolutionContract A B 0 (r * a) -
        (standardResolution A B).left.σ 0 r * standardResolutionContract A B 0 a) = 0 ∧
      (standardResolution A B).left.δ 1 (standardResolutionContract A B 0 (r * a) -
        (standardResolution A B).left.σ 0 r * standardResolutionContract A B 0 a) = 0 := by
  let X := (standardResolution A B).left
  have h0 : X.δ (0 : Fin 2) (X.σ 0 r) = r := δ_castSucc_σ_apply A B 0 0 r
  have h1 : X.δ (1 : Fin 2) (X.σ 0 r) = r := δ_succ_σ_apply A B 0 0 r
  have hra : r * a ∈ augmentationIdeal A B (op ⦋0⦌) := Ideal.mul_mem_left _ _ ha
  refine ⟨Ideal.sub_mem _ (standardResolutionContract_mem A B 0 _ hra)
    (Ideal.mul_mem_left _ _ (standardResolutionContract_mem A B 0 _ ha)), ?_, ?_⟩
  · show X.δ 0 _ = 0
    rw [map_sub, map_mul, h0, δ_zero_standardResolutionContract,
      δ_zero_standardResolutionContract, sub_self]
  · show X.δ 1 _ = 0
    rw [map_sub, map_mul, h1, δ_one_standardResolutionContract_zero A B _ hra,
      δ_one_standardResolutionContract_zero A B _ ha, mul_zero, sub_zero]

/-- The map `H̄ : J₀ ⊗_{P₀} J₀ → P₁ / (d₀ - d₁ + d₂)(J₂²)`, sending `a ⊗ b` to the class of
`([a] - [0])([b] - [0])`. -/
def squareClass :
    augmentationIdealZero A B ⊗[(standardResolution A B).left.obj (op ⦋0⦌)]
        augmentationIdealZero A B →+
      (standardResolution A B).left.obj (op ⦋1⦌) ⧸ boundaryOfSquares A B :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
        (fun b => QuotientAddGroup.mk (standardResolutionContract A B 0 a *
          standardResolutionContract A B 0 b))
        (fun b b' => by
          rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
          obtain ⟨h1, h2, h3⟩ := contract_add_sub A B b b' b.2 b'.2
          convert mul_mem_boundaryOfSquares A B _ _ h1
            (standardResolutionContract_mem A B 0 _ a.2) h2 h3
            (δ_one_standardResolutionContract_zero A B _ a.2) using 1
          rw [Submodule.coe_add]
          ring))
      (fun a a' => by
        ext b
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
        obtain ⟨h1, h2, h3⟩ := contract_add_sub A B a a' a.2 a'.2
        convert mul_mem_boundaryOfSquares A B _ _ h1
          (standardResolutionContract_mem A B 0 _ b.2) h2 h3
          (δ_one_standardResolutionContract_zero A B _ b.2) using 1
        rw [Submodule.coe_add]
        ring))
    (fun r a b => by
      simp only [AddMonoidHom.mk'_apply]
      rw [QuotientAddGroup.eq_iff_sub_mem]
      obtain ⟨h1, h2, h3⟩ := contract_smul_sub A B r a a.2
      obtain ⟨h1', h2', h3'⟩ := contract_smul_sub A B r b b.2
      have e1 := mul_mem_boundaryOfSquares A B _ _ h1
        (standardResolutionContract_mem A B 0 _ b.2) h2 h3
        (δ_one_standardResolutionContract_zero A B _ b.2)
      have e2 := mul_mem_boundaryOfSquares A B _ _ h1'
        (standardResolutionContract_mem A B 0 _ a.2) h2' h3'
        (δ_one_standardResolutionContract_zero A B _ a.2)
      convert sub_mem e1 e2 using 1
      rw [Submodule.coe_smul, Submodule.coe_smul, smul_eq_mul, smul_eq_mul]
      ring)

/-- `H̄ (a ⊗ b)` is the class of `([a] - [0])([b] - [0])`. -/
@[simp]
theorem squareClass_tmul (a b : augmentationIdealZero A B) :
    squareClass A B (a ⊗ₜ b) = QuotientAddGroup.mk (standardResolutionContract A B 0 a *
      standardResolutionContract A B 0 b) := rfl

/-- **Every element of `J₁²` is a value of `H̄` modulo boundaries of squares**, on a tensor whose
product is `d₀ z - d₁ z`. -/
theorem exists_squareClass_eq (z : (standardResolution A B).left.obj (op ⦋1⦌))
    (hz : z ∈ augmentationIdeal A B (op ⦋1⦌) ^ 2) :
    ∃ ξ : augmentationIdealZero A B ⊗[(standardResolution A B).left.obj (op ⦋0⦌)]
        augmentationIdealZero A B,
      idealTensorMul _ ξ = (standardResolution A B).left.δ 0 z -
          (standardResolution A B).left.δ 1 z ∧
        squareClass A B ξ = QuotientAddGroup.mk z := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    let a₀ : augmentationIdealZero A B := ⟨_, delta_mem_augmentationIdeal A B 0 0 a ha⟩
    let a₁ : augmentationIdealZero A B := ⟨_, delta_mem_augmentationIdeal A B 0 1 a ha⟩
    let b₀ : augmentationIdealZero A B := ⟨_, delta_mem_augmentationIdeal A B 0 0 b hb⟩
    let b₁ : augmentationIdealZero A B := ⟨_, delta_mem_augmentationIdeal A B 0 1 b hb⟩
    refine ⟨a₀ ⊗ₜ b₀ - a₁ ⊗ₜ b₁, ?_, ?_⟩
    · rw [map_sub, idealTensorMul_tmul, idealTensorMul_tmul, map_mul, map_mul]
    · rw [map_sub, squareClass_tmul, squareClass_tmul, ← QuotientAddGroup.mk_sub, eq_comm,
        QuotientAddGroup.eq_iff_sub_mem]
      have := faceSumTwo_mem_boundaryOfSquares A B
        (standardResolutionContract A B 1 a * standardResolutionContract A B 1 b) (by
          rw [pow_two]
          exact Ideal.mul_mem_mul (standardResolutionContract_mem A B 1 a ha)
            (standardResolutionContract_mem A B 1 b hb))
      rw [faceSumTwo_contract_mul] at this
      convert this using 1
      simp only [a₀, a₁, b₀, b₁]
      abel
  · rintro x y ⟨ξ, hξ1, hξ2⟩ ⟨η, hη1, hη2⟩
    refine ⟨ξ + η, ?_, ?_⟩
    · rw [map_add, hξ1, hη1, map_add, map_add]
      abel
    · rw [map_add, hξ2, hη2, QuotientAddGroup.mk_add]

/-- **`H̄` kills antisymmetric tensors.** -/
theorem squareClass_antisymm {ξ : augmentationIdealZero A B ⊗[(standardResolution A B).left.obj
      (op ⦋0⦌)] augmentationIdealZero A B} (hξ : ξ ∈ idealTensorAntisymm _) :
    squareClass A B ξ = 0 := by
  suffices H : ∀ r : (standardResolution A B).left.obj (op ⦋0⦌), squareClass A B (r • ξ) = 0 by
    simpa using H 1
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hξ
  · rintro _ ⟨⟨a, b⟩, rfl⟩ r
    rw [smul_sub, TensorProduct.smul_tmul' r a b, ← TensorProduct.tmul_smul r b a, map_sub,
      squareClass_tmul, squareClass_tmul, mul_comm, sub_self]
  · intro x y _ _ hx hy r
    rw [smul_add, map_add, hx, hy, add_zero]
  · intro s x _ hx r
    rw [smul_smul]
    exact hx _

/-- **Homotopy invariance of `H̄`, given the homotopy.** Let `φ₁, φ₂ : Q → P₀` be `A`-algebra maps
sending an ideal `I` into `J₀`, and let `E : Q → P₁` be an `A`-algebra map with `d₀ E = φ₁` and
`d₁ E = φ₂`. Then `φ₁` and `φ₂` induce, through `H̄`, the same map on `Ker(I ⊗ I → I²)`. -/
theorem squareClass_idealTensorMap_eq_of_homotopy {Q : Type w} [CommRing Q] [Algebra A Q]
    {I : Ideal Q} (φ₁ φ₂ : Q →ₐ[A] (standardResolution A B).left.obj (op ⦋0⦌))
    (E : Q →ₐ[A] (standardResolution A B).left.obj (op ⦋1⦌))
    (hEd : ∀ a, (standardResolution A B).left.δ 0 (E a) = φ₁ a)
    (hEd₁ : ∀ a, (standardResolution A B).left.δ 1 (E a) = φ₂ a)
    (h₁ : ∀ a ∈ I, φ₁.toRingHom a ∈ augmentationIdealZero A B)
    (h₂ : ∀ a ∈ I, φ₂.toRingHom a ∈ augmentationIdealZero A B)
    (ξ : I ⊗[Q] I) (hξ : idealTensorMul I ξ = 0) :
    squareClass A B (idealTensorMap _ h₁ ξ) = squareClass A B (idealTensorMap _ h₂ ξ) := by
  have hEmem : ∀ a ∈ I, E a ∈ augmentationIdeal A B (op ⦋1⦌) := fun a ha => by
    show (standardResolution A B).hom.app (op ⦋1⦌) (E a) = 0
    rw [← standardResolution_augmentation_δ A B 0 0, hEd]
    exact h₁ a ha
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset ξ
  let w : (standardResolution A B).left.obj (op ⦋2⦌) :=
    ∑ p ∈ S, standardResolutionContract A B 1 (E p.1) * standardResolutionContract A B 1 (E p.2)
  have hw : w ∈ augmentationIdeal A B (op ⦋2⦌) ^ 2 := by
    refine Ideal.sum_mem _ fun p _ => ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (standardResolutionContract_mem A B 1 _ (hEmem _ p.1.2))
      (standardResolutionContract_mem A B 1 _ (hEmem _ p.2.2))
  have hmul : (∑ p ∈ S, (p.1 : Q) * p.2) = 0 := by
    rw [map_sum] at hξ
    simpa using hξ
  have key := faceSumTwo_mem_boundaryOfSquares A B w hw
  simp only [w, map_sum, faceSumTwo_contract_mul, hEd, hEd₁] at key
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  have hEsum : ∑ p ∈ S, E p.1 * E p.2 = 0 := by
    simp_rw [← map_mul]
    rw [← map_sum, hmul, map_zero]
  rw [hEsum, zero_sub] at key
  simp only [map_sum, idealTensorMap_tmul, squareClass_tmul, idealRestrict_apply_coe,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simp only [← QuotientAddGroup.mk'_apply (boundaryOfSquares A B), ← map_sum]
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  convert neg_mem key using 1
  abel

/-- **Homotopy invariance of `H̄`.** Two `A`-algebra maps `φ₁, φ₂ : A[V] → P₀` with the same
composite to `B`, sending an ideal `I` into `J₀`, induce through `H̄` the same map on
`Ker(I ⊗ I → I²)`. The homotopy is the map `E : A[V] → P₁` with `d₀ E = φ₁` and `d₁ E = φ₂`. -/
theorem squareClass_idealTensorMap_eq {V : Type w} {I : Ideal (MvPolynomial V A)}
    (φ₁ φ₂ : MvPolynomial V A →ₐ[A] (standardResolution A B).left.obj (op ⦋0⦌))
    (hφ : ∀ x, (standardResolution A B).hom.app (op ⦋0⦌) (φ₁ x) =
      (standardResolution A B).hom.app (op ⦋0⦌) (φ₂ x))
    (h₁ : ∀ a ∈ I, φ₁.toRingHom a ∈ augmentationIdealZero A B)
    (h₂ : ∀ a ∈ I, φ₂.toRingHom a ∈ augmentationIdealZero A B)
    (ξ : I ⊗[MvPolynomial V A] I) (hξ : idealTensorMul I ξ = 0) :
    squareClass A B (idealTensorMap _ h₁ ξ) = squareClass A B (idealTensorMap _ h₂ ξ) := by
  let E : MvPolynomial V A →ₐ[A] (standardResolution A B).left.obj (op ⦋1⦌) :=
    MvPolynomial.aeval fun i => standardResolutionX A B 0 (φ₁ (MvPolynomial.X i)) -
      standardResolutionX A B 0 (φ₂ (MvPolynomial.X i)) +
        (standardResolution A B).left.σ 0 (φ₂ (MvPolynomial.X i))
  have hs0 : ∀ r, (standardResolution A B).left.δ (0 : Fin 2)
      ((standardResolution A B).left.σ 0 r) = r := δ_castSucc_σ_apply A B 0 0
  have hs1 : ∀ r, (standardResolution A B).left.δ (1 : Fin 2)
      ((standardResolution A B).left.σ 0 r) = r := δ_succ_σ_apply A B 0 0
  have hE₀ : ((standardResolution A B).left.δ (0 : Fin 2)).hom.comp E = φ₁ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    show (standardResolution A B).left.δ 0 (E (MvPolynomial.X i)) = _
    simp only [E, MvPolynomial.aeval_X, map_add, map_sub, standardResolution_δ_zero_X, hs0]
    abel
  have hE₁ : ((standardResolution A B).left.δ (1 : Fin 2)).hom.comp E = φ₂ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    show (standardResolution A B).left.δ 1 (E (MvPolynomial.X i)) = _
    simp only [E, MvPolynomial.aeval_X, map_add, map_sub, standardResolution_δ_one_X, hs1]
    rw [show standardResolutionAugmentationHom A B (op ⦋0⦌) (φ₁ (MvPolynomial.X i)) =
      standardResolutionAugmentationHom A B (op ⦋0⦌) (φ₂ (MvPolynomial.X i)) from
        hφ _, sub_self, zero_add]
  exact squareClass_idealTensorMap_eq_of_homotopy A B φ₁ φ₂ E
    (fun a => congrArg (fun f => f a) hE₀) (fun a => congrArg (fun f => f a) hE₁) h₁ h₂ ξ hξ

/-! ### Exactness of the Moore complex in degree two -/

/-- The degree-two case of the exactness of the Moore complex of the standard resolution: if
`(d₀ - d₁ + d₂) y = 0`, then `y` is the alternating sum of the four faces of an element of `P₃`. -/
theorem standardResolution_exists_of_faceSumTwo_eq_zero
    (y : (standardResolution A B).left.obj (op ⦋2⦌)) (hy : faceSumTwo A B y = 0) :
    ∃ z : (standardResolution A B).left.obj (op ⦋3⦌),
      (standardResolution A B).left.δ (0 : Fin 4) z
        - (standardResolution A B).left.δ (1 : Fin 4) z
        + (standardResolution A B).left.δ (2 : Fin 4) z
        - (standardResolution A B).left.δ (3 : Fin 4) z = y := by
  have hex := standardResolutionMooreComplex_exactAt.{u, v} A B 2 two_ne_zero
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)] at hex
  have hd21 : (standardResolutionMooreComplex.{u, v} A B).d 2 1 y = 0 := by
    rwa [standardResolutionMooreComplex_d_two_one]
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 hex y hd21
  refine ⟨z, ?_⟩
  have hd32 : (standardResolutionMooreComplex.{u, v} A B).d 3 2 =
      (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 0 -
          (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 1 +
        (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 2 -
          (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 3 := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_four]
    simp [sub_eq_add_neg]
  change (standardResolutionMooreComplex.{u, v} A B).d 3 2 z = y at hz
  rwa [hd32] at hz

end CommAlgCat

end
