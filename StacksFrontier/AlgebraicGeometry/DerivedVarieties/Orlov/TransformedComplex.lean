module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxPairings

/-!
# The transformed complex of [Stacks, Section 0G07]

Let `k` be a field, `X` and `Y` schemes over `k` with `X` proper, `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`
a `k`-linear functor, and `… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0` a resolution of the diagonal by
external tensor products of finite locally free modules ([Stacks, Tag 0FZ2]). By the Künneth
formula in degree zero each differential `ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ → ℰᵢ ⊠ 𝒢ᵢ` is the image of a unique tensor
in `Hom(ℰᵢ₊₁, ℰᵢ) ⊗_k Hom(𝒢ᵢ₊₁, 𝒢ᵢ)`; sending `a ⊗ b` to `a ⊠ F(b)` gives morphisms
`ℰᵢ₊₁ ⊠ F(𝒢ᵢ₊₁) → ℰᵢ ⊠ F(𝒢ᵢ)` on `X ×_k Y`, and they form a complex: this is the complex
(0G0A) of [Stacks, Section 0G07].

## Main definitions

* `AlgebraicGeometry.moduleBoxPairing`: the external tensor product of morphisms of modules as a
  box pairing.
* `AlgebraicGeometry.transformedTerm`, `AlgebraicGeometry.transformedDifferential`: the terms
  `ℰᵢ ⊠ F(𝒢ᵢ)` and the differentials of the transformed complex.

## Main results

* `AlgebraicGeometry.bijective_moduleBoxPairing_κ`: the Künneth formula in degree zero.
* `AlgebraicGeometry.transformedDifferential_comp`: the transformed differentials compose to
  zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- **The external tensor product of morphisms of modules, as a box pairing** on the terms of a
resolution of the diagonal. -/
def moduleBoxPairing (R : DiagonalResolution A.hom) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
    Linear.BoxPairing (k := k) R.left R.right R.boxTerm :=
  letI := modulesLinear k A
  letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  { box := fun _ _ => LinearMap.mk₂ k (fun a b => externalTensorProductMap A.hom A.hom a b)
      (fun a a' b => externalTensorProductMap_add_left A.hom A.hom a a' b)
      (fun r a b => externalTensorProductMap_smul_left k A A r a b)
      (fun a b b' => externalTensorProductMap_add_right A.hom A.hom a b b')
      (fun r a b => externalTensorProductMap_smul_right k A A r a b)
    box_comp := fun _ _ _ a b a' b' => externalTensorProductMap_comp A.hom A.hom a a' b b' }

/-- The map out of the tensor product induced by `moduleBoxPairing`, composed with the formal
pairing, is the additive extension of `(a, b) ↦ a ⊠ b`. -/
theorem moduleBoxPairing_κ_freeAbelianGroupToTensor (R : DiagonalResolution A.hom) (i j : ℕ)
    (z : FreeAbelianGroup (R.FactorPair i j)) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
    (moduleBoxPairing A R).κ i j (freeAbelianGroupToTensor k _ _ z) = R.boxPairing i j z := by
  let := modulesLinear k A
  let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    simp only [freeAbelianGroupToTensor_of, Linear.BoxPairing.κ_tmul]
    exact (FreeAbelianGroup.lift_apply_of _ _).symm
  | neg z hz => simp only [map_neg, hz]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- **The Künneth formula in degree zero**, for the terms of a resolution of the diagonal of a
proper scheme over a field: `Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(𝒢ᵢ, 𝒢ⱼ) ⟶ Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` is
bijective. -/
theorem bijective_moduleBoxPairing_κ [IsProper A.hom] (R : DiagonalResolution A.hom) (i j : ℕ) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
    Function.Bijective ((moduleBoxPairing A R).κ i j) := by
  let := modulesLinear k A
  let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  have h := DiagonalResolution.isTensorPairing_boxPairing A R i j
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun d => ?_⟩
  · obtain ⟨z, rfl⟩ := surjective_freeAbelianGroupToTensor k _ _ t
    rw [moduleBoxPairing_κ_freeAbelianGroupToTensor] at ht
    have hz : z ∈ (R.boxPairing i j).ker := ht
    rw [h.ker_eq] at hz
    exact hz
  · obtain ⟨z, hz⟩ := h.surjective d
    exact ⟨freeAbelianGroupToTensor k _ _ z, by
      rw [moduleBoxPairing_κ_freeAbelianGroupToTensor, hz]⟩

section Transformed

variable (B : Over (Spec (.of k))) (R : DiagonalResolution A.hom)
  (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
  (hG : ∀ i, IsPerfect (X := A.left.toRingedSpace)
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.right i)))

/-- The perfect object `𝒢ᵢ[0]` of `D_perf(𝒪_X)`. -/
abbrev rightPerfect (i : ℕ) : PerfectDerivedCategory A.left :=
  ⟨(DerivedCategory.singleFunctor A.left.Modules 0).obj (R.right i), hG i⟩

/-- `F(𝒢ᵢ)`, read in `D(𝒪_Y)`. -/
abbrev imageOfRight (i : ℕ) : DerivedCategory B.left.Modules :=
  (F.obj (rightPerfect A R hG i)).obj

/-- The morphism `F(b) : F(𝒢ᵢ) ⟶ F(𝒢ⱼ)` attached to a morphism of modules `b : 𝒢ᵢ ⟶ 𝒢ⱼ`. -/
def imageOfRightMap {i j : ℕ} (b : R.right i ⟶ R.right j) :
    imageOfRight A B R F hG i ⟶ imageOfRight A B R F hG j :=
  (F.map (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b))).hom

/-- `F(b ≫ b') = F(b) ≫ F(b')` for morphisms of modules `b : 𝒢ᵢ ⟶ 𝒢ⱼ` and `b' : 𝒢ⱼ ⟶ 𝒢ₗ`. -/
theorem imageOfRightMap_comp {i j l : ℕ} (b : R.right i ⟶ R.right j) (b' : R.right j ⟶ R.right l) :
    imageOfRightMap A B R F hG (b ≫ b') =
      imageOfRightMap A B R F hG b ≫ imageOfRightMap A B R F hG b' := by
  have : (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map (b ≫ b')) :
      rightPerfect A R hG i ⟶ rightPerfect A R hG l) =
      (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b) :
        rightPerfect A R hG i ⟶ rightPerfect A R hG j) ≫
        (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b') :
          rightPerfect A R hG j ⟶ rightPerfect A R hG l) := by
    ext
    simp
  unfold imageOfRightMap
  rw [this, CategoryTheory.Functor.map_comp]
  rfl

variable [F.Additive]

/-- `b ↦ F(b)`, as a `k`-linear map, for a `k`-linear `F`. -/
def imageLinearMap
    (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) (i j : ℕ) :
    letI := modulesLinear k A
    letI := modulesLinear k B
    (R.right i ⟶ R.right j) →ₗ[k] (imageOfRight A B R F hG i ⟶ imageOfRight A B R F hG j) :=
  letI := modulesLinear k A
  letI := modulesLinear k B
  { toFun := imageOfRightMap A B R F hG
    map_add' := fun b b' => by
      have : (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map
          (b + b')) : rightPerfect A R hG i ⟶ rightPerfect A R hG j) =
          ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b) +
            ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b') := by
        ext
        rw [Functor.map_add]
        rfl
      unfold imageOfRightMap
      rw [this, F.map_add]
      rfl
    map_smul' := fun r b => by
      have : (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map
          (r • b)) : rightPerfect A R hG i ⟶ rightPerfect A R hG j) =
          r • ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b) := by
        ext
        rw [Functor.map_smul]
        rfl
      unfold imageOfRightMap
      rw [this, hF.map_smul]
      rfl }

/-- The term `ℰᵢ ⊠ F(𝒢ᵢ)` of the transformed complex on `X ×_k Y`. -/
abbrev transformedTerm (i : ℕ) : DerivedCategory (pullback A.hom B.hom).Modules :=
  derivedBox A.hom B.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left i))
    (imageOfRight A B R F hG i)

/-- **The box pairing `(a, b) ↦ a ⊠ F(b)`** on the terms of the transformed complex. -/
def transformedBoxPairing
    (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
    Linear.BoxPairing (k := k) R.left R.right (transformedTerm A B R F hG) :=
  letI := modulesLinear k A
  letI := modulesLinear k B
  derivedBoxPairing k R.left R.right
    (fun i => (DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left i))
    (imageOfRight A B R F hG)
    (fun _ _ => (DerivedCategory.singleFunctor A.left.Modules 0).mapLinearMap k)
    (fun _ _ _ a a' => (DerivedCategory.singleFunctor A.left.Modules 0).map_comp a a')
    (imageLinearMap A B R F hG hF) (fun _ _ _ b b' => imageOfRightMap_comp A B R F hG b b')

variable [IsProper A.hom]

/-- The tensor in `Hom(ℰᵢ₊₁, ℰᵢ) ⊗_k Hom(𝒢ᵢ₊₁, 𝒢ᵢ)` whose image under the Künneth map is the
differential of the resolution of the diagonal. -/
def resolutionTensor (i : ℕ) :
    letI := modulesLinear k A
    (R.left (i + 1) ⟶ R.left i) ⊗[k] (R.right (i + 1) ⟶ R.right i) :=
  letI := modulesLinear k A
  letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  Function.surjInv (bijective_moduleBoxPairing_κ A R (i + 1) i).2 (R.boxDifferential i)

/-- The image of `resolutionTensor` under the Künneth map is the differential
`ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ ⟶ ℰᵢ ⊠ 𝒢ᵢ` of the resolution of the diagonal. -/
theorem moduleBoxPairing_κ_resolutionTensor (i : ℕ) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
    (moduleBoxPairing A R).κ (i + 1) i (resolutionTensor A R i) = R.boxDifferential i :=
  let := modulesLinear k A
  let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  Function.surjInv_eq (bijective_moduleBoxPairing_κ A R (i + 1) i).2 (R.boxDifferential i)

/-- **The differential `ℰᵢ₊₁ ⊠ F(𝒢ᵢ₊₁) ⟶ ℰᵢ ⊠ F(𝒢ᵢ)` of the transformed complex** (0G0A). -/
def transformedDifferential
    (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) (i : ℕ) :
    transformedTerm A B R F hG (i + 1) ⟶ transformedTerm A B R F hG i :=
  letI := modulesLinear k A
  letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
  (transformedBoxPairing A B R F hG hF).κ (i + 1) i (resolutionTensor A R i)

/-- **The transformed differentials compose to zero**, so (0G0A) is a complex. -/
theorem transformedDifferential_comp
    (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) (i : ℕ) :
    transformedDifferential A B R F hG hF (i + 1) ≫ transformedDifferential A B R F hG hF i =
      0 := by
  let := modulesLinear k A
  let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
  let : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
  exact (moduleBoxPairing A R).transport_comp (transformedBoxPairing A B R F hG hF)
    R.boxDifferential R.boxDifferential_comp (resolutionTensor A R)
    (moduleBoxPairing_κ_resolutionTensor A R)
    (fun i => (bijective_moduleBoxPairing_κ A R (i + 2) i).1) i

end Transformed

end AlgebraicGeometry
