module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Transporting a complex along two compatible box pairings

Let `k` be a commutative ring and let `Eᵢ`, `Gᵢ` be objects of two `k`-linear categories. A
*box pairing* into a `k`-linear category `𝒞` with objects `Pᵢ` is a family of `k`-bilinear maps
`(a, b) ↦ a ⊠ b : Hom(Eᵢ, Eⱼ) × Hom(Gᵢ, Gⱼ) ⟶ Hom(Pᵢ, Pⱼ)` compatible with composition,
`(a ⊠ b) ≫ (a' ⊠ b') = (a ≫ a') ⊠ (b ≫ b')`. It induces `k`-linear maps
`κᵢⱼ : Hom(Eᵢ, Eⱼ) ⊗_k Hom(Gᵢ, Gⱼ) ⟶ Hom(Pᵢ, Pⱼ)` compatible with the composition of tensors.

Given two box pairings over the same `Eᵢ`, `Gᵢ` and a complex `⋯ ⟶ P₂ ⟶ P₁ ⟶ P₀` for the
first whose differentials lie in the image of `κ` and whose composites are detected by `κ`, the
same tensors define a complex for the second. This is how the complex
`⋯ → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)` of [Stacks, Section 0G07] is obtained from a resolution of the
diagonal by the Künneth formula in degree zero.

## Main definitions

* `CategoryTheory.Linear.BoxPairing`: a box pairing.
* `CategoryTheory.Linear.BoxPairing.κ`: the induced map out of the tensor product.
* `CategoryTheory.Linear.tensorComp`: composition of tensors of morphisms.

## Main results

* `CategoryTheory.Linear.BoxPairing.κ_comp`: `κ t ≫ κ s = κ (t ∘ s)`.
* `CategoryTheory.Linear.BoxPairing.transport_comp`: the transported differentials compose to
  zero.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

namespace CategoryTheory.Linear

variable (k : Type*) [CommRing k] {𝒳 𝒢 𝒞 : Type*} [Category* 𝒳] [Category* 𝒢] [Category* 𝒞]
  [Preadditive 𝒳] [Preadditive 𝒢] [Preadditive 𝒞] [Linear k 𝒳] [Linear k 𝒢] [Linear k 𝒞]

/-- The composition of tensors of morphisms:
`(a ⊗ b, a' ⊗ b') ↦ (a ≫ a') ⊗ (b ≫ b')`. -/
def tensorComp (E₁ E₂ E₃ : 𝒳) (G₁ G₂ G₃ : 𝒢) :
    ((E₁ ⟶ E₂) ⊗[k] (G₁ ⟶ G₂)) →ₗ[k] ((E₂ ⟶ E₃) ⊗[k] (G₂ ⟶ G₃)) →ₗ[k]
      ((E₁ ⟶ E₃) ⊗[k] (G₁ ⟶ G₃)) :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun a b => TensorProduct.lift <| LinearMap.mk₂ k (fun a' b' => (a ≫ a') ⊗ₜ (b ≫ b'))
      (fun _ _ _ => by simp [Preadditive.comp_add, TensorProduct.add_tmul])
      (fun _ _ _ => by simp [TensorProduct.smul_tmul'])
      (fun _ _ _ => by simp [Preadditive.comp_add, TensorProduct.tmul_add])
      (fun _ _ _ => by simp [TensorProduct.tmul_smul]))
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp [Preadditive.add_comp, TensorProduct.add_tmul])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by simp [TensorProduct.smul_tmul'])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp [Preadditive.add_comp, TensorProduct.tmul_add])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by simp [TensorProduct.tmul_smul])

/-- `tensorComp` sends `a ⊗ b` and `a' ⊗ b'` to `(a ≫ a') ⊗ (b ≫ b')`. -/
@[simp]
theorem tensorComp_tmul_tmul {E₁ E₂ E₃ : 𝒳} {G₁ G₂ G₃ : 𝒢} (a : E₁ ⟶ E₂) (b : G₁ ⟶ G₂)
    (a' : E₂ ⟶ E₃) (b' : G₂ ⟶ G₃) :
    tensorComp k E₁ E₂ E₃ G₁ G₂ G₃ (a ⊗ₜ b) (a' ⊗ₜ b') = (a ≫ a') ⊗ₜ (b ≫ b') := by
  simp [tensorComp]

variable {k} (E : ℕ → 𝒳) (G : ℕ → 𝒢) (P : ℕ → 𝒞)

/-- **A box pairing**: `k`-bilinear maps `Hom(Eᵢ, Eⱼ) × Hom(Gᵢ, Gⱼ) ⟶ Hom(Pᵢ, Pⱼ)` compatible
with composition. -/
structure BoxPairing where
  /-- The pairing `(a, b) ↦ a ⊠ b`. -/
  box (i j : ℕ) : (E i ⟶ E j) →ₗ[k] (G i ⟶ G j) →ₗ[k] (P i ⟶ P j)
  /-- The pairing is compatible with composition. -/
  box_comp (i j l : ℕ) (a : E i ⟶ E j) (b : G i ⟶ G j) (a' : E j ⟶ E l) (b' : G j ⟶ G l) :
    box i j a b ≫ box j l a' b' = box i l (a ≫ a') (b ≫ b')

namespace BoxPairing

variable {E G P} (β : BoxPairing (k := k) E G P)

/-- The map out of the tensor product induced by a box pairing. -/
def κ (i j : ℕ) : ((E i ⟶ E j) ⊗[k] (G i ⟶ G j)) →ₗ[k] (P i ⟶ P j) :=
  TensorProduct.lift (β.box i j)

/-- `κ` sends a pure tensor `a ⊗ b` to `a ⊠ b`. -/
@[simp]
theorem κ_tmul (i j : ℕ) (a : E i ⟶ E j) (b : G i ⟶ G j) : β.κ i j (a ⊗ₜ b) = β.box i j a b :=
  TensorProduct.lift.tmul _ _

/-- **`κ` is compatible with composition.** -/
theorem κ_comp (i j l : ℕ) (t : (E i ⟶ E j) ⊗[k] (G i ⟶ G j))
    (s : (E j ⟶ E l) ⊗[k] (G j ⟶ G l)) :
    β.κ i j t ≫ β.κ j l s = β.κ i l (tensorComp k (E i) (E j) (E l) (G i) (G j) (G l) t s) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    induction s using TensorProduct.inductionOn with
    | tmul a' b' => simp [β.box_comp]
    | add x y hx hy => simp only [map_add, Preadditive.comp_add, hx, hy]
  | add x y hx hy =>
    simp only [map_add, Preadditive.add_comp, LinearMap.add_apply, hx, hy]

/-- **The transported differentials compose to zero.** Let `β` and `β'` be box pairings over the
same `Eᵢ`, `Gᵢ`, let `d i : P (i+1) ⟶ P i` be a complex for `β` with `d i = κ (t i)`, and suppose
`κ` for `β` is injective on `Hom(E_{i+2}, Eᵢ) ⊗ Hom(G_{i+2}, Gᵢ)`. Then the morphisms
`κ' (t i)` for `β'` compose to zero. -/
theorem transport_comp {𝒞' : Type*} [Category* 𝒞'] [Preadditive 𝒞'] [Linear k 𝒞']
    {P' : ℕ → 𝒞'} (β' : BoxPairing (k := k) E G P')
    (d : ∀ i, P (i + 1) ⟶ P i) (hd : ∀ i, d (i + 1) ≫ d i = 0)
    (t : ∀ i, (E (i + 1) ⟶ E i) ⊗[k] (G (i + 1) ⟶ G i)) (ht : ∀ i, β.κ (i + 1) i (t i) = d i)
    (hinj : ∀ i, Function.Injective (β.κ (i + 2) i)) (i : ℕ) :
    β'.κ (i + 2) (i + 1) (t (i + 1)) ≫ β'.κ (i + 1) i (t i) = 0 := by
  rw [β'.κ_comp]
  have h : tensorComp k _ _ _ _ _ _ (t (i + 1)) (t i) = 0 :=
    hinj i (by rw [map_zero, ← β.κ_comp, ht, ht, hd])
  rw [h, map_zero]

end BoxPairing

end CategoryTheory.Linear
