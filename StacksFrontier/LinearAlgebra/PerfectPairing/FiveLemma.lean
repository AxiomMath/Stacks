module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Exact.Basic

/-!
# The five lemma for perfect pairings

Let `k` be a field, `A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` and `B₅ ⟶ B₄ ⟶ B₃ ⟶ B₂ ⟶ B₁` exact sequences of
`k`-vector spaces, and `Pᵢ : Aᵢ × Bᵢ ⟶ k` bilinear pairings compatible with the two sequences up to
nonzero scalars: `P_{i+1}(fᵢ a, b) = cᵢ Pᵢ(a, gᵢ b)`. If `P₁`, `P₂`, `P₄` and `P₅` are perfect, so
is `P₃`. This is the argument by the five lemma used in the proof of [Stacks, Tag 0FW7]: over a
field, dualizing is exact, so the maps `Aᵢ ⟶ Bᵢ^∨` form a morphism of exact sequences.

## Main results

* `LinearMap.exists_comp_eq_of_exact`: a linear form vanishing on the image of `g'` factors
  through `g` when `g'` and `g` form an exact pair; this is the exactness of dualizing over a
  field.
* `LinearMap.bijective_of_five`: the five lemma for the maps `Aᵢ ⟶ Bᵢ^∨`.
* `LinearMap.isPerfPair_of_five`: **the five lemma for perfect pairings.**

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
-/

@[expose] public section

namespace LinearMap

variable {k : Type*} [Field k]

/-- **Dualizing is exact over a field**: if `B₀ ⟶ B₁ ⟶ B₂` is exact, every linear form on `B₁`
vanishing on the image of `B₀` is the pullback of a linear form on `B₂`. -/
theorem exists_comp_eq_of_exact {B₀ B₁ B₂ : Type*} [AddCommGroup B₀] [Module k B₀]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] {g' : B₀ →ₗ[k] B₁}
    {g : B₁ →ₗ[k] B₂} (hex : Function.Exact g' g) (l : B₁ →ₗ[k] k) (hl : l ∘ₗ g' = 0) :
    ∃ m : B₂ →ₗ[k] k, m ∘ₗ g = l := by
  have hker : LinearMap.ker g ≤ LinearMap.ker l := fun y hy => by
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    exact LinearMap.congr_fun hl x
  obtain ⟨m, hm⟩ := LinearMap.exists_extend
    (((LinearMap.ker g).liftQ l hker).comp g.quotKerEquivRange.symm.toLinearMap)
  refine ⟨m, LinearMap.ext fun y => ?_⟩
  have := LinearMap.congr_fun hm ⟨g y, LinearMap.mem_range_self g y⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at this
  rw [LinearMap.comp_apply, this, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}
  [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
  [AddCommGroup A₄] [Module k A₄] [AddCommGroup A₅] [Module k A₅]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
  [AddCommGroup B₄] [Module k B₄] [AddCommGroup B₅] [Module k B₅]

/-- **The five lemma for the maps `Aᵢ ⟶ Bᵢ^∨` of compatible pairings.** For exact sequences
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` and `B₅ ⟶ B₄ ⟶ B₃ ⟶ B₂ ⟶ B₁` and pairings compatible up to the
nonzero scalars `cᵢ`, the map `A₃ ⟶ B₃^∨` is bijective as soon as `A₁ ⟶ B₁^∨` is surjective,
`A₂ ⟶ B₂^∨` and `A₄ ⟶ B₄^∨` are bijective and `A₅ ⟶ B₅^∨` is injective. -/
theorem bijective_of_five (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (f₃ : A₃ →ₗ[k] A₄)
    (f₄ : A₄ →ₗ[k] A₅) (g₁ : B₂ →ₗ[k] B₁) (g₂ : B₃ →ₗ[k] B₂) (g₃ : B₄ →ₗ[k] B₃)
    (g₄ : B₅ →ₗ[k] B₄) (hf₁₂ : Function.Exact f₁ f₂) (hf₂₃ : Function.Exact f₂ f₃)
    (hf₃₄ : Function.Exact f₃ f₄) (hg₂₁ : Function.Exact g₂ g₁) (hg₃₂ : Function.Exact g₃ g₂)
    (hg₄₃ : Function.Exact g₄ g₃)
    (P₁ : A₁ →ₗ[k] B₁ →ₗ[k] k) (P₂ : A₂ →ₗ[k] B₂ →ₗ[k] k) (P₃ : A₃ →ₗ[k] B₃ →ₗ[k] k)
    (P₄ : A₄ →ₗ[k] B₄ →ₗ[k] k) (P₅ : A₅ →ₗ[k] B₅ →ₗ[k] k) (c₁ c₂ c₃ c₄ : kˣ)
    (h₁ : ∀ a b, P₂ (f₁ a) b = (c₁ : k) * P₁ a (g₁ b))
    (h₂ : ∀ a b, P₃ (f₂ a) b = (c₂ : k) * P₂ a (g₂ b))
    (h₃ : ∀ a b, P₄ (f₃ a) b = (c₃ : k) * P₃ a (g₃ b))
    (h₄ : ∀ a b, P₅ (f₄ a) b = (c₄ : k) * P₄ a (g₄ b))
    (hP₁ : Function.Surjective P₁) (hP₂ : Function.Bijective P₂) (hP₄ : Function.Bijective P₄)
    (hP₅ : Function.Injective P₅) : Function.Bijective P₃ := by
  refine ⟨(injective_iff_map_eq_zero P₃).2 fun a ha => ?_, fun l => ?_⟩
  · -- injectivity
    have h4 : f₃ a = 0 := hP₄.1 <| by
      rw [map_zero]
      refine LinearMap.ext fun b => ?_
      rw [h₃, ha, LinearMap.zero_apply, LinearMap.zero_apply, mul_zero]
    obtain ⟨a', rfl⟩ := (hf₂₃ a).1 h4
    have hz : P₂ a' ∘ₗ g₂ = 0 := LinearMap.ext fun b => by
      have := LinearMap.congr_fun ha b
      rw [h₂, LinearMap.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left c₂.ne_zero
    obtain ⟨m, hm⟩ := exists_comp_eq_of_exact hg₂₁ (P₂ a') hz
    obtain ⟨a'', ha''⟩ := hP₁ m
    have : a' = f₁ (((c₁⁻¹ : kˣ) : k) • a'') := hP₂.1 <| LinearMap.ext fun b => by
      rw [map_smul, map_smul, LinearMap.smul_apply, h₁, ← hm, ← ha'', LinearMap.comp_apply,
        smul_eq_mul, Units.inv_mul_cancel_left]
    rw [this]
    exact (hf₁₂ _).2 ⟨_, rfl⟩
  · -- surjectivity
    obtain ⟨x, hx⟩ := hP₄.2 (l ∘ₗ g₃)
    have h5 : f₄ x = 0 := hP₅ <| by
      rw [map_zero]
      refine LinearMap.ext fun b => ?_
      rw [h₄, hx, LinearMap.comp_apply, LinearMap.zero_apply, (hg₄₃ _).2 ⟨b, rfl⟩, map_zero,
        mul_zero]
    obtain ⟨y, rfl⟩ := (hf₃₄ x).1 h5
    have hz : (l - (c₃ : k) • P₃ y) ∘ₗ g₃ = 0 := LinearMap.ext fun b => by
      have := LinearMap.congr_fun hx b
      rw [h₃, LinearMap.comp_apply] at this
      rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, ← this, smul_eq_mul,
        sub_self, LinearMap.zero_apply]
    obtain ⟨m, hm⟩ := exists_comp_eq_of_exact hg₃₂ _ hz
    obtain ⟨z, rfl⟩ := hP₂.2 m
    refine ⟨(c₃ : k) • y + ((c₂⁻¹ : kˣ) : k) • f₂ z, LinearMap.ext fun b => ?_⟩
    have hb := LinearMap.congr_fun hm b
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hb
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, h₂, hb, smul_eq_mul, smul_eq_mul, Units.inv_mul_cancel_left]
    ring

/-- A compatibility `P'(f a, b) = c P(a, g b)` read backwards. -/
private theorem apply_eq_inv_mul {X Y X' Y' : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y']
    [Module k Y'] (c : kˣ) (f : X →ₗ[k] X') (g : Y' →ₗ[k] Y) (P : X →ₗ[k] Y →ₗ[k] k)
    (P' : X' →ₗ[k] Y' →ₗ[k] k) (h : ∀ a b, P' (f a) b = (c : k) * P a (g b)) (a : X) (b : Y') :
    P a (g b) = ((c⁻¹ : kˣ) : k) * P' (f a) b := by
  rw [h, Units.inv_mul_cancel_left]

/-- **The five lemma for perfect pairings.** Let `A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` and
`B₅ ⟶ B₄ ⟶ B₃ ⟶ B₂ ⟶ B₁` be exact sequences of vector spaces and `Pᵢ : Aᵢ × Bᵢ ⟶ k` pairings
compatible up to nonzero scalars, `P_{i+1}(fᵢ a, b) = cᵢ Pᵢ(a, gᵢ b)`. If `P₁`, `P₂`, `P₄` and `P₅`
are perfect, then so is `P₃`. -/
theorem isPerfPair_of_five (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (f₃ : A₃ →ₗ[k] A₄)
    (f₄ : A₄ →ₗ[k] A₅) (g₁ : B₂ →ₗ[k] B₁) (g₂ : B₃ →ₗ[k] B₂) (g₃ : B₄ →ₗ[k] B₃)
    (g₄ : B₅ →ₗ[k] B₄) (hf₁₂ : Function.Exact f₁ f₂) (hf₂₃ : Function.Exact f₂ f₃)
    (hf₃₄ : Function.Exact f₃ f₄) (hg₂₁ : Function.Exact g₂ g₁) (hg₃₂ : Function.Exact g₃ g₂)
    (hg₄₃ : Function.Exact g₄ g₃)
    (P₁ : A₁ →ₗ[k] B₁ →ₗ[k] k) (P₂ : A₂ →ₗ[k] B₂ →ₗ[k] k) (P₃ : A₃ →ₗ[k] B₃ →ₗ[k] k)
    (P₄ : A₄ →ₗ[k] B₄ →ₗ[k] k) (P₅ : A₅ →ₗ[k] B₅ →ₗ[k] k) (c₁ c₂ c₃ c₄ : kˣ)
    (h₁ : ∀ a b, P₂ (f₁ a) b = (c₁ : k) * P₁ a (g₁ b))
    (h₂ : ∀ a b, P₃ (f₂ a) b = (c₂ : k) * P₂ a (g₂ b))
    (h₃ : ∀ a b, P₄ (f₃ a) b = (c₃ : k) * P₃ a (g₃ b))
    (h₄ : ∀ a b, P₅ (f₄ a) b = (c₄ : k) * P₄ a (g₄ b))
    (hP₁ : P₁.IsPerfPair) (hP₂ : P₂.IsPerfPair) (hP₄ : P₄.IsPerfPair) (hP₅ : P₅.IsPerfPair) :
    P₃.IsPerfPair := by
  refine ⟨bijective_of_five f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ hf₁₂ hf₂₃ hf₃₄ hg₂₁ hg₃₂ hg₄₃ P₁ P₂ P₃ P₄
      P₅ c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ hP₁.bijective_left.2 hP₂.bijective_left hP₄.bijective_left
      hP₅.bijective_left.1, ?_⟩
  exact bijective_of_five g₄ g₃ g₂ g₁ f₄ f₃ f₂ f₁ hg₄₃ hg₃₂ hg₂₁ hf₃₄ hf₂₃ hf₁₂ P₅.flip P₄.flip
    P₃.flip P₂.flip P₁.flip c₄⁻¹ c₃⁻¹ c₂⁻¹ c₁⁻¹ (fun b a => apply_eq_inv_mul c₄ f₄ g₄ P₄ P₅ h₄ a b)
    (fun b a => apply_eq_inv_mul c₃ f₃ g₃ P₃ P₄ h₃ a b)
    (fun b a => apply_eq_inv_mul c₂ f₂ g₂ P₂ P₃ h₂ a b)
    (fun b a => apply_eq_inv_mul c₁ f₁ g₁ P₁ P₂ h₁ a b) hP₅.bijective_right.2 hP₄.bijective_right
    hP₂.bijective_right hP₁.bijective_right.1

end LinearMap
