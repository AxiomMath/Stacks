module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The connecting map of a short exact sequence mapping to another one

Let `φ : S₁ ⟶ S₂` be a morphism of short exact sequences `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in an abelian
category, with `φ.τ₁` an isomorphism. For `x ∈ Extⁿ(G, S₁.X₃)` the connecting map of `S₁`,
`x ↦ x ∘ [S₁] ∈ Extⁿ⁺¹(G, S₁.X₁)`, is, up to `φ.τ₁`, the Yoneda product of `x ∘ φ.τ₃` with the
class `[S₂] ∈ Ext¹(S₂.X₃, S₂.X₁)`. Hence `x` lifts to `Extⁿ(G, S₁.X₂)` if and only if
`(x ∘ φ.τ₃) ∘ [S₂] = 0`.

This is the mechanism of the obstruction to deforming a line bundle in the proof of
[Stacks, Tag 0D1R]. For a first order thickening `X ⊂ X'` with ideal `ℐ`, `S₁` is
`0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ 𝒪_X^* ⟶ 0` (`u ↦ 1 + u` on the left), `S₂` is the sequence of differentials
`0 ⟶ ℐ ⟶ Ω_{X'}|_X ⟶ Ω_X ⟶ 0` whose class is the Kodaira–Spencer class, and `φ` is `d log`.
With `G` the constant sheaf `ℤ` and `n = 1`, `x` is the class of a line bundle `L` in
`H¹(X, 𝒪_X^*) = Pic(X)`, `x ∘ φ.τ₃` is `c₁(L)`, and the statement reads: `L` extends to `X'` if and
only if `c₁(L) ∪ KS = 0` in `H²(X, ℐ)`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.comp_extClass_comp_mk₀_τ₁`: the connecting map of `S₁`
  followed by `φ.τ₁` is `x ↦ (x ∘ φ.τ₃) ∘ [S₂]`.
* `CategoryTheory.ShortComplex.ShortExact.comp_mk₀_τ₃_comp_extClass_eq_zero_iff`: `x` lifts along
  `S₁.g` if and only if `(x ∘ φ.τ₃) ∘ [S₂] = 0`, for `φ.τ₁` an isomorphism.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public section

namespace CategoryTheory

open Abelian Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace ShortComplex.ShortExact

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
  {G : C} {n : ℕ}

/-- **The connecting map of `S₁` through a morphism `φ : S₁ ⟶ S₂` of short exact sequences**:
`(x ∘ [S₁]) ∘ φ.τ₁ = (x ∘ φ.τ₃) ∘ [S₂]` in `Extⁿ⁺¹(G, S₂.X₁)`. -/
theorem comp_extClass_comp_mk₀_τ₁ (x : Ext.{w} G S₁.X₃ n) :
    (x.comp h₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero _) =
      (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero, h₁.extClass_naturality h₂ φ,
    Ext.comp_assoc_of_second_deg_zero]

/-- A class that lifts along `S₁.g` is killed by `(- ∘ φ.τ₃) ∘ [S₂]`. -/
theorem comp_mk₀_τ₃_comp_extClass_eq_zero_of_lift (y : Ext.{w} G S₁.X₂ n) :
    ((y.comp (Ext.mk₀ S₁.g) (add_zero n)).comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp
      h₂.extClass rfl = 0 := by
  have h : (y.comp (Ext.mk₀ S₁.g) (add_zero n)).comp (Ext.mk₀ φ.τ₃) (add_zero n) =
      (y.comp (Ext.mk₀ φ.τ₂) (add_zero n)).comp (Ext.mk₀ S₂.g) (add_zero n) := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀, φ.comm₂₃]
  rw [h, Ext.comp_assoc_of_second_deg_zero, h₂.comp_extClass, Ext.comp_zero]

/-- A class `x ∈ Extⁿ(G, S₁.X₃)` lifts along `S₁.g` if and only if `x ∘ [S₁] = 0`: exactness of
the long exact `Ext` sequence at `Extⁿ(G, S₁.X₃)`. -/
theorem exists_comp_mk₀_g_eq_iff_comp_extClass_eq_zero (x : Ext.{w} G S₁.X₃ n) :
    (∃ y : Ext.{w} G S₁.X₂ n, y.comp (Ext.mk₀ S₁.g) (add_zero n) = x) ↔
      x.comp h₁.extClass rfl = 0 := by
  have hex := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' G h₁ n (n + 1) rfl)
  exact (hex x).symm

include h₁ in
/-- **A class lifts along `S₁.g` if and only if its image under `φ.τ₃` pairs to zero with
`[S₂]`**, for a morphism `φ : S₁ ⟶ S₂` of short exact sequences with `φ.τ₁` an isomorphism:
`x ∈ Extⁿ(G, S₁.X₃)` comes from `Extⁿ(G, S₁.X₂)` if and only if `(x ∘ φ.τ₃) ∘ [S₂] = 0`. -/
theorem comp_mk₀_τ₃_comp_extClass_eq_zero_iff [IsIso φ.τ₁] (x : Ext.{w} G S₁.X₃ n) :
    (∃ y : Ext.{w} G S₁.X₂ n, y.comp (Ext.mk₀ S₁.g) (add_zero n) = x) ↔
      (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass rfl = 0 := by
  rw [h₁.exists_comp_mk₀_g_eq_iff_comp_extClass_eq_zero, ← h₁.comp_extClass_comp_mk₀_τ₁ h₂ φ]
  constructor
  · intro h
    rw [h, Ext.zero_comp]
  · intro h
    have h' := congrArg (fun z => z.comp (Ext.mk₀ (inv φ.τ₁)) (add_zero _)) h
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id,
      Ext.zero_comp] at h'
    simpa using h'

end ShortComplex.ShortExact

end CategoryTheory

end
