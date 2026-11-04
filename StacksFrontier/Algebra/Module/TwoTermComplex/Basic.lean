module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Comparison squares of two-term complexes

A *comparison square* from a two-term complex `δ : K₀ ⟶ K₁` to a two-term complex
`d : C₀ ⟶ C₁` of `R`-modules is a commuting square

```
K₀ --δ--> K₁
|φ₀       |φ₁
v         v
C₀ --d--> C₁
```

whose associated sequence `0 ⟶ K₀ ⟶ K₁ × C₀ ⟶ C₁ ⟶ 0`, with maps `x ↦ (δ x, φ₀ x)` and
`(k, c) ↦ φ₁ k - d c`, is short exact. Such a square induces isomorphisms on kernels and on
cokernels. When moreover `C₁` is flat, the square stays a comparison square after any base
change, so the identification of kernels and cokernels holds universally.

This is the module-theoretic part of the standard argument (Mumford, *Abelian varieties*, §5)
replacing a two-term complex of flat modules by a quasi-isomorphic complex of finite projective
modules.

## Main definitions

* `Stacks.TwoTermComplex.IsComparisonSquare`: the short exactness condition.

## Main results

* `Stacks.TwoTermComplex.IsComparisonSquare.kerEquiv`: the induced isomorphism `ker δ ≃ ker d`.
* `Stacks.TwoTermComplex.IsComparisonSquare.cokerEquiv`: the induced isomorphism
  `K₁ ⧸ range δ ≃ C₁ ⧸ range d`.
* `Stacks.TwoTermComplex.IsComparisonSquare.baseChange`: a comparison square with flat `C₁` stays
  a comparison square after any base change.
-/

@[expose] public section

open TensorProduct

universe u v

namespace Stacks.TwoTermComplex

variable {R : Type u} [CommRing R]
  {K₀ K₁ C₀ C₁ : Type v} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup C₀]
  [AddCommGroup C₁] [Module R K₀] [Module R K₁] [Module R C₀] [Module R C₁]

/-- A commuting square from `δ : K₀ ⟶ K₁` to `d : C₀ ⟶ C₁` is a *comparison square* when the
sequence `0 ⟶ K₀ ⟶ K₁ × C₀ ⟶ C₁ ⟶ 0`, with maps `x ↦ (δ x, φ₀ x)` and
`(k, c) ↦ φ₁ k - d c`, is short exact. -/
structure IsComparisonSquare (δ : K₀ →ₗ[R] K₁) (d : C₀ →ₗ[R] C₁) (φ₀ : K₀ →ₗ[R] C₀)
    (φ₁ : K₁ →ₗ[R] C₁) : Prop where
  /-- The square commutes: `φ₁ ∘ δ = d ∘ φ₀`. -/
  comm : φ₁ ∘ₗ δ = d ∘ₗ φ₀
  /-- The map `K₀ → K₁ × C₀`, `x ↦ (δ x, φ₀ x)`, is injective. -/
  injective : Function.Injective (δ.prod φ₀)
  /-- The sequence `K₀ ⟶ K₁ × C₀ ⟶ C₁` is exact in the middle. -/
  exact : Function.Exact (δ.prod φ₀) (φ₁.coprod (-d))
  /-- The map `K₁ × C₀ → C₁`, `(k, c) ↦ φ₁ k - d c`, is surjective. -/
  surjective : Function.Surjective (φ₁.coprod (-d))

namespace IsComparisonSquare

variable {δ : K₀ →ₗ[R] K₁} {d : C₀ →ₗ[R] C₁} {φ₀ : K₀ →ₗ[R] C₀} {φ₁ : K₁ →ₗ[R] C₁}

section Basic

variable (h : IsComparisonSquare δ d φ₀ φ₁)
include h

/-- The square commutes pointwise: `φ₁ (δ x) = d (φ₀ x)`. -/
theorem comm_apply (x : K₀) : φ₁ (δ x) = d (φ₀ x) :=
  LinearMap.congr_fun h.comm x

/-- An element killed by both `δ` and `φ₀` is zero. -/
theorem eq_zero_of_eq_zero {x : K₀} (h₁ : δ x = 0) (h₂ : φ₀ x = 0) : x = 0 :=
  h.injective (by simp [h₁, h₂])

/-- If `φ₁ k = d c` then `(k, c)` comes from `K₀`. -/
theorem exists_of_eq {k : K₁} {c : C₀} (hkc : φ₁ k = d c) : ∃ x, δ x = k ∧ φ₀ x = c := by
  obtain ⟨x, hx⟩ := (h.exact (k, c)).1 (by simp [hkc])
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

/-- Every element of `C₁` is `φ₁ k - d c`. -/
theorem exists_eq_sub (y : C₁) : ∃ k c, φ₁ k - d c = y := by
  obtain ⟨⟨k, c⟩, hkc⟩ := h.surjective y
  exact ⟨k, c, by simpa [sub_eq_add_neg] using hkc⟩

/-- `φ₀` sends the kernel of `δ` into the kernel of `d`. -/
theorem map_ker_le : (LinearMap.ker δ).map φ₀ ≤ LinearMap.ker d := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
  rw [← h.comm_apply, hx, map_zero]

/-- **The kernels are identified.** `φ₀` restricts to an isomorphism `ker δ ≃ ker d`. -/
noncomputable def kerEquiv : LinearMap.ker δ ≃ₗ[R] LinearMap.ker d :=
  LinearEquiv.ofBijective (φ₀.restrict fun x hx => h.map_ker_le ⟨x, hx, rfl⟩)
    ⟨fun x y hxy => by
      have h0 : φ₀ ((x : K₀) - y) = 0 := by
        rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hxy
      have h1 : δ ((x : K₀) - y) = 0 := by
        rw [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero]
      exact Subtype.ext (sub_eq_zero.mp (h.eq_zero_of_eq_zero h1 h0)),
    fun c => by
      obtain ⟨x, hx, hc⟩ := h.exists_of_eq (k := 0) (c := c)
        (by rw [map_zero, LinearMap.mem_ker.mp c.2])
      exact ⟨⟨x, hx⟩, Subtype.ext hc⟩⟩

/-- `kerEquiv` acts as `φ₀` on underlying elements. -/
@[simp]
theorem kerEquiv_apply (x : LinearMap.ker δ) : (h.kerEquiv x : C₀) = φ₀ x := rfl

/-- `φ₁` sends the range of `δ` into the range of `d`. -/
theorem range_le_comap : LinearMap.range δ ≤ (LinearMap.range d).comap φ₁ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ₀ x, (h.comm_apply x).symm⟩

/-- **The cokernels are identified.** `φ₁` induces an isomorphism
`K₁ ⧸ range δ ≃ C₁ ⧸ range d`. -/
noncomputable def cokerEquiv :
    (K₁ ⧸ LinearMap.range δ) ≃ₗ[R] (C₁ ⧸ LinearMap.range d) :=
  LinearEquiv.ofBijective ((LinearMap.range δ).mapQ (LinearMap.range d) φ₁ h.range_le_comap)
    ⟨by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨c, hc⟩ := hz
      obtain ⟨x, hx, -⟩ := h.exists_of_eq hc.symm
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, hx⟩,
    fun z => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨k, c, rfl⟩ := h.exists_eq_sub y
      refine ⟨Submodule.Quotient.mk k, ?_⟩
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
      exact ⟨c, by simp⟩⟩

/-- `cokerEquiv` sends the class of `k` to the class of `φ₁ k`. -/
@[simp]
theorem cokerEquiv_mk (k : K₁) :
    h.cokerEquiv (Submodule.Quotient.mk k) = Submodule.Quotient.mk (φ₁ k) := rfl

end Basic

end IsComparisonSquare

/-! ### Base change -/

section BaseChange

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The base change of `f.prod g` is `(f.baseChange B).prod (g.baseChange B)`, up to the
identification `B ⊗ (K₁ × C₀) ≃ (B ⊗ K₁) × (B ⊗ C₀)`. -/
theorem prod_baseChange (f : K₀ →ₗ[R] K₁) (g : K₀ →ₗ[R] C₀) :
    ⇑((f.baseChange B).prod (g.baseChange B)) =
      ⇑(TensorProduct.prodRight R B B K₁ C₀) ∘ ⇑(LinearMap.lTensor B (f.prod g)) := by
  exact congrArg DFunLike.coe
    (TensorProduct.ext' (g := ((f.baseChange B).prod (g.baseChange B)).restrictScalars R)
      (h := (TensorProduct.prodRight R B B K₁ C₀).toLinearMap.restrictScalars R ∘ₗ
      LinearMap.lTensor B (f.prod g)) fun b x => by simp)

/-- The base change of `f.coprod g` is `(f.baseChange B).coprod (g.baseChange B)`, up to the
identification `B ⊗ (K₁ × C₀) ≃ (B ⊗ K₁) × (B ⊗ C₀)`. -/
theorem coprod_baseChange (f : K₁ →ₗ[R] C₁) (g : C₀ →ₗ[R] C₁) :
    ⇑(LinearMap.lTensor B (f.coprod g)) =
      ⇑((f.baseChange B).coprod (g.baseChange B)) ∘
        ⇑(TensorProduct.prodRight R B B K₁ C₀) := by
  exact congrArg DFunLike.coe
    (TensorProduct.ext' (h := LinearMap.lTensor B (f.coprod g))
      (g := ((f.baseChange B).coprod (g.baseChange B)).restrictScalars R ∘ₗ
        (TensorProduct.prodRight R B B K₁ C₀).toLinearMap.restrictScalars R)
      fun b x => by simp [TensorProduct.tmul_add]).symm

end BaseChange

namespace IsComparisonSquare

variable {δ : K₀ →ₗ[R] K₁} {d : C₀ →ₗ[R] C₁} {φ₀ : K₀ →ₗ[R] C₀} {φ₁ : K₁ →ₗ[R] C₁}

/-- **A comparison square into a complex with flat second term is universal.** After base change
to any `R`-algebra `B` it is still a comparison square. -/
theorem baseChange (h : IsComparisonSquare δ d φ₀ φ₁) [Module.Flat R C₁]
    (B : Type u) [CommRing B] [Algebra R B] :
    IsComparisonSquare (δ.baseChange B) (d.baseChange B) (φ₀.baseChange B)
      (φ₁.baseChange B) := by
  have hneg : (-d).baseChange B = -(d.baseChange B) := LinearMap.baseChange_neg d
  have hc := coprod_baseChange B φ₁ (-d)
  rw [hneg] at hc
  have hp := prod_baseChange B δ φ₀
  set e := TensorProduct.prodRight R B B K₁ C₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h.comm]
  · rw [hp]
    exact e.injective.comp (LinearMap.lTensor_injective_of_exact_of_flat _ h.surjective _
      h.injective h.exact B)
  · rw [hp]
    have hex := lTensor_exact B h.exact h.surjective
    intro y
    have hy : ((φ₁.baseChange B).coprod (-(d.baseChange B))) y =
        LinearMap.lTensor B (φ₁.coprod (-d)) (e.symm y) := by
      rw [hc]; simp
    rw [hy, hex (e.symm y)]
    simp [← LinearEquiv.eq_symm_apply]
  · intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective B h.surjective y
    exact ⟨e x, by rw [← hx, hc]; rfl⟩

end IsComparisonSquare

end Stacks.TwoTermComplex
