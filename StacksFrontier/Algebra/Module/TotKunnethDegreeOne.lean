module

public import StacksFrontier.Algebra.Module.FieldTensorExactness

/-!
# The Künneth formula in degree one for a total complex, with base points

Let `k` be a field and `A₀ ⟶ A₁ ⟶ A₂`, `B₀ ⟶ B₁ ⟶ B₂` complexes of `k`-vector spaces whose
degree-zero cohomology is the line spanned by an element `1`, with "evaluation" maps
`ε_A : A₀ ⟶ k`, `ε_B : B₀ ⟶ k` sending `1` to `1`. A degree-one cocycle of the total complex of
`A ⊗ B` is a pair `(h, v)` with `h ∈ A₁ ⊗ B₀`, `v ∈ A₀ ⊗ B₁`,
`(d ⊗ 1) h = 0`, `(1 ⊗ d) v = 0` and `(1 ⊗ d) h = (d ⊗ 1) v`. If moreover its two
"restrictions to the axes" `(1 ⊗ ε_B) h ∈ A₁` and `(ε_A ⊗ 1) v ∈ B₁` are coboundaries, then
`(h, v)` is the total coboundary of some `f ∈ A₀ ⊗ B₀`
(`Stacks.TotKunneth.exists_eq_of_cocycle`).

In cohomology this is the injectivity of
`H¹(Tot(A ⊗ B)) ⟶ H¹(A) ⊕ H¹(B)` given by restriction to the two axes, which is the Künneth
formula `H¹(Tot) = H¹(A) ⊗ H⁰(B) ⊕ H⁰(A) ⊗ H¹(B)` read with `H⁰ = k`. Applied to Čech complexes
of the structure sheaves of two proper varieties with rational points it is the injectivity of
`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` used in the proof of
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), there quoted from
[Stacks, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED).

## Main definitions

* `Stacks.TotKunneth.evalLeft`: The map `A₀ ⊗ M ⟶ M` induced by a linear form `ε : A₀ ⟶ k`.

## Main results

* `Stacks.TotKunneth.exists_eq_of_cocycle`: A degree-one cocycle of the total complex whose
  restrictions to both axes are coboundaries is a total coboundary.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.TotKunneth

variable {k : Type u} [Field k]
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type u} [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [Module k A₀] [Module k A₁]
  [Module k A₂] [Module k B₀] [Module k B₁] [Module k B₂]

/-- The linear map `A₀ ⊗ M ⟶ M`, `a ⊗ m ↦ ε a • m`, induced by a linear form `ε : A₀ ⟶ k`. -/
noncomputable def evalLeft (ε : A₀ →ₗ[k] k) (M : Type u) [AddCommGroup M] [Module k M] :
    A₀ ⊗[k] M →ₗ[k] M :=
  (TensorProduct.lid k M).toLinearMap ∘ₗ ε.rTensor M

/-- `evalLeft ε M` sends `a ⊗ₜ m` to `ε a • m`. -/
@[simp]
theorem evalLeft_tmul (ε : A₀ →ₗ[k] k) {M : Type u} [AddCommGroup M] [Module k M] (a : A₀)
    (m : M) : evalLeft ε M (a ⊗ₜ m) = ε a • m := by
  simp [evalLeft]

/-- `evalLeft ε` commutes with a linear map `g : M →ₗ[k] N`: it sends `(1 ⊗ g) x` to
`g (evalLeft ε M x)`. -/
theorem evalLeft_lTensor (ε : A₀ →ₗ[k] k) {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (g : M →ₗ[k] N) (x : A₀ ⊗[k] M) :
    evalLeft ε N (g.lTensor A₀ x) = g (evalLeft ε M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Künneth in degree one, with base points.** Let `dA₀, dA₁` and `dB₀, dB₁` be complexes of
`k`-vector spaces whose degree-zero cocycles are spanned by `oneA` and `oneB`, with linear forms
`εA`, `εB` taking the value `1` there. If `(h, v)` is a degree-one cocycle of the total complex
whose restrictions `(1 ⊗ εB) h` and `evalLeft εA B₁ v` to the two axes are coboundaries, then
`(h, v)` is the total coboundary `((d ⊗ 1) f, (1 ⊗ d) f)` of some `f : A₀ ⊗[k] B₀`. -/
theorem exists_eq_of_cocycle (dA₀ : A₀ →ₗ[k] A₁) (dA₁ : A₁ →ₗ[k] A₂) (hdA : dA₁ ∘ₗ dA₀ = 0)
    (dB₀ : B₀ →ₗ[k] B₁) (dB₁ : B₁ →ₗ[k] B₂)
    (oneA : A₀) (hA : ∀ a, dA₀ a = 0 → ∃ c : k, a = c • oneA) (hdA1 : dA₀ oneA = 0)
    (εA : A₀ →ₗ[k] k) (hεA : εA oneA = 1)
    (oneB : B₀) (hB : ∀ b, dB₀ b = 0 → ∃ c : k, b = c • oneB)
    (εB : B₀ →ₗ[k] k) (hεB : εB oneB = 1)
    (h : A₁ ⊗[k] B₀) (v : A₀ ⊗[k] B₁)
    (hh : dA₁.rTensor B₀ h = 0) (hv : dB₁.lTensor A₀ v = 0)
    (hmix : dB₀.lTensor A₁ h = dA₀.rTensor B₁ v)
    (hfaceB : εB.lTensor A₁ h ∈ LinearMap.range (dA₀.rTensor k))
    (hfaceA : evalLeft εA B₁ v ∈ LinearMap.range dB₀) :
    ∃ f : A₀ ⊗[k] B₀, dA₀.rTensor B₀ f = h ∧ dB₀.lTensor A₀ f = v := by
  have hεinj : ∀ b, dB₀ b = 0 → εB b = 0 → b = 0 := by
    intro b hb hεb
    obtain ⟨c, rfl⟩ := hB b hb
    rw [map_smul, hεB, smul_eq_mul, mul_one] at hεb
    rw [hεb, zero_smul]
  obtain ⟨f, hf⟩ := Stacks.FieldTensorExactness.mem_range_rTensor_of_cocycle dA₀ dA₁ hdA dB₀ εB
    hεinj h hh ⟨v, hmix.symm⟩ hfaceB
  set v' := v - dB₀.lTensor A₀ f with hv'
  have hcomm : dB₀.lTensor A₁ (dA₀.rTensor B₀ f) = dA₀.rTensor B₁ (dB₀.lTensor A₀ f) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  have hv'0 : dA₀.rTensor B₁ v' = 0 := by
    rw [hv', map_sub, ← hmix, ← hf, hcomm, sub_self]
  obtain ⟨n, hn⟩ := Stacks.FieldTensorExactness.exists_eq_tmul_of_rTensor_eq_zero dA₀ oneA hA v'
    hv'0
  have hnrange : n ∈ LinearMap.range dB₀ := by
    have : evalLeft εA B₁ v' = n := by rw [hn, evalLeft_tmul, hεA, one_smul]
    rw [← this, hv', map_sub, evalLeft_lTensor]
    exact Submodule.sub_mem _ hfaceA (LinearMap.mem_range_self _ _)
  obtain ⟨m, hm⟩ := hnrange
  refine ⟨f + oneA ⊗ₜ m, ?_, ?_⟩
  · rw [map_add, hf, LinearMap.rTensor_tmul, hdA1, TensorProduct.zero_tmul, add_zero]
  · rw [map_add, LinearMap.lTensor_tmul, hm, ← hn, hv', add_sub_cancel]

end Stacks.TotKunneth

end
