module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Two lemmas on tensor products of complexes of vector spaces

Over a field every module is flat, so tensoring with a vector space is exact. This file records
two consequences for the tensor product of two complexes of vector spaces.

## Main results

* `Stacks.FieldTensorExactness.mem_range_rTensor_of_cocycle`: let `A₀ ⟶ A₁ ⟶ A₂` be a complex and
  `g : B₀ ⟶ B₁` a map, and let `ε : B₀ ⟶ K` be injective on `ker g`. An element `x` of `A₁ ⊗ B₀`
  which is a cocycle in the first factor, whose image under `1 ⊗ g` is a coboundary in the first
  factor, and whose image under `1 ⊗ ε` is a coboundary in the first factor, is itself a coboundary
  in the first factor. Read in cohomology: the class of `x` lies in `H¹(A) ⊗ ker g`, and `1 ⊗ ε`
  is injective there.
* `Stacks.FieldTensorExactness.exists_eq_tmul_of_rTensor_eq_zero`: if the kernel of `f : A₀ ⟶ A₁`
  is spanned by `one`, every element of the kernel of `f ⊗ 1` is `one ⊗ n`.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public section

open TensorProduct

universe u v

namespace Stacks.FieldTensorExactness

variable {k : Type u} [Field k]
variable {A₀ A₁ A₂ B₀ B₁ K : Type v} [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup K] [Module k A₀] [Module k A₁] [Module k A₂]
  [Module k B₀] [Module k B₁] [Module k K]

/-- `rTensor` and `lTensor` along arbitrary linear maps commute. -/
private theorem rTensor_lTensor_comm {R M M' N N' : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N'] [Module R M] [Module R M']
    [Module R N] [Module R N'] (a : M →ₗ[R] M') (φ : N →ₗ[R] N') (z : M ⊗[R] N) :
    a.rTensor N' (φ.lTensor M z) = φ.lTensor M' (a.rTensor N z) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/-- **A coboundary criterion in a tensor product of complexes of vector spaces.** Let
`A₀ ⟶ A₁ ⟶ A₂` be a complex, `g : B₀ ⟶ B₁` a linear map and `ε : B₀ ⟶ K` injective on `ker g`.
If `x ∈ A₁ ⊗ B₀` is a cocycle in the first factor and its images under `1 ⊗ g` and `1 ⊗ ε` are
coboundaries in the first factor, then `x` is a coboundary in the first factor. -/
theorem mem_range_rTensor_of_cocycle (f : A₀ →ₗ[k] A₁) (f' : A₁ →ₗ[k] A₂) (hff : f' ∘ₗ f = 0)
    (g : B₀ →ₗ[k] B₁) (ε : B₀ →ₗ[k] K) (hε : ∀ b, g b = 0 → ε b = 0 → b = 0)
    (x : A₁ ⊗[k] B₀) (h₁ : f'.rTensor B₀ x = 0)
    (h₂ : g.lTensor A₁ x ∈ LinearMap.range (f.rTensor B₁))
    (h₃ : ε.lTensor A₁ x ∈ LinearMap.range (f.rTensor K)) :
    x ∈ LinearMap.range (f.rTensor B₀) := by
  set Z := LinearMap.ker f'
  set ι := Z.subtype
  have hfZ : ∀ a, f a ∈ Z := fun a => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hff, LinearMap.zero_apply]
  set f₀ : A₀ →ₗ[k] Z := f.codRestrict Z hfZ
  have hιf₀ : ι ∘ₗ f₀ = f := by ext; rfl
  set q := (LinearMap.range f₀).mkQ
  have hexZ : Function.Exact ι f' := LinearMap.exact_subtype_ker_map f'
  obtain ⟨y, rfl⟩ := (Module.Flat.rTensor_exact B₀ hexZ x).mp h₁
  have hinj : ∀ (N : Type v) [AddCommGroup N] [Module k N], Function.Injective (ι.rTensor N) :=
    fun N _ _ => Module.Flat.rTensor_preserves_injective_linearMap ι Z.injective_subtype
  have htr : ∀ (N : Type v) [AddCommGroup N] [Module k N] (φ : B₀ →ₗ[k] N),
      φ.lTensor A₁ (ι.rTensor B₀ y) ∈ LinearMap.range (f.rTensor N) →
        q.rTensor N (φ.lTensor Z y) = 0 := by
    intro N _ _ φ ⟨z, hz⟩
    have : φ.lTensor Z y = f₀.rTensor N z := by
      apply hinj N
      rw [rTensor_lTensor_comm, ← hz, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hιf₀]
    rw [this, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : q ∘ₗ f₀ = 0 := by ext; simp [q, Submodule.Quotient.mk_eq_zero]
    rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
  have hgy := htr B₁ g h₂
  have hεy := htr K ε h₃
  set H := Z ⧸ LinearMap.range f₀
  have hgq : g.lTensor H (q.rTensor B₀ y) = 0 := by
    rw [← rTensor_lTensor_comm, hgy]
  have hexg : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨v, hv⟩ := (Module.Flat.lTensor_exact H hexg _).mp hgq
  have hεinj : Function.Injective (ε ∘ₗ (LinearMap.ker g).subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨b, hb⟩ hb'
    exact (Submodule.mem_bot k).mpr (Subtype.ext (hε b hb hb'))
  have hv0 : v = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap _ hεinj
    rw [map_zero, LinearMap.lTensor_comp, LinearMap.comp_apply, hv, ← rTensor_lTensor_comm, hεy]
  rw [hv0, map_zero] at hv
  have hexq : Function.Exact f₀ q := fun z => by simp [q, Submodule.Quotient.mk_eq_zero]
  obtain ⟨w, rfl⟩ := (rTensor_exact B₀ hexq (Submodule.mkQ_surjective _) y).mp hv.symm
  exact ⟨w, by rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hιf₀]⟩

/-- **The kernel of `f ⊗ 1` when `ker f` is a line.** If the kernel of `f : A₀ ⟶ A₁` is spanned by
`one`, then every element of the kernel of `f ⊗ 1 : A₀ ⊗ B₀ ⟶ A₁ ⊗ B₀` is `one ⊗ n`. -/
theorem exists_eq_tmul_of_rTensor_eq_zero (f : A₀ →ₗ[k] A₁) (one : A₀)
    (hker : ∀ a, f a = 0 → ∃ c : k, a = c • one) (y : A₀ ⊗[k] B₀)
    (hy : f.rTensor B₀ y = 0) : ∃ n : B₀, y = one ⊗ₜ n := by
  have hexf : Function.Exact (LinearMap.ker f).subtype f := LinearMap.exact_subtype_ker_map f
  obtain ⟨w, rfl⟩ := (Module.Flat.rTensor_exact B₀ hexf y).mp hy
  clear hy
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a n =>
    obtain ⟨c, hc⟩ := hker a.1 a.2
    exact ⟨c • n, by simp [hc, TensorProduct.smul_tmul]⟩
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁
    obtain ⟨n₂, hn₂⟩ := h₂
    exact ⟨n₁ + n₂, by rw [map_add, hn₁, hn₂, TensorProduct.tmul_add]⟩

end Stacks.FieldTensorExactness

end
