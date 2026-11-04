module

public import StacksFrontier.AlgebraicGeometry.ProjTwists.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading

/-!
# The canonical comparison `M⁽ᵈ⁾ ⊗ N⁽ᵈ⁾ ⟶ (M ⊗ N)⁽ᵈ⁾`

Let `S` be a graded ring, `d` a natural number, `M` and `N` graded `S`-modules, and
`S' = S⁽ᵈ⁾` the Veronese subring. The Veronese parts `M⁽ᵈ⁾` and `N⁽ᵈ⁾` are graded
`S'`-modules, and so is the Veronese part `(M ⊗_S N)⁽ᵈ⁾` of the tensor product. This file
builds the canonical comparison between them,

`c : M⁽ᵈ⁾ ⊗_{S'} N⁽ᵈ⁾ ⟶ (M ⊗_S N)⁽ᵈ⁾`,

which sends a pure tensor to the same pure tensor, and proves that it is a map of graded
modules: it carries Veronese degree `k` to Veronese degree `k`.

The map matters because the proof of [Stacks, Tag 0B5J] asserts instead an *equality*
`M⁽ᵈ⁾ ⊗_{S'} N⁽ᵈ⁾ = (M ⊗_S N)⁽ᵈ⁾` "as can be verified directly from the definitions", and
that equality is false: `Stacks.Veronese.not_injective_veroneseTensorMap` (in
`StacksFrontier.RingTheory.GradedAlgebra.VeroneseTensorCounterexample`) proves that `c` is
not injective for `S = k[x, y]`, `d = 2`, `M = N = S(1)`, the element `x ⊗ y - y ⊗ x` of degree
zero being nonzero with image zero. (In degree zero `c` is the multiplication `S₁ ⊗_k S₁ ⟶ S₂`,
whose non-injectivity is `Stacks.Veronese.not_injective_multiplicationDegreeOne`.) So `c` is not
invertible, and the compatibility assertion of that tag is phrased with this map rather than with
the asserted equality. This file supplies the map.

## Main definitions

* `Stacks.Veronese.veroneseTensorMap`: the comparison `c`, as an `S⁽ᵈ⁾`-linear map.

## Main results

* `Stacks.Veronese.veroneseTensorMap_tmul`: `c` sends a pure tensor to the same pure tensor.
* `Stacks.Veronese.veroneseTensorMap_mem_veroneseModuleGrading`: `c` is a map of graded
  `S⁽ᵈ⁾`-modules — it takes the degree-`k` piece of the tensor grading of `M⁽ᵈ⁾` and `N⁽ᵈ⁾`
  into the degree-`k` piece of `(M ⊗_S N)⁽ᵈ⁾`.

## Implementation notes

The decomposition of the tensor grading of `M ⊗_S N` and its compatibility with the graded
action of `S` are section instance variables, following the convention of
`StacksFrontier/RingTheory/GradedAlgebra/VeroneseGrading.lean`; they are inhabited by
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition` and
`.tensorGrading_gradedSMul`, which are not imported here because nothing else in this file
needs the sheaf theory they come with. None of the declarations below uses them, nor the
graded-ring and module-grading instances: `c` and its two properties hold for any family of
subgroups, and they are omitted. Positivity of `d` is never assumed.

`c` is built as the codomain restriction of `TensorProduct.lift` of the bilinear map
`(m, n) ↦ m ⊗ₜ n` into `M ⊗_S N`; that its image lands in the Veronese part is proved by
spanning induction on both arguments, the generating case being
`Stacks.GradedModule.tmul_mem_tensorGrading` at `id + jd = (i + j)d`. Semilinearity over
`S⁽ᵈ⁾` is the semilinearity over `S` of the pure tensor, because the action of `S⁽ᵈ⁾` on any
`S`-module is restriction of scalars along the inclusion
(`Stacks.Veronese.veroneseModule_smul_def`).

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Veronese

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable (ℳ : ℤ → AddSubgroup M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable (𝒩 : ℤ → AddSubgroup N) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
variable [DirectSum.Decomposition (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)]
  [SetLike.GradedSMul 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)]

/-- The pure tensor of two elements of the Veronese parts, as a bilinear map over the
Veronese subring with values in the whole tensor product. -/
public def veroneseTensorBilin (d : ℕ) :
    veroneseSubmodule 𝒜 ℳ d →ₗ[veroneseSubring 𝒜 d]
      veroneseSubmodule 𝒜 𝒩 d →ₗ[veroneseSubring 𝒜 d] (M ⊗[A] N) where
  toFun m :=
    { toFun := fun n => (m : M) ⊗ₜ[A] (n : N)
      map_add' := fun n p => TensorProduct.tmul_add _ _ _
      map_smul' := fun r n => by
        change (m : M) ⊗ₜ[A] ((r : A) • (n : N)) = (r : A) • ((m : M) ⊗ₜ[A] (n : N))
        exact TensorProduct.tmul_smul _ _ _ }
  map_add' m p := by ext n; exact TensorProduct.add_tmul _ _ _
  map_smul' r m := by
    ext n
    change ((r : A) • (m : M)) ⊗ₜ[A] (n : N) = (r : A) • ((m : M) ⊗ₜ[A] (n : N))
    exact TensorProduct.smul_tmul' _ _ _

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
  [DirectSum.Decomposition (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)]
  [SetLike.GradedSMul 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)] in
/-- The pure tensor of an element of `M⁽ᵈ⁾` and an element of `N⁽ᵈ⁾` lies in the Veronese
part `(M ⊗_S N)⁽ᵈ⁾`. -/
public theorem tmul_mem_veroneseSubmodule (d : ℕ) {m : M}
    (hm : m ∈ veroneseSubmodule 𝒜 ℳ d) {n : N} (hn : n ∈ veroneseSubmodule 𝒜 𝒩 d) :
    m ⊗ₜ[A] n ∈
      veroneseSubmodule 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩) d := by
  set VT := veroneseSubmodule 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩) d with hVT
  clear_value VT
  induction hm using Submodule.span_induction generalizing n with
  | mem m hm =>
    obtain ⟨i, hm⟩ := Set.mem_iUnion.mp hm
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨j, hn⟩ := Set.mem_iUnion.mp hn
      rw [hVT]
      apply Submodule.subset_span
      refine Set.mem_iUnion.mpr ⟨i + j, ?_⟩
      exact Stacks.GradedModule.tmul_mem_tensorGrading ℳ 𝒩
        (by ring : i * (d : ℤ) + j * (d : ℤ) = (i + j) * (d : ℤ)) hm hn
    | zero => simp
    | add n p _ _ ihn ihp =>
      rw [TensorProduct.tmul_add]
      exact VT.add_mem ihn ihp
    | smul r n _ ih =>
      show m ⊗ₜ[A] ((r : A) • n) ∈ VT
      rw [TensorProduct.tmul_smul]
      exact VT.smul_mem r ih
  | zero => simp
  | add m p _ _ ihm ihp =>
    rw [TensorProduct.add_tmul]
    exact VT.add_mem (ihm hn) (ihp hn)
  | smul r m _ ih =>
    show ((r : A) • m) ⊗ₜ[A] n ∈ VT
    rw [← TensorProduct.smul_tmul']
    exact VT.smul_mem r (ih hn)

/-- **The canonical comparison `M⁽ᵈ⁾ ⊗_{S⁽ᵈ⁾} N⁽ᵈ⁾ ⟶ (M ⊗_S N)⁽ᵈ⁾`**, sending a pure tensor
to the same pure tensor. It is not an isomorphism: it is not injective at `S = k[x, y]`,
`d = 2`, `M = N = S(1)`, by `Stacks.Veronese.not_injective_veroneseTensorMap`. -/
public def veroneseTensorMap (d : ℕ) :
    veroneseSubmodule 𝒜 ℳ d ⊗[veroneseSubring 𝒜 d] veroneseSubmodule 𝒜 𝒩 d →ₗ[
        veroneseSubring 𝒜 d]
      veroneseSubmodule 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩) d :=
  (TensorProduct.lift (veroneseTensorBilin 𝒜 ℳ 𝒩 d)).codRestrict _ (by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => exact tmul_mem_veroneseSubmodule 𝒜 ℳ 𝒩 d m.2 n.2
    | add z t hz ht => simpa only [map_add] using add_mem hz ht)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
  [DirectSum.Decomposition (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)]
  [SetLike.GradedSMul 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)] in
/-- The comparison `veroneseTensorMap` sends the pure tensor `m ⊗ n` to the pure tensor
`m ⊗ n` of `M ⊗_A N`. -/
@[simp]
public theorem veroneseTensorMap_tmul (d : ℕ) (m : veroneseSubmodule 𝒜 ℳ d)
    (n : veroneseSubmodule 𝒜 𝒩 d) :
    ((veroneseTensorMap 𝒜 ℳ 𝒩 d (m ⊗ₜ[veroneseSubring 𝒜 d] n) : M ⊗[A] N)) =
      (m : M) ⊗ₜ[A] (n : N) :=
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
  [DirectSum.Decomposition (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)]
  [SetLike.GradedSMul 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩)] in
/-- **The comparison is a map of graded `S⁽ᵈ⁾`-modules**: it carries the degree-`k` piece of
the tensor grading of the Veronese parts into the degree-`k` piece of the Veronese part of the
tensor product. This is what lets it induce a map of the associated sheaves on
`Proj S⁽ᵈ⁾`. -/
public theorem veroneseTensorMap_mem_veroneseModuleGrading (d : ℕ) (k : ℤ)
    (z : veroneseSubmodule 𝒜 ℳ d ⊗[veroneseSubring 𝒜 d] veroneseSubmodule 𝒜 𝒩 d)
    (hz : z ∈ Stacks.GradedModule.tensorGrading (S := veroneseSubring 𝒜 d)
      (veroneseModuleGrading 𝒜 ℳ d) (veroneseModuleGrading 𝒜 𝒩 d) k) :
    veroneseTensorMap 𝒜 ℳ 𝒩 d z ∈
      veroneseModuleGrading 𝒜 (Stacks.GradedModule.tensorGrading (S := A) ℳ 𝒩) d k := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, j, hij, m, hm, n, hn, rfl⟩ := hz
    rw [mem_veroneseModuleGrading, veroneseTensorMap_tmul]
    exact Stacks.GradedModule.tmul_mem_tensorGrading ℳ 𝒩
      (by rw [← add_mul, hij] : i * (d : ℤ) + j * (d : ℤ) = k * (d : ℤ)) hm hn
  | zero => simp
  | add z t _ _ ihz iht => simpa only [map_add] using add_mem ihz iht
  | neg z _ ih => simpa only [map_neg] using neg_mem ih

end Stacks.Veronese

end
