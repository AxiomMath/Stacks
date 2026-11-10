module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystem
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# The comparison maps `Iⁿ M₀ → M_j` and the pro-isomorphism of the two systems

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M 0 ← M 1 ← M 2 ← ⋯` an inverse system of
`R`-modules over a module `M₀`, with multiplication maps `Iᵏ ⊗ M n → M (k + n)`, as in
`Stacks.RingTheory.IdealPowerSystem`. This file carries out parts (4) and (5) of
[Stacks, Tag 02OA] for such a system: granted the conclusions of parts (1), (2) and (3) — one
constant `c` with `Iⁿ⁻ᶜ · M_c = Mₙ`, with `Im(Mₙ → M₀) ⊆ Iⁿ⁻ᶜM₀` and with
`Ker(M_k → M₀) = Ker(M_k → M_m)` for `m + c ≤ k` — there are comparison maps `IⁿM₀ → M_{n-c}`
whose composites with the canonical maps are canonical, and the two inverse systems `(Mₙ)` and
`(IⁿM₀)` are isomorphic as pro-objects.

## The extra multiplication the source uses

Parts (1), (2) and (3) use only the multiplication maps `Iᵏ ⊗ Mₙ → M_{k+n}`. Part (4) needs one
more operation: multiplication `Iᵏ ⊗ M₀ → M_m` for `m ≤ k` *out of the module `M₀` at the
bottom* — in the motivating example, multiplication by a function on the base read as a map
`ℱ → Iᵏℱ`, whence `Hᵖ(X, ℱ) → Hᵖ(X, Iᵏℱ)`. The source has it because it writes `M₀` as the
degree-zero member of the graded module; here `M₀` is a separate module, so the operation is
added as the field `mulTop` of `Stacks.RingTheory.TopMulSystem`, together with the laws the
argument uses: it projects to the module action (`proj_mulTop`), it is compatible with the
transition maps (`tr_mulTop`), it depends on the ring element alone (`mulTop_congr`), and
multiplying in degree `n` by `a ∈ Iᵏ` and dropping to degree `k` is projecting to `M₀` and
multiplying there (`tr_mul_eq_mulTop_proj`). The last of these is the compatibility the source
displays, and it *implies* the field `IdealPowerSystem.tr_mul_of_proj_eq_zero` that parts
(1)-(3) run on.

## The construction

`IⁿM₀` is presented as the range of `Stacks.RingTheory.idealPowerSmulLift`, the map
`Iⁿ ⊗ M₀ → M₀` sending `a ⊗ x` to `a • x`. The composite `Iⁿ ⊗ M₀ → Mₙ → M_j` through `mulTop`
kills the kernel of that presentation: an element of the kernel is carried into
`Ker(Mₙ → M₀)`, which for `j + c ≤ n` is `Ker(Mₙ → M_j)` by part (3). So the composite descends
to `Stacks.RingTheory.TopMulSystem.comparison`, a map `IⁿM₀ → M_j`. Part (1) is what identifies
the composite `Mₙ → IⁿM₀ → M_j`: an element of `Mₙ` is a sum of products `a · y` with
`a ∈ Iⁿ⁻ᶜ` and `y ∈ M_c`, and on such a product both maps are multiplication by `a`.

## Main definitions

* `Stacks.RingTheory.TopMulSystem` — an `IdealPowerSystem` with the multiplication out of `M₀`.
* `Stacks.RingTheory.TopMulSystem.comparison` — **the comparison map `IⁿM₀ → M_j` of
  [Stacks, Tag 02OA] part (4)**, for `j + c ≤ n`.
* `Stacks.RingTheory.TopMulSystem.system` and `Stacks.RingTheory.idealPowerSmulSystem` — the two
  inverse systems `(Mₙ)` and `(IⁿM₀)` as functors `ℕᵒᵖ ⥤ ModuleCat R`.

## Main results

* `Stacks.RingTheory.TopMulSystem.comparison_proj` and
  `Stacks.RingTheory.TopMulSystem.proj_comparison` — **the two composites of
  [Stacks, Tag 02OA] part (4)** are the canonical maps.
* `Stacks.RingTheory.TopMulSystem.nonempty_proIso` — **[Stacks, Tag 02OA] part (5)**: the two
  systems are pro-isomorphic, by the cofinal shift `n ↦ n + c`.

Neither statement is registered as the tag: both are proved from the conclusions of parts
(1)-(3), carried as hypotheses, and those are discharged only at the cohomology of a proper
morphism, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ArtinReesChain.lean`.

## Implementation notes

The target degree `j` of `comparison` is a parameter rather than being `n - c`, because the
pro-isomorphism uses it at `n = m + c`, `j = m`, where `n - c` is the term `m + c - c`: not the
term `m`, so a subtraction in the target *type* would force a transport. Part (4) of the source
is the case `j = n - c`.

Pro-isomorphism is `InverseSequence.ProIso`, the explicit up-to-refinement notion of
[Stacks, Tag 0H3D] already used in `StacksFrontier/RingTheory/Module/AdicSystem/Homology.lean`.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open scoped TensorProduct

universe u v

namespace Stacks.RingTheory

variable {R : Type u} [CommRing R]

/-- **The presentation of `Iᵏ M₀`**: the map `Iᵏ ⊗_R M₀ → M₀` sending `a ⊗ x` to `a • x`. Its
range is `Iᵏ M₀`, and the comparison map of [Stacks, Tag 02OA] part (4) is defined by descending
a map on `Iᵏ ⊗_R M₀` along it. -/
def idealPowerSmulLift (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀] (k : ℕ) :
    (↥(I ^ k) ⊗[R] M₀) →ₗ[R] M₀ :=
  TensorProduct.lift ((LinearMap.lsmul R M₀).comp (I ^ k).subtype)

/-- The presentation of `Iᵏ M₀` sends `a ⊗ x` to `a • x`. -/
@[simp]
theorem idealPowerSmulLift_tmul (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀]
    (k : ℕ) (a : ↥(I ^ k)) (x : M₀) :
    idealPowerSmulLift I M₀ k (a ⊗ₜ[R] x) = (a : R) • x := rfl

/-- The range of the presentation of `Iᵏ M₀` is `Iᵏ M₀`. -/
theorem range_idealPowerSmulLift (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀]
    (k : ℕ) :
    LinearMap.range (idealPowerSmulLift I M₀ k) = I ^ k • (⊤ : Submodule R M₀) := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun r hr x _ ↦ ⟨⟨r, hr⟩ ⊗ₜ[R] x, rfl⟩)
  rintro _ ⟨ξ, rfl⟩
  induction ξ using TensorProduct.inductionOn with
  | tmul a x => exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  | add ξ ξ' hξ hξ' => simpa only [map_add] using Submodule.add_mem _ hξ hξ'

/-- Every element of `Iᵏ M₀` comes from the presentation `Iᵏ ⊗_R M₀ → M₀`. -/
theorem exists_idealPowerSmulLift_eq {I : Ideal R} {M₀ : Type v} [AddCommGroup M₀]
    [Module R M₀] {k : ℕ} (y : ↥(I ^ k • (⊤ : Submodule R M₀))) :
    ∃ ξ : ↥(I ^ k) ⊗[R] M₀, idealPowerSmulLift I M₀ k ξ = (y : M₀) :=
  LinearMap.mem_range.1 (by rw [range_idealPowerSmulLift]; exact y.2)

/-- Reading an element of `Iᵏ ⊗ M₀` in `Iᵏ' ⊗ M₀` for `k' ≤ k` does not change the element of
`M₀` it presents. -/
theorem idealPowerSmulLift_map_inclusion {I : Ideal R} {M₀ : Type v} [AddCommGroup M₀]
    [Module R M₀] {k k' : ℕ} (hk : k' ≤ k) (ξ : ↥(I ^ k) ⊗[R] M₀) :
    idealPowerSmulLift I M₀ k' (TensorProduct.map
        (Submodule.inclusion (Ideal.pow_le_pow_right hk)) LinearMap.id ξ) =
      idealPowerSmulLift I M₀ k ξ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add ξ ξ' hξ hξ' => simp only [map_add, hξ, hξ']

/-- **The inverse system `n ↦ Iⁿ M₀`**, with the inclusions `Iⁿ⁺¹M₀ ⊆ IⁿM₀` as transition maps:
the second of the two systems of [Stacks, Tag 02OA] part (5). -/
def idealPowerSmulSystem (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀] :
    ℕᵒᵖ ⥤ ModuleCat.{v} R where
  obj n := ModuleCat.of R ↥(I ^ n.unop • (⊤ : Submodule R M₀))
  map f := ModuleCat.ofHom (Submodule.inclusion
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (leOfHom f.unop))))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The `n`-th term of the inverse system `n ↦ Iⁿ M₀` is `Iⁿ M₀`. -/
@[simp]
theorem idealPowerSmulSystem_obj (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀]
    (n : ℕ) :
    (idealPowerSmulSystem I M₀).obj (op n) =
      ModuleCat.of R ↥(I ^ n • (⊤ : Submodule R M₀)) := rfl

/-- The transition map `IⁿM₀ → IᵐM₀` of the inverse system `n ↦ Iⁿ M₀`, for `m ≤ n`, is the
inclusion. -/
@[simp]
theorem idealPowerSmulSystem_map (I : Ideal R) (M₀ : Type v) [AddCommGroup M₀] [Module R M₀]
    {m n : ℕ} (h : m ≤ n) :
    (idealPowerSmulSystem I M₀).map (homOfLE h).op =
      ModuleCat.ofHom (Submodule.inclusion
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right h))) := rfl

/-- An **`IdealPowerSystem` with multiplication out of the bottom module `M₀`**, which is what
[Stacks, Tag 02OA] part (4) needs beyond parts (1), (2) and (3): for `m ≤ k` a multiplication
`Iᵏ ⊗ M₀ → M_m`, projecting to the module action of `Iᵏ` on `M₀`, compatible with the transition
maps, depending on the ring element alone, and agreeing with multiplication in a positive degree
followed by the transition map that drops that degree.

In the motivating example `M n = Hᵖ(X, Iⁿℱ)` over `M₀ = Hᵖ(X, ℱ)` the new operation is induced
by multiplication by a function on the base, read as a morphism `ℱ ⟶ Iᵏℱ`.

The field `tr_mul_eq_mulTop_proj` implies the inherited field
`IdealPowerSystem.tr_mul_of_proj_eq_zero`, which is therefore not independent data; the latter
is kept because parts (1), (2) and (3) are proved for a bare `IdealPowerSystem`. -/
structure TopMulSystem (I : Ideal R) (M : ℕ → Type v) [∀ n, AddCommGroup (M n)]
    [∀ n, Module R (M n)] (M₀ : Type v) [AddCommGroup M₀] [Module R M₀] extends
    IdealPowerSystem I M M₀ where
  /-- A transition map between equal degrees is the identity. -/
  tr_self : ∀ {n : ℕ} (h : n ≤ n) (x : M n), tr h x = x
  /-- **Multiplication `Iᵏ ⊗ M₀ → M_m` for `m ≤ k`**, out of the bottom module. -/
  mulTop : ∀ ⦃k m : ℕ⦄, m ≤ k → ↥(I ^ k) →ₗ[R] M₀ →ₗ[R] M m
  /-- Multiplying `M₀` into `M_m` and projecting back is the module action. -/
  proj_mulTop : ∀ ⦃k m : ℕ⦄ (h : m ≤ k) (a : ↥(I ^ k)) (x : M₀),
    proj m (mulTop h a x) = (a : R) • x
  /-- Multiplying `M₀` into `M_m` and dropping to `M_j` is multiplying `M₀` into `M_j`. -/
  tr_mulTop : ∀ ⦃k m j : ℕ⦄ (h : m ≤ k) (h' : j ≤ k) (hj : j ≤ m) (a : ↥(I ^ k)) (x : M₀),
    tr hj (mulTop h a x) = mulTop h' a x
  /-- Multiplication out of `M₀` depends only on the ring element, not on the power of `I` in
  which it is taken. -/
  mulTop_congr : ∀ ⦃k k' m : ℕ⦄ (h : m ≤ k) (h' : m ≤ k') (a : ↥(I ^ k)) (a' : ↥(I ^ k'))
    (x : M₀), (a : R) = (a' : R) → mulTop h a x = mulTop h' a' x
  /-- **Multiplying in degree `n` by `a ∈ Iᵏ` and dropping to degree `k` is projecting to `M₀`
  and multiplying there.** This is the compatibility of the multiplication maps with the
  transition maps that [Stacks, Tag 02OA] displays. -/
  tr_mul_eq_mulTop_proj : ∀ (k n : ℕ) (a : ↥(I ^ k)) (x : M n),
    tr (Nat.le_add_right k n) (mul k n a x) = mulTop (le_refl k) a (proj n x)

namespace TopMulSystem

variable {I : Ideal R} {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M₀ : Type v} [AddCommGroup M₀] [Module R M₀] (S : TopMulSystem I M M₀)

/-- The multiplication map `Iᵏ ⊗_R Mₙ → M_{k+n}` of the system, as a map out of the tensor
product. [Stacks, Tag 02OA] part (1) is its surjectivity, after dropping to degree `n`, for
`k = n - c` and source degree `c`. -/
def mulTensor (k n : ℕ) : (↥(I ^ k) ⊗[R] M n) →ₗ[R] M (k + n) :=
  TensorProduct.lift (S.mul k n)

/-- The multiplication map `Iᵏ ⊗_R Mₙ → M_{k+n}` sends `a ⊗ x` to `a · x`. -/
@[simp]
theorem mulTensor_tmul (k n : ℕ) (a : ↥(I ^ k)) (x : M n) :
    S.mulTensor k n (a ⊗ₜ[R] x) = S.mul k n a x := rfl

/-- The multiplication map `Iᵏ ⊗_R M₀ → M_m` out of the bottom module, `m ≤ k`, as a map out of
the tensor product. -/
def mulTopTensor ⦃k m : ℕ⦄ (h : m ≤ k) : (↥(I ^ k) ⊗[R] M₀) →ₗ[R] M m :=
  TensorProduct.lift (S.mulTop h)

/-- The multiplication map `Iᵏ ⊗_R M₀ → M_m` sends `a ⊗ x` to `a · x`. -/
@[simp]
theorem mulTopTensor_tmul ⦃k m : ℕ⦄ (h : m ≤ k) (a : ↥(I ^ k)) (x : M₀) :
    S.mulTopTensor h (a ⊗ₜ[R] x) = S.mulTop h a x := rfl

/-- Multiplying `M₀` into `M_m` and projecting back is the module action, on the tensor
product. -/
theorem proj_mulTopTensor ⦃k m : ℕ⦄ (h : m ≤ k) (ξ : ↥(I ^ k) ⊗[R] M₀) :
    S.proj m (S.mulTopTensor h ξ) = idealPowerSmulLift I M₀ k ξ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a x => exact S.proj_mulTop h a x
  | add ξ ξ' hξ hξ' => simp only [map_add, hξ, hξ']

/-- Multiplying `M₀` into `M_m` and dropping to `M_j`, read on the two presentations of one
element of `Iᵏ M₀` as an element of `Iᵏ ⊗ M₀` and of `Iᵏ' ⊗ M₀` with `k' ≤ k`: the same map down
to `M_j`. -/
theorem tr_mulTopTensor_inclusion {k k' m m' j : ℕ} (hk : k' ≤ k) (h : m ≤ k) (h' : m' ≤ k')
    (hj : j ≤ m) (hj' : j ≤ m') (ξ : ↥(I ^ k) ⊗[R] M₀) :
    S.tr hj (S.mulTopTensor h ξ) =
      S.tr hj' (S.mulTopTensor h' (TensorProduct.map
        (Submodule.inclusion (Ideal.pow_le_pow_right hk)) LinearMap.id ξ)) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a x =>
      rw [TensorProduct.map_tmul, mulTopTensor_tmul, mulTopTensor_tmul,
        S.tr_mulTop h (hj.trans h) hj, S.tr_mulTop h' (hj'.trans h') hj']
      exact S.mulTop_congr (hj.trans h) (hj'.trans h') _ _ x rfl
  | add ξ ξ' hξ hξ' => simp only [map_add, hξ, hξ']

/-- The presentation of `Iᵏ M₀` applied to a projected product: the image in `M₀` of a product
`a · y` with `a ∈ Iᵏ` and `y ∈ Mₙ` is `a` times the image of `y`. -/
theorem idealPowerSmulLift_map_proj (k n : ℕ) (ζ : ↥(I ^ k) ⊗[R] M n) :
    idealPowerSmulLift I M₀ k (TensorProduct.map LinearMap.id (S.proj n) ζ) =
      S.proj (k + n) (S.mulTensor k n ζ) := by
  induction ζ using TensorProduct.inductionOn with
  | tmul a x => exact (S.proj_mul k n a x).symm
  | add ζ ζ' hζ hζ' => simp only [map_add, hζ, hζ']

/-- Multiplying a projected product back into the system and dropping to `M_j` is dropping the
product itself to `M_j`: the identity that makes the composite `Mₙ → IⁿM₀ → M_j` of
[Stacks, Tag 02OA] part (4) the canonical map. -/
theorem tr_mulTopTensor_map_proj {k n j : ℕ} (hj : j ≤ k) (ζ : ↥(I ^ k) ⊗[R] M n) :
    S.tr hj (S.mulTopTensor (le_refl k) (TensorProduct.map LinearMap.id (S.proj n) ζ)) =
      S.tr (hj.trans (Nat.le_add_right k n)) (S.mulTensor k n ζ) := by
  induction ζ using TensorProduct.inductionOn with
  | tmul a x =>
      rw [TensorProduct.map_tmul, mulTensor_tmul, mulTopTensor_tmul,
        ← S.tr_tr hj (Nat.le_add_right k n), S.tr_mul_eq_mulTop_proj]
      rfl
  | add ζ ζ' hζ hζ' => simp only [map_add, hζ, hζ']

/-- **The inverse system `n ↦ Mₙ`** as a functor `ℕᵒᵖ ⥤ ModuleCat R`: the first of the two
systems of [Stacks, Tag 02OA] part (5). -/
def system : ℕᵒᵖ ⥤ ModuleCat.{v} R where
  obj n := ModuleCat.of R (M n.unop)
  map f := ModuleCat.ofHom (S.tr (leOfHom f.unop))
  map_id _ := by ext x; exact S.tr_self _ x
  map_comp _ _ := by ext x; exact (S.tr_tr _ _ x).symm

section Comparison

variable (c : ℕ)
  (hker : ∀ (m k : ℕ) (h : m ≤ k), m + c ≤ k →
    LinearMap.ker (S.proj k) ≤ LinearMap.ker (S.tr h))

include hker in
/-- The composite `Iⁿ ⊗ M₀ → Mₙ → M_j` kills the kernel of the presentation of `IⁿM₀`: an
element of that kernel is multiplied into `Ker(Mₙ → M₀)`, which is `Ker(Mₙ → M_j)` by
[Stacks, Tag 02OA] part (3). -/
theorem ker_idealPowerSmulLift_le {n j : ℕ} (hj : j + c ≤ n) :
    LinearMap.ker (idealPowerSmulLift I M₀ n) ≤
      LinearMap.ker ((S.tr ((Nat.le_add_right j c).trans hj)).comp
        (S.mulTopTensor (le_refl n))) := by
  intro ξ hξ
  refine LinearMap.mem_ker.2
    (hker j n ((Nat.le_add_right j c).trans hj) hj (LinearMap.mem_ker.2 ?_))
  rw [S.proj_mulTopTensor (le_refl n) ξ]
  exact LinearMap.mem_ker.1 hξ

/-- The presentation of `IⁿM₀` as a quotient of `Iⁿ ⊗ M₀`. -/
def quotEquiv (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule R M₀)) ≃ₗ[R]
      ((↥(I ^ n) ⊗[R] M₀) ⧸ LinearMap.ker (idealPowerSmulLift I M₀ n)) :=
  (LinearEquiv.ofEq _ _ (range_idealPowerSmulLift I M₀ n).symm).trans
    (LinearMap.quotKerEquivRange (idealPowerSmulLift I M₀ n)).symm

/-- The presentation of `IⁿM₀` as a quotient of `Iⁿ ⊗ M₀` sends an element `y` of `IⁿM₀` to the
class of any `ξ ∈ Iⁿ ⊗ M₀` presenting it. -/
theorem quotEquiv_apply {n : ℕ} (ξ : ↥(I ^ n) ⊗[R] M₀)
    (y : ↥(I ^ n • (⊤ : Submodule R M₀))) (hy : (y : M₀) = idealPowerSmulLift I M₀ n ξ) :
    quotEquiv (I := I) (M₀ := M₀) n y = Submodule.Quotient.mk ξ := by
  have h1 : (LinearEquiv.ofEq (I ^ n • (⊤ : Submodule R M₀))
      (LinearMap.range (idealPowerSmulLift I M₀ n))
      (range_idealPowerSmulLift I M₀ n).symm) y =
      ⟨idealPowerSmulLift I M₀ n ξ, LinearMap.mem_range_self _ ξ⟩ := Subtype.ext hy
  change (LinearMap.quotKerEquivRange (idealPowerSmulLift I M₀ n)).symm
      ((LinearEquiv.ofEq _ _ (range_idealPowerSmulLift I M₀ n).symm) y) = _
  rw [h1, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- **The comparison map `IⁿM₀ → M_j` of [Stacks, Tag 02OA] part (4)**, for `j + c ≤ n`: the
composite `Iⁿ ⊗ M₀ → Mₙ → M_j` descended along the presentation `Iⁿ ⊗ M₀ → IⁿM₀`, which is
legitimate by `ker_idealPowerSmulLift_le`. Part (4) of the source is the case `j = n - c`. -/
def comparison (n j : ℕ) (hj : j + c ≤ n) :
    ↥(I ^ n • (⊤ : Submodule R M₀)) →ₗ[R] M j :=
  (Submodule.liftQ (LinearMap.ker (idealPowerSmulLift I M₀ n))
      ((S.tr ((Nat.le_add_right j c).trans hj)).comp (S.mulTopTensor (le_refl n)))
      (S.ker_idealPowerSmulLift_le c hker hj)).comp
    (quotEquiv (I := I) (M₀ := M₀) n).toLinearMap

/-- **The comparison map, computed on a presentation.** This is the defining property of
`comparison`: on an element of `IⁿM₀` written as `Σ aᵢ • xᵢ` it is `Σ aᵢ · xᵢ`, read in `M_j`. -/
theorem comparison_apply {n j : ℕ} (hj : j + c ≤ n) (ξ : ↥(I ^ n) ⊗[R] M₀)
    (y : ↥(I ^ n • (⊤ : Submodule R M₀))) (hy : (y : M₀) = idealPowerSmulLift I M₀ n ξ) :
    S.comparison c hker n j hj y =
      S.tr ((Nat.le_add_right j c).trans hj) (S.mulTopTensor (le_refl n) ξ) := by
  change Submodule.liftQ _ _ (S.ker_idealPowerSmulLift_le c hker hj)
    (quotEquiv (I := I) (M₀ := M₀) n y) = _
  rw [quotEquiv_apply ξ y hy]
  exact Submodule.liftQ_apply _ _ ξ

/-- The comparison map out of `IⁿM₀` into `M_j`, computed on a presentation of the element in
`Iᵏ ⊗ M₀` for any `n ≤ k`. -/
private theorem comparison_apply_of_le {n k j : ℕ} (hj : j + c ≤ n) (hk : n ≤ k) (hjk : j ≤ k)
    (ξ : ↥(I ^ k) ⊗[R] M₀) (y : ↥(I ^ n • (⊤ : Submodule R M₀)))
    (hy : (y : M₀) = idealPowerSmulLift I M₀ k ξ) :
    S.comparison c hker n j hj y = S.tr hjk (S.mulTopTensor (le_refl k) ξ) := by
  rw [S.comparison_apply c hker hj _ y
    (hy.trans (idealPowerSmulLift_map_inclusion hk ξ).symm),
    S.tr_mulTopTensor_inclusion hk (le_refl k) (le_refl n) hjk (hj.trans' (Nat.le_add_right j c))
      ξ]

/-- The comparison maps out of one `IⁿM₀` into the various degrees are compatible with the
transition maps of the system. -/
theorem tr_comparison {n j j' : ℕ} (hj : j + c ≤ n) (hj' : j' + c ≤ n) (hjj' : j' ≤ j)
    (y : ↥(I ^ n • (⊤ : Submodule R M₀))) :
    S.tr hjj' (S.comparison c hker n j hj y) = S.comparison c hker n j' hj' y := by
  obtain ⟨ξ, hξ⟩ := exists_idealPowerSmulLift_eq y
  rw [S.comparison_apply c hker hj ξ y hξ.symm, S.comparison_apply c hker hj' ξ y hξ.symm,
    S.tr_tr hjj' (show j ≤ n by omega)]

/-- **The second composite of [Stacks, Tag 02OA] part (4) is the canonical map**: the composite
`IⁿM₀ → M_j → M₀` is the inclusion `IⁿM₀ ⊆ M₀`. Read inside `Iⁿ⁻²ᶜM₀`, which contains the image
of `M_{n-c} → M₀` by part (2), this is the source's statement that the composite
`IⁿM₀ → M_{n-c} → Iⁿ⁻²ᶜM₀` is the canonical map. -/
theorem proj_comparison {n j : ℕ} (hj : j + c ≤ n) (y : ↥(I ^ n • (⊤ : Submodule R M₀))) :
    S.proj j (S.comparison c hker n j hj y) = (y : M₀) := by
  obtain ⟨ξ, hξ⟩ := exists_idealPowerSmulLift_eq y
  rw [S.comparison_apply c hker hj ξ y hξ.symm, S.proj_tr (show j ≤ n by omega),
    S.proj_mulTopTensor (le_refl n) ξ, hξ]

/-- The comparison maps are compatible with the transition maps of both systems: for `n' ≤ n`
and `j' ≤ j`, the comparison out of `IⁿM₀` followed by `M_j → M_{j'}` is the comparison out of
`Iⁿ'M₀` of the same element of `M₀`. This is the naturality that makes the comparison maps a
morphism of pro-objects. -/
theorem comparison_tr {n n' j j' : ℕ} (hj : j + c ≤ n) (hj' : j' + c ≤ n') (hnn' : n' ≤ n)
    (hjj' : j' ≤ j) (y : ↥(I ^ n • (⊤ : Submodule R M₀)))
    (y' : ↥(I ^ n' • (⊤ : Submodule R M₀))) (hyy' : (y' : M₀) = (y : M₀)) :
    S.tr hjj' (S.comparison c hker n j hj y) = S.comparison c hker n' j' hj' y' := by
  obtain ⟨ξ, hξ⟩ := exists_idealPowerSmulLift_eq y
  rw [S.comparison_apply c hker hj ξ y hξ.symm,
    S.comparison_apply_of_le c hker hj' hnn' (show j' ≤ n by omega) ξ y' (hyy'.trans hξ.symm),
    S.tr_tr hjj' (show j ≤ n by omega)]

variable (hsurj : ∀ (r : ℕ) (hr : c ≤ r), Function.Surjective
  ((S.tr (Nat.sub_add_cancel hr).ge).comp (S.mulTensor (r - c) c)))

include hsurj in
/-- **The first composite of [Stacks, Tag 02OA] part (4) is the canonical map**: an element of
`Mₙ` projects into `Iⁿ'M₀` for `n' + c ≤ n`, and the comparison map carries that image to the
canonical image of the element in `M_j`. The source's statement is the case `n' = n - c`,
`j = n - 2c`.

This is where part (1) enters: the element of `Mₙ` is a sum of products `a · y` with
`a ∈ Iⁿ⁻ᶜ` and `y ∈ M_c`, and on such a product both maps are multiplication by `a`. -/
theorem comparison_proj {n n' j : ℕ} (hn : c ≤ n) (hn' : n' + c ≤ n) (hj : j + c ≤ n')
    (x : M n) (y : ↥(I ^ n' • (⊤ : Submodule R M₀))) (hy : (y : M₀) = S.proj n x) :
    S.comparison c hker n' j hj y =
      S.tr (((Nat.le_add_right j c).trans hj).trans
        ((Nat.le_add_right n' c).trans hn')) x := by
  obtain ⟨ζ, hζ⟩ := hsurj n hn x
  have hx : S.tr (show n ≤ n - c + c by omega) (S.mulTensor (n - c) c ζ) = x := hζ
  have hlift : idealPowerSmulLift I M₀ (n - c)
      (TensorProduct.map LinearMap.id (S.proj c) ζ) = (y : M₀) := by
    rw [hy, ← hx, S.proj_tr (show n ≤ n - c + c by omega),
      S.idealPowerSmulLift_map_proj (n - c) c ζ]
  rw [S.comparison_apply_of_le c hker hj (show n' ≤ n - c by omega) (show j ≤ n - c by omega) _ y
      hlift.symm,
    S.tr_mulTopTensor_map_proj (show j ≤ n - c by omega) ζ, ← hx,
    S.tr_tr (show j ≤ n by omega) (show n ≤ n - c + c by omega)]

variable (hrange : ∀ r : ℕ, c ≤ r →
  LinearMap.range (S.proj r) ≤ I ^ (r - c) • (⊤ : Submodule R M₀))

/-- **The forward map `M_{m+c} → IᵐM₀`** of the pro-isomorphism: the projection to `M₀`, whose
image lies in `IᵐM₀` by [Stacks, Tag 02OA] part (2). -/
def forwardMap (m : ℕ) : M (m + c) →ₗ[R] ↥(I ^ m • (⊤ : Submodule R M₀)) :=
  LinearMap.codRestrict _ (S.proj (m + c)) fun x ↦ by
    have h := hrange (m + c) (Nat.le_add_left c m) (LinearMap.mem_range_self _ x)
    rwa [Nat.add_sub_cancel] at h

/-- The forward map `M_{m+c} → IᵐM₀`, read in `M₀`, is the projection `M_{m+c} → M₀`. -/
@[simp]
theorem coe_forwardMap_apply (m : ℕ) (x : M (m + c)) :
    (S.forwardMap c hrange m x : M₀) = S.proj (m + c) x := rfl

include hker hsurj hrange in
/-- **[Stacks, Tag 02OA] part (5): the two inverse systems `(Mₙ)` and `(IⁿM₀)` are
pro-isomorphic**, by the cofinal shift `n ↦ n + c`: the forward maps are the projections
`M_{m+c} → IᵐM₀` of part (2), the backward maps are the comparison maps `Iᵐ⁺ᶜM₀ → M_m` of
part (4), and the two composites are the transition maps of the two systems by the two
identities of part (4).

The witness is stated as `Nonempty` of the pro-isomorphism data, as [Stacks, Tag 0H3D] is in
this library: the data itself is `Stacks.RingTheory.TopMulSystem.forwardMap` and
`Stacks.RingTheory.TopMulSystem.comparison`, which are definitions in their own right. -/
theorem nonempty_proIso :
    Nonempty (InverseSequence.ProIso S.system (idealPowerSmulSystem I M₀)) :=
  ⟨{ α := fun m ↦ m + c
     β := fun m ↦ m + c
     αmono := fun _ _ h ↦ Nat.add_le_add_right h c
     βmono := fun _ _ h ↦ Nat.add_le_add_right h c
     αle := fun _ ↦ Nat.le_add_right _ c
     βle := fun _ ↦ Nat.le_add_right _ c
     φ := fun m ↦ ModuleCat.ofHom (S.forwardMap c hrange m)
     ψ := fun m ↦ ModuleCat.ofHom (S.comparison c hker (m + c) m (le_refl _))
     φnat := fun {m m'} h ↦ by
       ext x
       exact Subtype.ext (S.proj_tr (Nat.add_le_add_right h c) x)
     ψnat := fun {m m'} h ↦ by
       ext z
       exact (S.comparison_tr c hker (le_refl (m' + c)) (le_refl (m + c))
         (Nat.add_le_add_right h c) h z _ rfl).symm
     ψφ := fun m ↦ by
       ext x
       exact S.comparison_proj c hker hsurj (Nat.le_add_left c (m + c))
         (le_refl (m + c + c)) (le_refl (m + c)) x (S.forwardMap c hrange (m + c) x) rfl
     φψ := fun m ↦ by
       ext z
       exact Subtype.ext (S.proj_comparison c hker (le_refl (m + c + c)) z) }⟩

end Comparison

end TopMulSystem

end Stacks.RingTheory

end
