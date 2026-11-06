module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the adic filtration of a flat module

Let `R` be a commutative ring, `𝔪 ⊆ R` an ideal and `M` a **flat** `R`-module. This file
identifies the `n`-th graded piece `𝔪ⁿM/𝔪ⁿ⁺¹M` of the `𝔪`-adic filtration of `M`:

* `Stacks.Flatness.gradedTensorEquivSmulTop` — multiplication gives an isomorphism
  `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M ≅ 𝔪ⁿ · (M/𝔪ⁿ⁺¹M)`;
* `Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv` — the same decomposition as a map, given an
  identification of `𝔪ⁿ/𝔪ⁿ⁺¹` with `κᵏ`; canonical in `M` once that identification is fixed;
* `Stacks.Flatness.exists_pi_linearEquiv_smul_top_of_flat` — if moreover `R` is Noetherian and
  `𝔪` is maximal, then `𝔪ⁿM/𝔪ⁿ⁺¹M` is a finite direct sum of copies of `M/𝔪M`, the number of
  copies being `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` for `κ = R/𝔪`;
* `Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv` and
  `Stacks.Flatness.exists_pi_linearEquiv_smul_top_of_flat_tower` — the same two statements for a
  module over a ring `T` through which `R` acts, with the ideal `𝔪 T` in place of `𝔪` and the
  equivalence linear over `T`.

The second statement is the algebraic step of the proof of
[Stacks, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU): the decomposition
`Iⁿ ℱ_(n+1) ≅ ℱ_1 ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹` which the source checks on the formal stalks, each of which is
flat over the Noetherian local base `R` by that tag's hypothesis (2), with `I = 𝔪A` by its
hypothesis (1). Only the module-theoretic content is here; nothing in this file mentions schemes.

## Implementation notes

`𝔪ⁿ/𝔪ⁿ⁺¹` is spelled `↥(𝔪 ^ n) ⧸ (𝔪 • ⊤)`, the quotient of the ideal viewed as a module by
`𝔪` times it; `Submodule.mem_smul_top_iff` says an element of `𝔪 ^ n` lies in that submodule
exactly when it lies in `𝔪 • 𝔪 ^ n = 𝔪 ^ (n + 1)`. This is the spelling Mathlib's
`Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow` uses, and for `n = 1` it is
`IsLocalRing.CotangentSpace`.

`𝔪ⁿM/𝔪ⁿ⁺¹M` is spelled as the submodule `𝔪 ^ n • ⊤` of `M ⧸ (𝔪 ^ (n + 1) • ⊤)` rather than as a
quotient of a submodule of `M`: that is the shape in which it arises as a subsheaf of a term of a
coherent adic system, and it avoids naming a subquotient.

Flatness enters once, through the injectivity of the multiplication map `𝔪ⁿ ⊗_R M → M`
(`Module.Flat.iff_rTensor_injective'`); its range is `𝔪ⁿM` unconditionally
(`Ideal.subtype_rTensor_range`). Those two facts turn the kernel of
`𝔪ⁿ ⊗_R M → M/𝔪ⁿ⁺¹M` into the image of `𝔪ⁿ⁺¹ ⊗_R M`, and right exactness of the tensor product
(`TensorProduct.quotientTensorEquiv`) then produces the graded piece.

The passage from `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M` to a finite product of copies of `M/𝔪M` uses that `𝔪ⁿ/𝔪ⁿ⁺¹`
is a finite-dimensional vector space over `κ = R/𝔪`: it is a finite `R`-module because `R` is
Noetherian, and it is a `κ`-module because `𝔪` annihilates it, which is the global instance
`Module (R ⧸ I) (M ⧸ I • ⊤)`. That vector-space step is isolated in
`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`, which does not mention `M`: it is the one
place a basis is chosen, so the number of copies and the identification with `κᵏ` are the same for
every flat `M` and the rest of the construction stays a map.

The first half of the file records only `R`-linearity. For a module `M` on which a larger ring `T`
acts, with `R` acting through a ring map `R → T`, the construction is in fact `T`-linear — every
map in sight is a tensor-product map in the `M` variable — and a geometric application that needs
a morphism of sheaves rather than a map of abelian groups needs that, because a morphism of
`𝒪`-modules is `𝒪`-linear on each stalk. Saying it requires the submodules `𝔪ᵏ • ⊤` to be
respelled as the `T`-submodules `(𝔪ᵏ T) • ⊤` — which have the same elements, by
`Ideal.smul_restrictScalars` — and the tensor products to be taken in
`TensorProduct.AlgebraTensorModule`, whose `M ⊗[R] N` is a `T`-module when the left factor is.
That is the section "The decomposition over the ring that acts" below, ending in
`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv`; the application is in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizationCoherentFormal/FlatOverLocalBase.lean`.
The `T`-linear chain is not transported from the `R`-linear one: the factor carrying the
`T`-action has to be the left one, and the exchange of factors is only `R`-linear.
-/

@[expose] public noncomputable section

open TensorProduct LinearMap

universe u v w

namespace Stacks.Flatness

variable {R : Type u} [CommRing R] (𝔪 : Ideal R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-! ### The multiplication map `𝔪ⁿ ⊗ M → M` -/

/-- Multiplication `x ⊗ m ↦ x • m` as a map `K ⊗_R M → M`, for an ideal `K`. Its range is `KM`
(`Ideal.subtype_rTensor_range`) and it is injective when `M` is flat. -/
def idealMulMap (K : Ideal R) : (↥K ⊗[R] M) →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ K.subtype.rTensor M

/-- `Stacks.Flatness.idealMulMap` sends `x ⊗ m` to `x • m`. -/
@[simp]
theorem idealMulMap_tmul (K : Ideal R) (x : ↥K) (m : M) :
    idealMulMap M K (x ⊗ₜ[R] m) = (x : R) • m := rfl

/-- The range of multiplication `K ⊗_R M → M` is `KM`. -/
theorem range_idealMulMap (K : Ideal R) :
    LinearMap.range (idealMulMap M K) = K • (⊤ : Submodule R M) :=
  Ideal.subtype_rTensor_range M K

/-- For `M` flat, multiplication `K ⊗_R M → M` is injective. -/
theorem injective_idealMulMap [Module.Flat R M] (K : Ideal R) :
    Function.Injective (idealMulMap M K) :=
  (TensorProduct.lid R M).injective.comp
    (Module.Flat.iff_rTensor_injective'.mp inferInstance K)

/-! ### The graded piece -/

section GradedPiece

variable (n : ℕ)

/-- `𝔪 ^ (n + 1)`, viewed inside `𝔪 ^ n` as the submodule `𝔪 • ⊤`. -/
theorem mem_smul_top_pow_iff (x : ↥(𝔪 ^ n)) :
    x ∈ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))) ↔ (x : R) ∈ 𝔪 ^ (n + 1) := by
  rw [Submodule.mem_smul_top_iff]
  simp [pow_succ']

/-- The inclusion of `𝔪 ^ (n + 1)` into the submodule `𝔪 • ⊤` of `𝔪 ^ n`. -/
def inclusionSmulTop :
    ↥(𝔪 ^ (n + 1)) →ₗ[R] ↥(𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))) :=
  LinearMap.codRestrict _
    (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ : 𝔪 ^ (n + 1) ≤ 𝔪 ^ n))
    fun x => (mem_smul_top_pow_iff 𝔪 n _).2 x.2

/-- The composite `𝔪ⁿ ⊗ M → M → M/𝔪ⁿ⁺¹M`. Its range is `𝔪ⁿ · (M/𝔪ⁿ⁺¹M)` and, for `M` flat, its
kernel is the image of `𝔪ⁿ⁺¹ ⊗ M`. -/
def gradedMulMap :
    (↥(𝔪 ^ n) ⊗[R] M) →ₗ[R] (M ⧸ (𝔪 ^ (n + 1) • (⊤ : Submodule R M))) :=
  (𝔪 ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ idealMulMap M (𝔪 ^ n)

/-- The image of `I • ⊤` under the quotient map by any submodule is `I • ⊤` of the quotient. -/
private theorem map_mkQ_smul_top {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N]
    [Module S N] (I : Ideal S) (P : Submodule S N) :
    (I • (⊤ : Submodule S N)).map P.mkQ = I • (⊤ : Submodule S (N ⧸ P)) := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

/-- The range of `𝔪ⁿ ⊗ M → M/𝔪ⁿ⁺¹M` is the submodule `𝔪ⁿ · (M/𝔪ⁿ⁺¹M)`. -/
theorem range_gradedMulMap :
    LinearMap.range (gradedMulMap 𝔪 M n) =
      𝔪 ^ n • (⊤ : Submodule R (M ⧸ (𝔪 ^ (n + 1) • (⊤ : Submodule R M)))) := by
  rw [gradedMulMap, LinearMap.range_comp, range_idealMulMap,
    map_mkQ_smul_top]

/-- For `M` flat, the kernel of `𝔪ⁿ ⊗ M → M/𝔪ⁿ⁺¹M` is the image of `𝔪ⁿ⁺¹ ⊗ M`, spelled as
`(𝔪 • ⊤) ⊗ M` with `𝔪 • ⊤` the submodule `𝔪ⁿ⁺¹` of `𝔪ⁿ`. -/
theorem ker_gradedMulMap [Module.Flat R M] :
    LinearMap.ker (gradedMulMap 𝔪 M n) =
      LinearMap.range ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M) := by
  refine le_antisymm ?_ ?_
  · have hcomp : (idealMulMap M (𝔪 ^ n)) ∘ₗ
        ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M) ∘ₗ
          ((inclusionSmulTop 𝔪 n).rTensor M) = idealMulMap M (𝔪 ^ (n + 1)) :=
      TensorProduct.ext' fun _ _ => rfl
    intro x hx
    have hx' : idealMulMap M (𝔪 ^ n) x ∈ 𝔪 ^ (n + 1) • (⊤ : Submodule R M) := by
      simpa [gradedMulMap, Submodule.Quotient.mk_eq_zero] using hx
    rw [← range_idealMulMap M (𝔪 ^ (n + 1)), LinearMap.mem_range] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨(inclusionSmulTop 𝔪 n).rTensor M y, injective_idealMulMap M (𝔪 ^ n) ?_⟩
    exact (congrArg (fun f => f y) hcomp).trans hy
  · rw [LinearMap.range_le_ker_iff]
    refine TensorProduct.ext' fun w m => ?_
    have hw : ((w : ↥(𝔪 ^ n)) : R) ∈ 𝔪 ^ (n + 1) := (mem_smul_top_pow_iff 𝔪 n _).1 w.2
    change (𝔪 ^ (n + 1) • (⊤ : Submodule R M)).mkQ (((w : ↥(𝔪 ^ n)) : R) • m) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hw Submodule.mem_top)

/-- **The graded pieces of the adic filtration of a flat module.** For `M` flat over `R`,
multiplication identifies `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M` with `𝔪ⁿM/𝔪ⁿ⁺¹M`, the latter read as the submodule
`𝔪ⁿ · (M/𝔪ⁿ⁺¹M)`.

Flatness is what makes the multiplication map `𝔪ⁿ ⊗_R M → M` injective, so that the kernel of
its composite with `M → M/𝔪ⁿ⁺¹M` is exactly the image of `𝔪ⁿ⁺¹ ⊗_R M`; right exactness of the
tensor product then identifies the quotient by that image with `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M`. -/
@[ega "0 10.1.1" "φ_n for flat M", ega "IV 16.2.4" "affine case, each n"]
def gradedTensorEquivSmulTop [Module.Flat R M] :
    ((↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ⊗[R] M) ≃ₗ[R]
      ↥(𝔪 ^ n • (⊤ : Submodule R (M ⧸ (𝔪 ^ (n + 1) • (⊤ : Submodule R M))))) :=
  (TensorProduct.quotientTensorEquiv M (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))).trans
    (((Submodule.quotEquivOfEq _ _ (ker_gradedMulMap 𝔪 M n).symm).trans
        (LinearMap.quotKerEquivRange (gradedMulMap 𝔪 M n))).trans
      (LinearEquiv.ofEq _ _ (range_gradedMulMap 𝔪 M n)))

end GradedPiece

/-! ### Decomposition into copies of `M/𝔪M` -/

/-- `𝔪ⁿ/𝔪ⁿ⁺¹` is a finite-dimensional vector space over the residue field `κ = R/𝔪`, hence
`R`-linearly isomorphic to `Fin k → κ` for some `k`.

This is the **only** choice made by the decomposition below, and it does not mention the module
being decomposed: both `k` and the identification depend on `R`, `𝔪` and `n` alone. -/
theorem exists_pi_linearEquiv_gradedPiece [IsNoetherianRing R] [𝔪.IsMaximal] (n : ℕ) :
    ∃ k : ℕ,
      Nonempty ((↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪))) := by
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hfinR : Module.Finite R ↥(𝔪 ^ n) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfin : Module.Finite (R ⧸ 𝔪) (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : Module.Free (R ⧸ 𝔪) (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) :=
    Module.Free.of_divisionRing (R ⧸ 𝔪) _
  exact ⟨_, ⟨((Module.finBasis (R ⧸ 𝔪) _).equivFun).restrictScalars R⟩⟩

/-- **The decomposition of the graded pieces of a flat module, as a map.** Given an
identification `e` of `𝔪ⁿ/𝔪ⁿ⁺¹` with `Fin k → κ`, the graded piece `𝔪ⁿM/𝔪ⁿ⁺¹M` of a flat module
`M` is `k` copies of `M/𝔪M`.

This is the content of `Stacks.Flatness.exists_pi_linearEquiv_smul_top_of_flat` with the choice
taken out: `e` does not mention `M`, so for a fixed `e` this equivalence is canonical in `M`, and
one `k` serves every flat `M` at once. That is what an application to a family of modules — the
formal stalks of a coherent adic system, in Stacks 0EJU — needs, and what the existence statement
cannot give. -/
def piEquivSmulTopOfGradedPieceEquiv [Module.Flat R M] {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪))) :
    (Fin k → (M ⧸ (𝔪 • (⊤ : Submodule R M)))) ≃ₗ[R]
      ↥(𝔪 ^ n • (⊤ : Submodule R (M ⧸ (𝔪 ^ (n + 1) • (⊤ : Submodule R M))))) :=
  (LinearEquiv.piCongrRight fun _ : Fin k =>
        (TensorProduct.tensorQuotEquivQuotSMul M 𝔪).symm).trans
    ((TensorProduct.piRight R R M fun _ : Fin k => (R ⧸ 𝔪)).symm.trans
      ((LinearEquiv.lTensor M e.symm).trans
        ((TensorProduct.comm R M _).trans (gradedTensorEquivSmulTop 𝔪 M n))))

/-- **The decomposition of the graded pieces of a flat module over a Noetherian local base.**
Let `R` be a Noetherian commutative ring, `𝔪 ⊆ R` a maximal ideal and `M` a flat `R`-module.
For every `n` the graded piece `𝔪ⁿM/𝔪ⁿ⁺¹M` is isomorphic to a finite direct sum of copies of
`M/𝔪M`; the number of copies is the dimension of `𝔪ⁿ/𝔪ⁿ⁺¹` over the residue field `R/𝔪`.

This is the statement `Iⁿ ℱ_(n+1) ≅ ℱ_1 ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹` of the proof of
[Stacks, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU), for a single flat module. -/
theorem exists_pi_linearEquiv_smul_top_of_flat [IsNoetherianRing R] [𝔪.IsMaximal]
    [Module.Flat R M] (n : ℕ) :
    ∃ k : ℕ, Nonempty ((Fin k → (M ⧸ (𝔪 • (⊤ : Submodule R M)))) ≃ₗ[R]
      ↥(𝔪 ^ n • (⊤ : Submodule R (M ⧸ (𝔪 ^ (n + 1) • (⊤ : Submodule R M)))))) := by
  obtain ⟨k, ⟨e⟩⟩ := exists_pi_linearEquiv_gradedPiece 𝔪 n
  exact ⟨k, ⟨piEquivSmulTopOfGradedPieceEquiv 𝔪 M n e⟩⟩

/-! ### The decomposition over the ring that acts

Everything above is `R`-linear, which is not enough for a module `M` carrying an action of a
larger ring `T` through which `R` acts: a morphism of `T`-modules is more than an `R`-linear map,
so an `R`-linear equivalence is not a candidate for one. This section repeats the construction
over `T`. Two changes make that possible and they are the two the remark at the top of the file
asks for: the submodules `𝔪ᵏ • ⊤` of `M` are respelled as the `T`-submodules `(𝔪ᵏT) • ⊤`, which
have the same elements by `Ideal.smul_restrictScalars`, and the tensor products are taken in
`TensorProduct.AlgebraTensorModule`, whose `M ⊗[R] N` is a `T`-module when the left factor is.

The left factor must be the one carrying the `T`-action, so the multiplication map is written
`M ⊗[R] 𝔪ⁿ → M` here and `𝔪ⁿ ⊗[R] M → M` above; the two differ by `TensorProduct.comm`, which is
only `R`-linear, and that is why the construction is repeated rather than transported. Flatness is
still flatness over `R`: the module is not assumed flat over `T`.
-/

/-- Two submodules of one module with the same elements — one over the ring that acts, one over a
subring — are the same module over the subring.

This is the `Submodule` half of the respelling carried out below: by
`Ideal.smul_restrictScalars` the submodules `𝔪ᵏ • ⊤` and `(𝔪ᵏT) • ⊤` of a `T`-module have the same
elements, and this turns that equality of elements into an equivalence of modules. -/
def restrictScalarsSubmoduleEquiv {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    [Algebra A B] {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (P : Submodule B N) (P' : Submodule A N) (h : P.restrictScalars A = P') : ↥P ≃ₗ[A] ↥P' where
  toFun x := ⟨x.1, by rw [← h]; exact x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨x.1, by
    have hx : (x : N) ∈ P.restrictScalars A := by rw [h]; exact x.2
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Tower

variable (T : Type w) [CommRing T] [Algebra R T] [Module T M] [IsScalarTower R T M]

/-- Multiplication `m ⊗ x ↦ x • m` as a `T`-linear map `M ⊗[R] K → M`, for `K` an ideal of `R`
acting on `M` through `T`.

This is `Stacks.Flatness.idealMulMap` with the factors exchanged, so that the factor carrying the
`T`-action is on the left and the tensor product is a `T`-module. -/
def towerIdealMulMap (K : Ideal R) : (M ⊗[R] ↥K) →ₗ[T] M :=
  (TensorProduct.AlgebraTensorModule.rid R T M).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor T M K.subtype

/-- `Stacks.Flatness.towerIdealMulMap` sends `m ⊗ x` to `x • m`. -/
@[simp]
theorem towerIdealMulMap_tmul (K : Ideal R) (m : M) (x : ↥K) :
    towerIdealMulMap M T K (m ⊗ₜ[R] x) = (x : R) • m := rfl

/-- `Stacks.Flatness.towerIdealMulMap` is `Stacks.Flatness.idealMulMap` after exchanging the
factors. -/
theorem towerIdealMulMap_apply (K : Ideal R) (z : M ⊗[R] ↥K) :
    towerIdealMulMap M T K z = idealMulMap M K (TensorProduct.comm R M ↥K z) := by
  induction z with
  | tmul m x => simp
  | add z z' hz hz' => simp [hz, hz']

/-- The range of `M ⊗[R] K → M`, viewed over `R`, is the range of `K ⊗[R] M → M`. -/
theorem restrictScalars_range_towerIdealMulMap (K : Ideal R) :
    (LinearMap.range (towerIdealMulMap M T K)).restrictScalars R =
      LinearMap.range (idealMulMap M K) :=
  Submodule.ext fun x => by
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    exact ⟨fun ⟨z, hz⟩ => ⟨TensorProduct.comm R M ↥K z,
        (towerIdealMulMap_apply M T K z).symm.trans hz⟩,
      fun ⟨z, hz⟩ => ⟨(TensorProduct.comm R M ↥K).symm z, by
        rw [towerIdealMulMap_apply]; simpa using hz⟩⟩

/-- The range of multiplication `M ⊗[R] K → M` is the `T`-submodule `(KT) • ⊤`: the elements of
`KM` are the same whether `K` or its image in `T` is made to act. -/
theorem range_towerIdealMulMap (K : Ideal R) :
    LinearMap.range (towerIdealMulMap M T K) =
      (K.map (algebraMap R T)) • (⊤ : Submodule T M) :=
  Submodule.restrictScalars_injective R T M <| by
    rw [restrictScalars_range_towerIdealMulMap, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top, range_idealMulMap]

/-- For `M` flat over `R`, multiplication `M ⊗[R] K → M` is injective. -/
theorem injective_towerIdealMulMap [Module.Flat R M] (K : Ideal R) :
    Function.Injective (towerIdealMulMap M T K) := fun z z' h => by
  refine (TensorProduct.comm R M ↥K).injective (injective_idealMulMap M K ?_)
  rw [← towerIdealMulMap_apply M T K, ← towerIdealMulMap_apply M T K]
  exact h

section TowerGradedPiece

variable (n : ℕ)

/-- The composite `M ⊗[R] 𝔪ⁿ → M → M/(𝔪ⁿ⁺¹T)M`, as a `T`-linear map. -/
def towerGradedMulMap :
    (M ⊗[R] ↥(𝔪 ^ n)) →ₗ[T]
      (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) :=
  ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)).mkQ ∘ₗ
    towerIdealMulMap M T (𝔪 ^ n)

/-- The range of `M ⊗[R] 𝔪ⁿ → M/(𝔪ⁿ⁺¹T)M` is the `T`-submodule `(𝔪ⁿT) · (M/(𝔪ⁿ⁺¹T)M)`. -/
theorem range_towerGradedMulMap :
    LinearMap.range (towerGradedMulMap 𝔪 M T n) =
      (𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))) := by
  rw [towerGradedMulMap, LinearMap.range_comp, range_towerIdealMulMap, Ideal.map_pow,
    map_mkQ_smul_top]

/-- For `M` flat over `R`, the kernel of `M ⊗[R] 𝔪ⁿ → M/(𝔪ⁿ⁺¹T)M` is the image of
`M ⊗[R] 𝔪ⁿ⁺¹`, spelled as `M ⊗[R] (𝔪 • ⊤)` with `𝔪 • ⊤` the submodule `𝔪ⁿ⁺¹` of `𝔪ⁿ`. -/
theorem ker_towerGradedMulMap [Module.Flat R M] :
    LinearMap.ker (towerGradedMulMap 𝔪 M T n) =
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor T M
        ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.restrictScalars R)) := by
  refine le_antisymm ?_ ?_
  · have hcomp : (towerIdealMulMap M T (𝔪 ^ n)) ∘ₗ
        (TensorProduct.AlgebraTensorModule.lTensor T M
          ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.restrictScalars R)) ∘ₗ
          (TensorProduct.AlgebraTensorModule.lTensor T M (inclusionSmulTop 𝔪 n)) =
        towerIdealMulMap M T (𝔪 ^ (n + 1)) :=
      TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl
    intro z hz
    have hz' : towerIdealMulMap M T (𝔪 ^ n) z ∈
        LinearMap.range (towerIdealMulMap M T (𝔪 ^ (n + 1))) := by
      rw [range_towerIdealMulMap, Ideal.map_pow]
      simpa [towerGradedMulMap, Submodule.Quotient.mk_eq_zero] using hz
    exact hz'.elim fun y hy =>
      ⟨TensorProduct.AlgebraTensorModule.lTensor T M (inclusionSmulTop 𝔪 n) y,
        injective_towerIdealMulMap M T (𝔪 ^ n) ((congrArg (fun f => f y) hcomp).trans hy)⟩
  · rw [LinearMap.range_le_ker_iff]
    refine TensorProduct.AlgebraTensorModule.ext fun m w => ?_
    have hw : ((w : ↥(𝔪 ^ n)) : R) ∈ 𝔪 ^ (n + 1) := (mem_smul_top_pow_iff 𝔪 n _).1 w.2
    change ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)).mkQ
        (((w : ↥(𝔪 ^ n)) : R) • m) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hsmul : ((w : ↥(𝔪 ^ n)) : R) • m = algebraMap R T ((w : ↥(𝔪 ^ n)) : R) • m :=
      (algebraMap_smul T _ m).symm
    rw [← Ideal.map_pow, hsmul]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hw) Submodule.mem_top

/-- **The graded pieces of the adic filtration of a flat module, over the ring that acts.** For
`M` a `T`-module flat over `R`, multiplication identifies `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M` with
`(𝔪ⁿT)M/(𝔪ⁿ⁺¹T)M` *as `T`-modules*, the latter read as the `T`-submodule `(𝔪ⁿT) • (M/(𝔪ⁿ⁺¹T)M)`.

This is `Stacks.Flatness.gradedTensorEquivSmulTop` with the ring that acts put back: the tensor
product is the `T`-module `TensorProduct.AlgebraTensorModule` and every submodule in sight is a
`T`-submodule. -/
@[ega "0 10.1.1" "φ_n for flat M", ega "IV 16.2.4" "affine case", sga "1 IV 5.5" "(i)⇒(iii)"]
def towerGradedTensorEquivSmulTop [Module.Flat R M] :
    (M ⊗[R] (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))))) ≃ₗ[T]
      ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))))) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv T R M
      (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))).trans
    (((Submodule.quotEquivOfEq _ _ (ker_towerGradedMulMap 𝔪 M T n).symm).trans
        (LinearMap.quotKerEquivRange (towerGradedMulMap 𝔪 M T n))).trans
      (LinearEquiv.ofEq _ _ (range_towerGradedMulMap 𝔪 M T n)))

end TowerGradedPiece

/-- `M ⊗_R κ ≅ M/(𝔪T)M` for `κ = R/𝔪`, as `T`-modules. -/
def towerTensorResidueEquivQuotSmulTop :
    (M ⊗[R] (R ⧸ 𝔪)) ≃ₗ[T] (M ⧸ ((𝔪.map (algebraMap R T)) • (⊤ : Submodule T M))) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv T R M (𝔪 : Submodule R R)).trans
    (Submodule.Quotient.equiv _ _ (TensorProduct.AlgebraTensorModule.rid R T M) (by
      have hcomp : (TensorProduct.AlgebraTensorModule.rid R T M).toLinearMap ∘ₗ
          TensorProduct.AlgebraTensorModule.lTensor T M
            ((𝔪 : Submodule R R).subtype.restrictScalars R) =
          towerIdealMulMap M T 𝔪 := rfl
      rw [← LinearMap.range_comp, hcomp, range_towerIdealMulMap]))

/-- **The decomposition of the graded pieces of a flat module, over the ring that acts, as a
map.** Given an identification `e` of `𝔪ⁿ/𝔪ⁿ⁺¹` with `Fin k → κ`, the graded piece
`(𝔪ⁿT)M/(𝔪ⁿ⁺¹T)M` of a `T`-module `M` flat over `R` is `k` copies of `M/(𝔪T)M`, `T`-linearly.

This is `Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv` over the ring that acts. As there, `e`
does not mention `M`, so one `k` and one equivalence formula serve every flat `M` at once — and
now the equivalence is a map of `T`-modules, which is what a family of modules over varying rings
`T` glued into a sheaf requires of its stalkwise pieces. -/
def towerPiEquivSmulTopOfGradedPieceEquiv [Module.Flat R M] {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪))) :
    (Fin k → (M ⧸ ((𝔪.map (algebraMap R T)) • (⊤ : Submodule T M)))) ≃ₗ[T]
      ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))))) :=
  (LinearEquiv.piCongrRight fun _ : Fin k =>
        (towerTensorResidueEquivQuotSmulTop 𝔪 M T).symm).trans
    ((TensorProduct.piRight R T M fun _ : Fin k => (R ⧸ 𝔪)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T M) e.symm).trans
        (towerGradedTensorEquivSmulTop 𝔪 M T n)))

/-- **The decomposition of the graded pieces of a flat module over a Noetherian local base, over
the ring that acts.** For `M` a `T`-module flat over `R`, with `R` Noetherian and `𝔪` maximal,
the graded piece `(𝔪ⁿT)M/(𝔪ⁿ⁺¹T)M` is a finite direct sum of copies of `M/(𝔪T)M` *as
`T`-modules*. -/
theorem exists_pi_linearEquiv_smul_top_of_flat_tower [IsNoetherianRing R] [𝔪.IsMaximal]
    [Module.Flat R M] (n : ℕ) :
    ∃ k : ℕ, Nonempty ((Fin k → (M ⧸ ((𝔪.map (algebraMap R T)) • (⊤ : Submodule T M)))) ≃ₗ[T]
      ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))))) := by
  obtain ⟨k, ⟨e⟩⟩ := exists_pi_linearEquiv_gradedPiece 𝔪 n
  exact ⟨k, ⟨towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e⟩⟩

/-! ### The decomposition as multiplication by a lift of a basis

`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv` is a composite of four maps, so its
*value* is not visible in its definition, and a consumer that builds the decomposition by hand
cannot recognise what it has built as that equivalence. The formula is the expected one: choose
a representative `aᵢ ∈ 𝔪ⁿ` of each basis vector, lift each component of the argument to `M`,
multiply and add.

The two consequences below are what a bijectivity argument consumes, and they are stated without
quotients or tensor products: multiplication by the chosen `aᵢ` sends a tuple into `𝔪ⁿ⁺¹M` only
if every component already lies in `𝔪M`, and every element of `𝔪ⁿM` is such a combination up to
`𝔪ⁿ⁺¹M`. That shape is what survives transport along an isomorphism of the ambient module.
-/

/-- `M ⊗_R κ ≅ M/(𝔪T)M` carries `m ⊗ 1` to the class of `m`. -/
theorem towerTensorResidueEquivQuotSmulTop_tmul_one (m : M) :
    towerTensorResidueEquivQuotSmulTop 𝔪 M T (m ⊗ₜ[R] (1 : R ⧸ 𝔪)) =
      Submodule.Quotient.mk m := by
  change Submodule.Quotient.mk
      ((TensorProduct.AlgebraTensorModule.rid R T M) (m ⊗ₜ[R] (1 : R))) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]

/-- The graded-piece identification over the ring that acts, on a generator: `m ⊗ x̄` is the
class of `x • m`. -/
theorem towerGradedTensorEquivSmulTop_tmul_mk [Module.Flat R M] (n : ℕ) (m : M)
    (x : ↥(𝔪 ^ n)) :
    ((towerGradedTensorEquivSmulTop 𝔪 M T n (m ⊗ₜ[R] Submodule.Quotient.mk x) :
          ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
            (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))))) :
        M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) =
      Submodule.Quotient.mk ((x : R) • m) :=
  rfl

/-- **The value of the decomposition.** With `aᵢ = xᵢ` a representative in `𝔪ⁿ` of the `i`-th
basis vector of `𝔪ⁿ/𝔪ⁿ⁺¹` under `e`, the equivalence
`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv` sends the tuple of classes of `mᵢ` to the
class of `∑ aᵢ mᵢ`. -/
theorem towerPiEquivSmulTopOfGradedPieceEquiv_apply_coe [Module.Flat R M] {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
    (x : Fin k → ↥(𝔪 ^ n))
    (hx : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i))
    (m : Fin k → M) :
    ((towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e
            (fun i => Submodule.Quotient.mk (m i)) :
          ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
            (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))))) :
        M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) =
      Submodule.Quotient.mk (∑ i, (x i : R) • m i) := by
  classical
  have hcomp : (towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e
        (fun i => Submodule.Quotient.mk (m i)) :
      ↥((𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))))) =
      towerGradedTensorEquivSmulTop 𝔪 M T n
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T M) e.symm
          ((TensorProduct.piRight R T M fun _ : Fin k => (R ⧸ 𝔪)).symm
            (fun i => (towerTensorResidueEquivQuotSmulTop 𝔪 M T).symm
              (Submodule.Quotient.mk (m i))))) :=
    rfl
  have hstep1 : (fun i => (towerTensorResidueEquivQuotSmulTop 𝔪 M T).symm
        (Submodule.Quotient.mk (m i))) =
      fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪) :=
    funext fun i => (LinearEquiv.symm_apply_eq _).2
      (towerTensorResidueEquivQuotSmulTop_tmul_one 𝔪 M T (m i)).symm
  have hstep2 : (TensorProduct.piRight R T M fun _ : Fin k => (R ⧸ 𝔪)).symm
        (fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) =
      ∑ i : Fin k, m i ⊗ₜ[R] Pi.single i (1 : R ⧸ 𝔪) := by
    have hv : (fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) =
        ∑ i : Fin k, Pi.single i (m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) :=
      (Finset.univ_sum_single _).symm
    rw [hv, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      TensorProduct.piRight_symm_single R T M (fun _ : Fin k => (R ⧸ 𝔪)) (m i) i _
  have hmk : ∀ f : Fin k → M, (Submodule.Quotient.mk (∑ i, f i) :
        M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) =
      ∑ i, (Submodule.Quotient.mk (f i) :
        M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) := fun f =>
    map_sum ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)).mkQ f Finset.univ
  rw [hcomp, hstep1, hstep2, map_sum, map_sum, AddSubmonoidClass.coe_finsetSum,
    hmk fun i => (x i : R) • m i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hx i]
  exact towerGradedTensorEquivSmulTop_tmul_mk 𝔪 M T n (m i) (x i)

/-- **Injectivity of the decomposition, as a statement about `M` alone.** If the multiples of a
tuple `(mᵢ)` by representatives `xᵢ` of a basis of `𝔪ⁿ/𝔪ⁿ⁺¹` add up into `𝔪ⁿ⁺¹M`, then every
`mᵢ` already lies in `𝔪M`.

This is injectivity of `Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv`, read through
`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv_apply_coe`. The basis and its
representatives are arguments rather than existentials: an application that decomposes a whole
family of modules needs one choice of them for the whole family, and the `xᵢ` do not mention the
module. -/
theorem mem_smul_top_of_sum_smul_mem [Module.Flat R M] {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
    (x : Fin k → ↥(𝔪 ^ n))
    (hx : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i))
    (m : Fin k → M)
    (hm : (∑ i, (x i : R) • m i) ∈
      (𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)) (i : Fin k) :
    m i ∈ (𝔪.map (algebraMap R T)) • (⊤ : Submodule T M) := by
  have key := towerPiEquivSmulTopOfGradedPieceEquiv_apply_coe 𝔪 M T n e x hx m
  have hzero : towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e
      (fun j => Submodule.Quotient.mk (m j)) = 0 := by
    refine Subtype.ext ?_
    rw [key]
    exact (Submodule.Quotient.mk_eq_zero _).2 hm
  have hv := (towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e).injective
    (hzero.trans (map_zero _).symm)
  have hi : (Submodule.Quotient.mk (m i) :
      M ⧸ ((𝔪.map (algebraMap R T)) • (⊤ : Submodule T M))) = 0 := congrFun hv i
  exact (Submodule.Quotient.mk_eq_zero _).1 hi

/-- **Surjectivity of the decomposition, as a statement about `M` alone.** Every element of
`𝔪ⁿM` is, modulo `𝔪ⁿ⁺¹M`, a combination `∑ xᵢ mᵢ` of representatives `xᵢ` of a basis of
`𝔪ⁿ/𝔪ⁿ⁺¹`.

This is surjectivity of `Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv`; as in
`Stacks.Flatness.mem_smul_top_of_sum_smul_mem`, the basis is an argument. -/
theorem exists_sum_smul_sub_mem [Module.Flat R M] {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
    (x : Fin k → ↥(𝔪 ^ n))
    (hx : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i))
    {u : M} (hu : u ∈ (𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T M)) :
    ∃ m : Fin k → M, u - (∑ i, (x i : R) • m i) ∈
      (𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M) := by
  classical
  have humem : (Submodule.Quotient.mk u :
        M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M))) ∈
      (𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T
        (M ⧸ ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)))) := by
    rw [← map_mkQ_smul_top]
    exact Submodule.mem_map_of_mem hu
  obtain ⟨v, hv⟩ :=
    (towerPiEquivSmulTopOfGradedPieceEquiv 𝔪 M T n e).surjective ⟨_, humem⟩
  choose m hm using fun i : Fin k =>
    Submodule.Quotient.mk_surjective
      ((𝔪.map (algebraMap R T)) • (⊤ : Submodule T M)) (v i)
  refine ⟨m, ?_⟩
  have hveq : v = fun i => Submodule.Quotient.mk (m i) := funext fun i => (hm i).symm
  rw [hveq] at hv
  have key := towerPiEquivSmulTopOfGradedPieceEquiv_apply_coe 𝔪 M T n e x hx m
  rw [hv] at key
  refine (Submodule.Quotient.mk_eq_zero _).1 ?_
  have hsub : ((𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)).mkQ
      (u - ∑ i, (x i : R) • m i) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact key
  exact hsub

/-- **The decomposition of the graded pieces of a flat module, as multiplication by a lift of a
basis.** For `M` a `T`-module flat over `R`, with `R` Noetherian and `𝔪` maximal, there are `k`
elements `aᵢ ∈ 𝔪ⁿ` such that

* a tuple `(mᵢ)` with `∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺¹M` has every `mᵢ` in `𝔪M`, and
* every `u ∈ 𝔪ⁿM` is `∑ aᵢ mᵢ` modulo `𝔪ⁿ⁺¹M`.

These are `Stacks.Flatness.mem_smul_top_of_sum_smul_mem` and
`Stacks.Flatness.exists_sum_smul_sub_mem` with the choice of basis packed away. The powers of `𝔪`
are those of the image ideal `𝔪T`, the ideal of the ring that acts.

Only the flatness of `M` over `R` is used, and it is used only for the first assertion; the second
holds for every module. -/
theorem exists_lift_basis_smul_of_flat_tower [IsNoetherianRing R] [𝔪.IsMaximal]
    [Module.Flat R M] (n : ℕ) :
    ∃ (k : ℕ) (a : Fin k → R), (∀ i, a i ∈ 𝔪 ^ n) ∧
      (∀ m : Fin k → M,
        (∑ i, a i • m i) ∈ (𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M) →
          ∀ i, m i ∈ (𝔪.map (algebraMap R T)) • (⊤ : Submodule T M)) ∧
      (∀ u ∈ (𝔪.map (algebraMap R T)) ^ n • (⊤ : Submodule T M),
        ∃ m : Fin k → M,
          u - (∑ i, a i • m i) ∈
            (𝔪.map (algebraMap R T)) ^ (n + 1) • (⊤ : Submodule T M)) := by
  classical
  obtain ⟨k, ⟨e⟩⟩ := exists_pi_linearEquiv_gradedPiece 𝔪 n
  choose x hx using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))
      (e.symm (Pi.single i (1 : R ⧸ 𝔪)))
  exact ⟨k, fun i => (x i : R), fun i => (x i).2,
    fun m hm i => mem_smul_top_of_sum_smul_mem 𝔪 M T n e x (fun j => (hx j).symm) m hm i,
    fun _ hu => exists_sum_smul_sub_mem 𝔪 M T n e x (fun j => (hx j).symm) hu⟩

end Tower

end Stacks.Flatness

end
