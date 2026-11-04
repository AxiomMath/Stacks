module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.BigOperators.Pi

/-!
# A small model of `Mᵛ ⊗ N` for a finite projective module `M`

Let `R` be a commutative ring, let `M` be a finite projective `R`-module and let `N` be an
arbitrary `R`-module. The module `Mᵛ ⊗_R N`, with `Mᵛ = Hom_R(M, R)`, naively lives in the
universe of `R`, `M` and `N` together, a dual being a module of maps into the base ring. This
file produces a model of it in the universe of `N` alone.

The construction is the splitting of a finite free presentation. Choose a surjection
`p : R^n → M` and, by projectivity, a section `σ : M → R^n` with `p ∘ σ = id`, and write
`eᵢ = p(δᵢ)` and `cᵢ = (σ ·)ᵢ ∈ Mᵛ`, so that `∑ᵢ cᵢ(m) • eᵢ = m` for every `m`. The `R`-linear
map `Mᵛ ⊗ N → Nⁿ`, `λ ⊗ y ↦ (i ↦ λ(eᵢ) • y)`, then has the `R`-linear retraction
`Nⁿ → Mᵛ ⊗ N`, `y ↦ ∑ᵢ cᵢ ⊗ yᵢ`: on a generator `λ ⊗ y` the composite is
`(∑ᵢ λ(eᵢ) • cᵢ) ⊗ y`, and the first factor sends `m` to `λ(∑ᵢ cᵢ(m) • eᵢ) = λ(m)`. Hence the
map is injective and `Mᵛ ⊗ N` is `R`-linearly isomorphic to its range, a submodule of `Nⁿ` and
so a module in the universe of `N`.

## Main definitions

* `Stacks.DualTensor.smallModel`: the submodule of `Nⁿ` modelling `Mᵛ ⊗_R N`.
* `Stacks.DualTensor.smallModelEquiv`: the `R`-linear isomorphism
  `Mᵛ ⊗_R N ≃ₗ[R] smallModel R M N`.

## Implementation notes

The presentation data `n`, `p`, `σ` is chosen with `Classical.choice`, so `smallModel` is not
canonical; only its isomorphism class is.
-/

@[expose] public noncomputable section

open Function TensorProduct

universe u w w'

namespace Stacks.DualTensor

variable (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- The length of a chosen finite free presentation `Rⁿ ↠ M` of a finite module `M`. -/
def rank : ℕ := (Module.Finite.exists_fin' R M).choose

/-- A chosen surjection `R^(rank R M) ↠ M`. -/
def proj : (Fin (rank R M) → R) →ₗ[R] M :=
  (Module.Finite.exists_fin' R M).choose_spec.choose

/-- The chosen map `Stacks.DualTensor.proj` is surjective. -/
lemma proj_surjective : Surjective (proj R M) :=
  (Module.Finite.exists_fin' R M).choose_spec.choose_spec

/-- The `i`-th of the chosen generators of `M`, namely the image of the `i`-th standard basis
vector under `Stacks.DualTensor.proj`. -/
def gen (i : Fin (rank R M)) : M := proj R M (Pi.single i 1)

variable (N : Type w') [AddCommGroup N] [Module R N]

/-- Evaluation of the dual factor at a fixed element of `M`, as a bilinear map. -/
def evalBilin (m : M) : Module.Dual R M →ₗ[R] N →ₗ[R] N :=
  LinearMap.mk₂ R (fun (l : Module.Dual R M) (y : N) => l m • y)
    (fun _ _ _ => by simp [add_smul]) (fun _ _ _ => by simp [mul_smul])
    (fun _ _ _ => by simp [smul_add]) (fun c _ y => smul_comm _ c y)

/-- The comparison map `Mᵛ ⊗_R N → Nⁿ`, `λ ⊗ y ↦ (i ↦ λ(eᵢ) • y)`, attached to the chosen
presentation of `M`. -/
def toPi : Module.Dual R M ⊗[R] N →ₗ[R] (Fin (rank R M) → N) :=
  LinearMap.pi fun i => TensorProduct.lift (evalBilin R M N (gen R M i))

/-- The comparison map sends `λ ⊗ y` to `i ↦ λ(eᵢ) • y`. -/
@[simp]
lemma toPi_tmul (l : Module.Dual R M) (y : N) (i : Fin (rank R M)) :
    toPi R M N (l ⊗ₜ y) i = l (gen R M i) • y := by
  simp [toPi, evalBilin]

variable [Module.Projective R M]

/-- A chosen `R`-linear section of `Stacks.DualTensor.proj`, which exists because `M` is
projective. -/
def sect : M →ₗ[R] (Fin (rank R M) → R) :=
  (LinearMap.exists_rightInverse_of_surjective (proj R M)
    (LinearMap.range_eq_top.2 (proj_surjective R M))).choose

/-- `Stacks.DualTensor.sect` is a section of `Stacks.DualTensor.proj`. -/
@[simp]
lemma proj_sect (m : M) : proj R M (sect R M m) = m :=
  congrArg (fun f : M →ₗ[R] M => f m)
    (LinearMap.exists_rightInverse_of_surjective (proj R M)
      (LinearMap.range_eq_top.2 (proj_surjective R M))).choose_spec

/-- The `i`-th coordinate of the chosen section, as an element of the dual of `M`. -/
def coord (i : Fin (rank R M)) : Module.Dual R M := (LinearMap.proj i).comp (sect R M)

/-- The `i`-th dual coordinate of `m` is the `i`-th coordinate of its image under the chosen
section. -/
@[simp]
lemma coord_apply (i : Fin (rank R M)) (m : M) : coord R M i m = sect R M m i := rfl

/-- The chosen generators and dual coordinates give a (non-canonical) finite "dual basis"
decomposition `m = ∑ᵢ cᵢ(m) • eᵢ` of every element of a finite projective module. -/
lemma sum_coord_smul_gen (m : M) : ∑ i : Fin (rank R M), coord R M i m • gen R M i = m := by
  have h := (Pi.basisFun R (Fin (rank R M))).sum_repr (sect R M m)
  simp only [Pi.basisFun_repr, Pi.basisFun_apply] at h
  calc ∑ i : Fin (rank R M), coord R M i m • gen R M i
      = proj R M (∑ i : Fin (rank R M), sect R M m i • (Pi.single i 1 : Fin (rank R M) → R)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [gen]
    _ = m := by rw [h, proj_sect]

/-- Two `R`-linear maps out of a finite projective module agree as soon as they agree on the
chosen generators. -/
lemma linearMap_eq_of_forall_gen {P : Type*} [AddCommGroup P] [Module R P]
    {f f' : M →ₗ[R] P} (h : ∀ i, f (gen R M i) = f' (gen R M i)) : f = f' := by
  ext m
  rw [← sum_coord_smul_gen R M m]
  simp only [map_sum, map_smul, h]

/-- The retraction `Nⁿ → Mᵛ ⊗_R N`, `y ↦ ∑ᵢ cᵢ ⊗ yᵢ`, attached to the chosen section. -/
def fromPi : (Fin (rank R M) → N) →ₗ[R] Module.Dual R M ⊗[R] N :=
  ∑ i : Fin (rank R M),
    (TensorProduct.mk R (Module.Dual R M) N (coord R M i)).comp (LinearMap.proj i)

/-- The retraction sends `y` to `∑ᵢ cᵢ ⊗ yᵢ`. -/
lemma fromPi_apply (y : Fin (rank R M) → N) :
    fromPi R M N y = ∑ i : Fin (rank R M), coord R M i ⊗ₜ y i := by
  simp [fromPi, LinearMap.sum_apply]

/-- The comparison map is split injective, the retraction being
`Stacks.DualTensor.fromPi`. -/
lemma fromPi_comp_toPi : (fromPi R M N).comp (toPi R M N) = LinearMap.id := by
  refine TensorProduct.ext' fun l y => ?_
  have hsum : ∑ i : Fin (rank R M), l (gen R M i) • coord R M i = l := by
    ext m
    simpa [mul_comm, map_sum] using
      congrArg l (sum_coord_smul_gen R M m)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, fromPi_apply, toPi_tmul]
  calc ∑ i : Fin (rank R M), coord R M i ⊗ₜ (l (gen R M i) • y)
      = (∑ i : Fin (rank R M), l (gen R M i) • coord R M i) ⊗ₜ y := by
        rw [TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun i _ => by
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = l ⊗ₜ y := by rw [hsum]

/-- The comparison map `Mᵛ ⊗_R N → Nⁿ` is injective. -/
lemma toPi_injective : Injective (toPi R M N) :=
  Function.LeftInverse.injective (g := fromPi R M N)
    (LinearMap.congr_fun (fromPi_comp_toPi R M N))

/-- A model of `Mᵛ ⊗_R N` living in the universe of `N`: a submodule of `Nⁿ` for a chosen
finite free presentation `Rⁿ ↠ M` of the finite projective module `M`. -/
def smallModel : Submodule R (Fin (rank R M) → N) := LinearMap.range (toPi R M N)

/-- The `R`-linear isomorphism identifying `Mᵛ ⊗_R N` with its model
`Stacks.DualTensor.smallModel` in the universe of `N`. -/
def smallModelEquiv : Module.Dual R M ⊗[R] N ≃ₗ[R] smallModel R M N :=
  LinearEquiv.ofInjective (toPi R M N) (toPi_injective R M N)

/-- The isomorphism `Stacks.DualTensor.smallModelEquiv` is the comparison map. -/
@[simp]
lemma smallModelEquiv_coe (x : Module.Dual R M ⊗[R] N) :
    (smallModelEquiv R M N x : Fin (rank R M) → N) = toPi R M N x := rfl

end Stacks.DualTensor
