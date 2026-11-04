module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltration

/-!
# Linearity over the completed ring of a map out of an adic completion

Let `A` be a commutative ring, `I ⊆ A` a finitely generated ideal and `M` an `A`-module. The
`I`-adic completion `M ^∧_I` is a module over the completed ring `A ^∧_I`, and the `A`-module
structure of `M ^∧_I` is the restriction of that one along `A ⟶ A ^∧_I`. This file records the
one fact that makes an `A`-linear map out of `M ^∧_I` automatically `A ^∧_I`-linear as soon as
its target is annihilated by a power of `I`:

if `I ^ n` annihilates `Q` and `ψ : M ^∧_I ⟶ Q` is `A`-linear, then `ψ (r • x) = a • ψ x` for
every `r : A ^∧_I` and every `a : A` whose class in `A ⧸ I ^ n` is the `n`-th component of `r`.

The mechanism is Mathlib's `AdicCompletion.pow_smul_top_eq_ker_eval`: for `I` finitely
generated, an element of `M ^∧_I` whose `n`-th component vanishes lies in `I ^ n M ^∧_I`.
Applied to `r • x - a • x`, whose `n`-th component is `(r_n - a) • x_n = 0`, it puts that
difference in `I ^ n M ^∧_I`, which an `A`-linear map carries into `I ^ n Q = 0`.

This is the whole of the passage from an `𝒪_{Y, y}`-linear isomorphism to an
`𝒪 ^∧_{Y, y}`-linear one in the theorem on formal functions: both sides there are limits of
towers whose `n`-th term is killed by `𝔪_y ^ n`, so the `n`-th component of any `𝒪_{Y, y}`-linear
map out of a completion is already `𝒪 ^∧_{Y, y}`-linear, and a map into a limit is determined by
its components.

## Main results

* `Stacks.FormalFunctions.sub_smul_mem_pow_smul_top`: for `I` finitely generated,
  `r • x - a • x ∈ I ^ n M ^∧_I` whenever `r` and `a` agree in `A ⧸ I ^ n`.
* `Stacks.FormalFunctions.map_adicCompletion_smul`: the statement above.
* `Stacks.FormalFunctions.towerLimit_smul_mem`: the `A ^∧_I`-action on the limit of a tower all
  of whose terms are killed by the corresponding power of `I`, read on components.
-/

@[expose] public section

namespace Stacks.FormalFunctions

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- **An element of `R ^∧_I` and a scalar of `R` with the same class in the `n`-th truncation act
on `M ^∧_I` in ways that differ by `I ^ n M ^∧_I`.** For `I` finitely generated this is
`AdicCompletion.pow_smul_top_eq_ker_eval` applied to `r • x - a • x`, whose `n`-th component is
zero by construction. -/
public theorem sub_smul_mem_pow_smul_top (hI : I.FG) {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module R M] (r : AdicCompletion I R) (a : R)
    (ha : eval I R n r = eval I R n (of I R a)) (x : AdicCompletion I M) :
    r • x - a • x ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
  have hof : (of I R a : AdicCompletion I R) • x = a • x := by
    rw [show (of I R a : AdicCompletion I R) = algebraMap R (AdicCompletion I R) a from rfl,
      algebraMap_smul]
  have ha' : r.val n = (of I R a : AdicCompletion I R).val n := ha
  rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, ← hof, eval_apply, eval_apply,
    smul_eval, smul_eval, ha', sub_self]

/-- **An `R`-linear map out of `M ^∧_I` into a module annihilated by `I ^ n` is already linear
for the completed ring**, read at the level `n`: the scalar `r : R ^∧_I` acts as any `a : R`
representing its class in the `n`-th truncation. -/
public theorem map_adicCompletion_smul (hI : I.FG) {n : ℕ} {M Q : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup Q] [Module R Q]
    (hQ : I ^ n • (⊤ : Submodule R Q) = ⊥) (ψ : AdicCompletion I M →ₗ[R] Q)
    (r : AdicCompletion I R) (a : R) (ha : eval I R n r = eval I R n (of I R a))
    (x : AdicCompletion I M) : ψ (r • x) = a • ψ x := by
  have h := map_mem_pow_smul_top ψ I n (sub_smul_mem_pow_smul_top hI r a ha x)
  rw [hQ, Submodule.mem_bot, map_sub, sub_eq_zero] at h
  rw [h]
  exact ψ.map_smul a x

/-- Every class in the `n`-th truncation of `R ^∧_I` is represented by a scalar of `R`. -/
public theorem exists_eval_eq (n : ℕ) (r : AdicCompletion I R) :
    ∃ a : R, eval I R n r = eval I R n (of I R a) :=
  Quotient.inductionOn' (eval I R n r) fun a => ⟨a, rfl⟩

/-! ### Transporting a tower limit along an isomorphism of towers -/

open Stacks.IntertwinedFiltration

/-- The limit of a tower of modules over a ring `B` is the limit of the same tower read over a
base ring `A` acting through `B`: the two submodules of the product have the same carrier. -/
public def towerLimitRestrictScalars (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)] [∀ n, Module B (P n)]
    [∀ n, IsScalarTower A B (P n)] (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[B] P m) :
    towerLimit P (fun m n h => (T m n h).restrictScalars A) ≃ₗ[A] towerLimit P T where
  toFun x := ⟨(x : ∀ k, P k), x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨(x : ∀ k, P k), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **An `R`-linear map into the limit of a tower killed by the powers of `I` is automatically
linear over `R ^∧_I`.** Each component is `map_adicCompletion_smul`, and an element of the limit
is determined by its components. -/
public theorem map_adicCompletion_smul_towerLimit (hI : I.FG) {M : Type*} [AddCommGroup M]
    [Module R M] (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
    [∀ n, Module (AdicCompletion I R) (P n)]
    [∀ n, IsScalarTower R (AdicCompletion I R) (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[AdicCompletion I R] P m)
    (hP : ∀ n, I ^ n • (⊤ : Submodule R (P n)) = ⊥)
    (hsmul : ∀ (n : ℕ) (r : AdicCompletion I R) (a : R),
      eval I R n r = eval I R n (of I R a) → ∀ z : P n, r • z = a • z)
    (E : AdicCompletion I M →ₗ[R] towerLimit P T)
    (r : AdicCompletion I R) (x : AdicCompletion I M) : E (r • x) = r • E x := by
  refine Subtype.ext (funext fun n => ?_)
  obtain ⟨a, ha⟩ := exists_eval_eq n r
  have hE : ((towerLimit.proj n : towerLimit P T →ₗ[AdicCompletion I R] P n).restrictScalars
      R).comp E (r • x) = a • ((towerLimit.proj n :
        towerLimit P T →ₗ[AdicCompletion I R] P n).restrictScalars R).comp E x :=
    map_adicCompletion_smul hI (hP n) _ r a ha x
  exact hE.trans (hsmul n r a ha ((E x : ∀ k, P k) n)).symm

end Stacks.FormalFunctions

end
