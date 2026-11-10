module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `ℓ`-adic Tate module of an abelian group

Let `M` be an abelian group and `ℓ` a prime. The `ℓ`-adic Tate module of `M` is the inverse limit
`T_ℓ M = lim_n M[ℓ^n]` of the `ℓ^n`-torsion subgroups, the transition maps being multiplication by
`ℓ`. Here it is the group of sequences `x : ℕ → M` with `x 0 = 0` and `ℓ • x (n + 1) = x n`, so
that `ℓ ^ n • x n = 0`, with the `ℤ_ℓ`-module structure `(a • x) n = (a mod ℓ^n) • x n`.

## Main definitions

* `Stacks.AbelianGroup.tateModule M ℓ`: the Tate module, a `ℤ_[ℓ]`-module.
* `Stacks.AbelianGroup.tateModuleMap ℓ f`: the `ℤ_[ℓ]`-linear map induced by `f : M →+ N`.
* `Stacks.AbelianGroup.torsionMap f n`: the restriction `M[n] →+ N[n]` of `f`; for an
  isomorphism, `Stacks.AbelianGroup.torsionAddEquiv`.
* `Stacks.AbelianGroup.tateReduction ℓ n`: the projection `T_ℓ M →+ M[ℓ^n]`, `x ↦ x n`.
* `Stacks.AbelianGroup.tateQuotientEquiv`: `T_ℓ M ⧸ ℓ^n T_ℓ M ≃+ M[ℓ^n]` when `M` is
  `ℓ`-divisible.

## Main results

Assume `M` is `ℓ`-divisible and `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n`.

* `Stacks.AbelianGroup.nonempty_linearEquiv_tateModule`: `T_ℓ M ≅ ℤ_ℓ^r`; hence
  `Stacks.AbelianGroup.module_free_tateModule` and `Stacks.AbelianGroup.finrank_tateModule`.
* `Stacks.AbelianGroup.toZModPow_trace_tateModuleMap`: for an endomorphism `f` of `M`, the trace
  of `T_ℓ f` reduced mod `ℓ^n` is the trace over `ℤ/ℓ^n` of `f` on `M[ℓ^n]`, transported along any
  isomorphism of `M[ℓ^n]` with a `ℤ/ℓ^n`-module.

## Implementation notes

The base's `CompletionSequences.adicTateModule` is the same inverse limit taken in `ModuleCat A`
for an `A`-module; it carries no `ℤ_ℓ`-module structure, which is what is needed here, so the
limit is built concretely. Freeness follows the compatible-bases argument: lift an `𝔽_ℓ`-basis of
`M[ℓ]` to `T_ℓ M`; by divisibility the lifts reduce to a `ℤ/ℓ^n`-basis of every `M[ℓ^n]`, and so
form a `ℤ_ℓ`-basis of `T_ℓ M`.
-/

@[expose] public noncomputable section

open PadicInt Pointwise

namespace Stacks.AbelianGroup

section Basic

variable (M : Type*) [AddCommGroup M] (ℓ : ℕ)

/-- The subgroup of `ℕ → M` of the sequences `x` with `x 0 = 0` and `ℓ • x (n + 1) = x n`. -/
def tateSubgroup : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    exact ⟨by simp [hx0, hy0], fun n => by simp [smul_add, hx, hy]⟩
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    exact ⟨by simp [hx0], fun n => by simp [hx]⟩

variable {M ℓ} in
/-- A sequence `x : ℕ → M` lies in `tateSubgroup M ℓ` iff `x 0 = 0` and `ℓ • x (n + 1) = x n`. -/
theorem mem_tateSubgroup {x : ℕ → M} :
    x ∈ tateSubgroup M ℓ ↔ x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n :=
  Iff.rfl

/-- The `ℓ`-adic Tate module `T_ℓ M = lim_n M[ℓ^n]` of an abelian group `M`: the sequences
`x : ℕ → M` with `x 0 = 0` and `ℓ • x (n + 1) = x n`. -/
@[sga "1 XI 2.1", sga "7 I 6.1" "partial"]
abbrev tateModule : Type _ :=
  tateSubgroup M ℓ

variable {M ℓ}

/-- The `0`-th component of an element of `T_ℓ M` vanishes. -/
theorem seq_zero (x : tateModule M ℓ) : (x : ℕ → M) 0 = 0 :=
  (mem_tateSubgroup.1 x.2).1

/-- For `x` in `T_ℓ M`, `ℓ • x (n + 1) = x n`. -/
theorem smul_seq_succ (x : tateModule M ℓ) (n : ℕ) :
    ℓ • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (mem_tateSubgroup.1 x.2).2 n

/-- For a sequence `s` with `ℓ • s (k + 1) = s k`, `ℓ ^ k • s (n + k) = s n`. -/
private theorem pow_smul_add_of_smul_succ {s : ℕ → M} (hs : ∀ k, ℓ • s (k + 1) = s k) (n k : ℕ) :
    ℓ ^ k • s (n + k) = s n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← smul_smul, ← add_assoc, hs, ih]

/-- For `x` in `T_ℓ M`, `ℓ ^ k • x (n + k) = x n`. -/
theorem pow_smul_seq_add (x : tateModule M ℓ) (n k : ℕ) :
    ℓ ^ k • (x : ℕ → M) (n + k) = (x : ℕ → M) n :=
  pow_smul_add_of_smul_succ (smul_seq_succ x) n k

/-- Multiplying `∑ i, c i • (E i) (n + 1)` by `ℓ` gives `∑ i, c i • (E i) n`. -/
private theorem smul_sum_nsmul_seq_succ {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ)
    (c : ι → ℕ) (n : ℕ) :
    ℓ • ∑ i, c i • (E i : ℕ → M) (n + 1) = ∑ i, c i • (E i : ℕ → M) n := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, smul_seq_succ]

/-- For `x` in `T_ℓ M`, the `n`-th component `x n` is `ℓ ^ n`-torsion. -/
theorem pow_smul_seq (x : tateModule M ℓ) (n : ℕ) : ℓ ^ n • (x : ℕ → M) n = 0 := by
  simpa [seq_zero] using pow_smul_seq_add x 0 n

/-- Two elements of `T_ℓ M` with the same components are equal. -/
@[ext]
theorem tateModule_ext {x y : tateModule M ℓ} (h : ∀ n, (x : ℕ → M) n = (y : ℕ → M) n) :
    x = y :=
  Subtype.ext (funext h)

/-- The `n`-th component of a finite sum in `T_ℓ M` is the sum of the `n`-th components. -/
theorem seq_sum {ι : Type*} (s : Finset ι) (f : ι → tateModule M ℓ) (n : ℕ) :
    ((∑ i ∈ s, f i : tateModule M ℓ) : ℕ → M) n = ∑ i ∈ s, (f i : ℕ → M) n :=
  map_sum ((Pi.evalAddMonoidHom (fun _ : ℕ => M) n).comp (tateSubgroup M ℓ).subtype) f s

/-- If `N • y = 0`, then `a • y` depends only on `a` modulo `N`. -/
theorem nsmul_eq_nsmul_of_natCast_eq {N : ℕ} {y : M} (hy : N • y = 0) {a b : ℕ}
    (h : (a : ZMod N) = b) : a • y = b • y := by
  rw [nsmul_eq_mod_nsmul a hy, nsmul_eq_mod_nsmul b hy, (ZMod.natCast_eq_natCast_iff' a b N).1 h]

end Basic

section Module

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- A power of a prime `ℓ` is nonzero. -/
instance (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n hℓ.out.ne_zero⟩

/-- For `m ≤ n`, the residue of `a` modulo `ℓ^n`, cast to `ℤ/ℓ^m`, is the residue of `a` modulo
`ℓ^m`. -/
theorem natCast_val_toZModPow_of_le {m n : ℕ} (h : m ≤ n) (a : ℤ_[ℓ]) :
    (((toZModPow n a).val : ℕ) : ZMod (ℓ ^ m)) = toZModPow m a := by
  rw [ZMod.natCast_val, cast_toZModPow m n h]

/-- The action of `ℤ_[ℓ]` on `T_ℓ M`, `(a • x) n = (a mod ℓ^n) • x n`. -/
instance : SMul ℤ_[ℓ] (tateModule M ℓ) where
  smul a x := ⟨fun n => (toZModPow n a).val • (x : ℕ → M) n, mem_tateSubgroup.2
    ⟨by simp [seq_zero x], fun n => by
      rw [smul_comm, smul_seq_succ]
      exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
        (by rw [natCast_val_toZModPow_of_le (Nat.le_succ n), ZMod.natCast_zmod_val])⟩⟩

/-- The `n`-th component of `a • x` is `(a mod ℓ^n) • x n`. -/
theorem smul_seq (a : ℤ_[ℓ]) (x : tateModule M ℓ) (n : ℕ) :
    ((a • x : tateModule M ℓ) : ℕ → M) n = (toZModPow n a).val • (x : ℕ → M) n :=
  rfl

/-- The Tate module `T_ℓ M` is a module over the `ℓ`-adic integers. -/
instance : Module ℤ_[ℓ] (tateModule M ℓ) where
  one_smul x := by
    ext n
    rw [smul_seq]
    exact (nsmul_eq_nsmul_of_natCast_eq (b := 1) (pow_smul_seq x n)
      (by rw [ZMod.natCast_zmod_val, map_one, Nat.cast_one])).trans (one_nsmul _)
  mul_smul a b x := by
    ext n
    rw [smul_seq, smul_seq, smul_seq, smul_smul]
    exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
      (by rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        map_mul])
  smul_zero a := by
    ext n
    simp [smul_seq]
  smul_add a x y := by
    ext n
    simp [smul_seq]
  add_smul a b x := by
    ext n
    simp only [smul_seq, AddSubgroup.coe_add, Pi.add_apply, ← add_nsmul]
    exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
      (by rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        map_add])
  zero_smul x := by
    ext n
    simp [smul_seq]

end Module

section Map

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] (ℓ : ℕ)
  [Fact ℓ.Prime]

/-- The `ℤ_[ℓ]`-linear map `T_ℓ M → T_ℓ N` induced by an additive map `f : M →+ N`. -/
@[sga "7 IX 1.0" "partial"]
def tateModuleMap (f : M →+ N) : tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule N ℓ where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), mem_tateSubgroup.2
    ⟨by simp [seq_zero x], fun n => by rw [← map_nsmul, smul_seq_succ]⟩⟩
  map_add' x y := by
    ext n
    simp
  map_smul' a x := by
    ext n
    simp [smul_seq]

variable {ℓ}

/-- The `n`-th component of `T_ℓ f x` is `f (x n)`. -/
@[simp]
theorem tateModuleMap_seq (f : M →+ N) (x : tateModule M ℓ) (n : ℕ) :
    ((tateModuleMap ℓ f x : tateModule N ℓ) : ℕ → N) n = f ((x : ℕ → M) n) :=
  rfl

variable (ℓ)

/-- The identity of `M` induces the identity of `T_ℓ M`. -/
@[simp]
theorem tateModuleMap_id : tateModuleMap ℓ (AddMonoidHom.id M) = LinearMap.id := by
  ext x n
  rfl

/-- The induced map of a composite is the composite of the induced maps. -/
theorem tateModuleMap_comp (g : N →+ P) (f : M →+ N) :
    tateModuleMap ℓ (g.comp f) = tateModuleMap ℓ g ∘ₗ tateModuleMap ℓ f := by
  ext x n
  rfl

/-- The zero map induces the zero map on Tate modules. -/
@[simp]
theorem tateModuleMap_zero : tateModuleMap ℓ (0 : M →+ N) = 0 := by
  ext x n
  simp

/-- `T_ℓ (f + g) = T_ℓ f + T_ℓ g`. -/
theorem tateModuleMap_add (f g : M →+ N) :
    tateModuleMap ℓ (f + g) = tateModuleMap ℓ f + tateModuleMap ℓ g := by
  ext x n
  simp

/-- `T_ℓ (-f) = -T_ℓ f`. -/
theorem tateModuleMap_neg (f : M →+ N) : tateModuleMap ℓ (-f) = -tateModuleMap ℓ f := by
  ext x n
  simp

/-- `T_ℓ (f - g) = T_ℓ f - T_ℓ g`. -/
theorem tateModuleMap_sub (f g : M →+ N) :
    tateModuleMap ℓ (f - g) = tateModuleMap ℓ f - tateModuleMap ℓ g := by
  ext x n
  simp

/-- `T_ℓ (k • f) = k • T_ℓ f` for `k : ℕ`. -/
theorem tateModuleMap_nsmul (k : ℕ) (f : M →+ N) :
    tateModuleMap ℓ (k • f) = k • tateModuleMap ℓ f := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, tateModuleMap_add, ih, succ_nsmul]

/-- `T_ℓ (k • f) = k • T_ℓ f` for `k : ℤ`. -/
theorem tateModuleMap_zsmul (k : ℤ) (f : M →+ N) :
    tateModuleMap ℓ (k • f) = k • tateModuleMap ℓ f := by
  cases k with
  | ofNat k => simpa using tateModuleMap_nsmul ℓ k f
  | negSucc k => rw [negSucc_zsmul, negSucc_zsmul, tateModuleMap_neg, tateModuleMap_nsmul]

end Map

section Torsion

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The restriction `M[n] →+ N[n]` of an additive map `f : M →+ N` to the `n`-torsion. -/
def torsionMap (f : M →+ N) (n : ℤ) :
    AddSubgroup.torsionBy M n →+ AddSubgroup.torsionBy N n where
  toFun x := ⟨f (x : M), (Submodule.mem_torsionBy_iff _ _).2 (by
    rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero])⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f (x : M) y)

/-- `torsionMap f n` acts as `f` on the underlying elements. -/
@[simp]
theorem coe_torsionMap (f : M →+ N) (n : ℤ) (x : AddSubgroup.torsionBy M n) :
    (torsionMap f n x : N) = f (x : M) :=
  rfl

/-- The restriction `M[n] ≃+ N[n]` of an additive isomorphism `e : M ≃+ N` to the `n`-torsion. -/
def torsionAddEquiv (e : M ≃+ N) (n : ℤ) :
    AddSubgroup.torsionBy M n ≃+ AddSubgroup.torsionBy N n where
  __ := torsionMap e.toAddMonoidHom n
  invFun := torsionMap e.symm.toAddMonoidHom n
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

/-- `torsionAddEquiv e n` acts as `e` on the underlying elements. -/
@[simp]
theorem coe_torsionAddEquiv (e : M ≃+ N) (n : ℤ) (x : AddSubgroup.torsionBy M n) :
    (torsionAddEquiv e n x : N) = e (x : M) :=
  rfl

variable (M) in
/-- The two spellings `AddSubgroup.torsionBy M ↑(ℓ ^ n)` and `Submodule.torsionBy ℤ M (↑ℓ ^ n)` of
the `ℓ^n`-torsion of `M`. -/
def torsionByNatCastPowEquiv (ℓ n : ℕ) :
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ Submodule.torsionBy ℤ M ((ℓ : ℤ) ^ n) where
  toFun x := ⟨x, (Submodule.mem_torsionBy_iff _ _).2
    (by rw [← Nat.cast_pow]; exact (Submodule.mem_torsionBy_iff _ _).1 x.2)⟩
  invFun x := ⟨x, (Submodule.mem_torsionBy_iff _ _).2
    (by rw [Nat.cast_pow]; exact (Submodule.mem_torsionBy_iff _ _).1 x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `torsionByNatCastPowEquiv M ℓ n` is the identity on the underlying elements. -/
@[simp]
theorem coe_torsionByNatCastPowEquiv (ℓ n : ℕ) (x : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)) :
    (torsionByNatCastPowEquiv M ℓ n x : M) = x :=
  rfl

end Torsion

section Reduction

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The projection `T_ℓ M →+ M[ℓ^n]`, `x ↦ x n`. -/
def tateReduction (n : ℕ) : tateModule M ℓ →+ AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) where
  toFun x := ⟨(x : ℕ → M) n, AddSubgroup.torsionBy.nsmul_iff.2 (pow_smul_seq x n)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ℓ}

omit [Fact (Nat.Prime ℓ)] in
/-- The underlying element of `tateReduction ℓ n x` is `x n`. -/
@[simp]
theorem coe_tateReduction (n : ℕ) (x : tateModule M ℓ) :
    (tateReduction ℓ n x : M) = (x : ℕ → M) n :=
  rfl

/-- The reduction of `a • x` modulo `ℓ^n` is `(a mod ℓ^n) • (x mod ℓ^n)`. -/
theorem coe_tateReduction_smul (n : ℕ) (a : ℤ_[ℓ]) (x : tateModule M ℓ) :
    (tateReduction ℓ n (a • x) : M) = (toZModPow n a).val • (tateReduction ℓ n x : M) :=
  rfl

/-- The reduction is equivariant: `(T_ℓ f x) mod ℓ^n = f (x mod ℓ^n)`. -/
theorem tateReduction_tateModuleMap (n : ℕ) (f : M →+ N) (x : tateModule M ℓ) :
    tateReduction ℓ n (tateModuleMap ℓ f x) = torsionMap f _ (tateReduction ℓ n x) :=
  rfl

omit [Fact (Nat.Prime ℓ)] in
/-- If `M` is `ℓ`-divisible, every `z : M` starts a sequence `s` with `s 0 = z` and
`ℓ • s (k + 1) = s k`. -/
theorem exists_divisionChain (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (z : M) :
    ∃ s : ℕ → M, s 0 = z ∧ ∀ k, ℓ • s (k + 1) = s k :=
  ⟨fun k => Nat.rec z (fun _ y => Classical.choose (hdiv y)) k, rfl,
    fun _ => Classical.choose_spec (hdiv _)⟩

omit [Fact (Nat.Prime ℓ)] in
/-- If `M` is `ℓ`-divisible, every `ℓ^n`-torsion point lifts to the Tate module. -/
theorem tateReduction_surjective (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (n : ℕ) :
    Function.Surjective (tateReduction (M := M) ℓ n) := by
  rintro ⟨z, hz⟩
  obtain ⟨s, hs0, hs⟩ := exists_divisionChain hdiv z
  refine ⟨⟨fun m => ℓ ^ n • s m, mem_tateSubgroup.2 ⟨?_, fun m => ?_⟩⟩,
    Subtype.ext (by simpa [hs0] using pow_smul_add_of_smul_succ hs 0 n :
      ℓ ^ n • s n = z)⟩
  · rw [hs0]
    exact AddSubgroup.torsionBy.nsmul_iff.1 hz
  · rw [smul_comm, hs]

/-- The residue of `ℓ ^ n` modulo `ℓ^n` is zero. -/
theorem toZModPow_pow_self (n : ℕ) : toZModPow n ((ℓ : ℤ_[ℓ]) ^ n) = 0 := by
  rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

/-- The residue of `ℓ ^ n` modulo `ℓ^m`, read as a natural number, is `ℓ ^ n` in `ℤ/ℓ^m`. -/
theorem natCast_val_toZModPow_pow (m n : ℕ) :
    (((toZModPow m ((ℓ : ℤ_[ℓ]) ^ n)).val : ℕ) : ZMod (ℓ ^ m)) = ((ℓ ^ n : ℕ) : ZMod (ℓ ^ m)) := by
  rw [ZMod.natCast_zmod_val, map_pow, map_natCast, Nat.cast_pow]

/-- The kernel of the reduction `T_ℓ M → M[ℓ^n]` is `ℓ^n T_ℓ M`. -/
theorem tateReduction_eq_zero_iff (n : ℕ) (x : tateModule M ℓ) :
    tateReduction ℓ n x = 0 ↔
      x ∈ ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule M ℓ)) := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    have hn : (x : ℕ → M) n = 0 := congrArg Subtype.val h
    let y : tateModule M ℓ := ⟨fun m => (x : ℕ → M) (m + n), mem_tateSubgroup.2
      ⟨by simpa using hn, fun m => by rw [Nat.add_right_comm, smul_seq_succ]⟩⟩
    refine ⟨y, Submodule.mem_top, ?_⟩
    ext m
    rw [smul_seq]
    exact (nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq y m) (natCast_val_toZModPow_pow m n)).trans
      (pow_smul_seq_add x m n)
  · rintro ⟨y, -, rfl⟩
    refine Subtype.ext ?_
    change (toZModPow n ((ℓ : ℤ_[ℓ]) ^ n)).val • (y : ℕ → M) n = 0
    rw [toZModPow_pow_self, ZMod.val_zero, zero_nsmul]

/-- The kernel of the reduction `T_ℓ M → M[ℓ^n]`, as a `ℤ`-submodule, is `ℓ^n T_ℓ M`. -/
theorem ker_tateReduction (n : ℕ) :
    LinearMap.ker (tateReduction (M := M) ℓ n).toIntLinearMap =
      (((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule M ℓ))).restrictScalars ℤ := by
  ext x
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, ← tateReduction_eq_zero_iff]
  rfl

/-- **The Tate module modulo `ℓ^n`.** If `M` is `ℓ`-divisible, reduction induces
`T_ℓ M ⧸ ℓ^n T_ℓ M ≃+ M[ℓ^n]`. -/
def tateQuotientEquiv (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (n : ℕ) :
    (tateModule M ℓ ⧸ ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule M ℓ))) ≃+
      AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) :=
  ((Submodule.Quotient.restrictScalarsEquiv ℤ _).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_tateReduction n).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (tateReduction_surjective hdiv n)))).toAddEquiv

/-- `tateQuotientEquiv` sends the class of `x` to its reduction `tateReduction ℓ n x`. -/
@[simp]
theorem tateQuotientEquiv_mk (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (n : ℕ) (x : tateModule M ℓ) :
    tateQuotientEquiv hdiv n (Submodule.Quotient.mk x) = tateReduction ℓ n x :=
  rfl

/-- The map `T_ℓ f` sends `ℓ^n T_ℓ M` into `ℓ^n T_ℓ N`. -/
theorem pow_smul_top_le_comap_tateModuleMap (n : ℕ) (f : M →+ N) :
    ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule M ℓ)) ≤
      (((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule N ℓ))).comap (tateModuleMap ℓ f) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- The isomorphism `T_ℓ M ⧸ ℓ^n ≃+ M[ℓ^n]` is equivariant for the maps induced by `f`. -/
theorem tateQuotientEquiv_mapQ (hdivM : ∀ x : M, ∃ y, ℓ • y = x)
    (hdivN : ∀ x : N, ∃ y, ℓ • y = x) (n : ℕ) (f : M →+ N)
    (q : tateModule M ℓ ⧸ ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule M ℓ))) :
    tateQuotientEquiv hdivN n (Submodule.mapQ _ _ (tateModuleMap ℓ f)
        (pow_smul_top_le_comap_tateModuleMap n f) q) =
      torsionMap f _ (tateQuotientEquiv hdivM n q) := by
  induction q using Submodule.Quotient.induction_on with
  | H x => rfl

end Reduction

section Free

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The combination `∑ i, (c i).val • (E i) n` of the `n`-th components of a family `E` of elements
of `T_ℓ M`, with coefficients in `ℤ/ℓ^n`. -/
def tateLevelCombination {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ) (n : ℕ)
    (c : ι → ZMod (ℓ ^ n)) : M :=
  ∑ i, (c i).val • (E i : ℕ → M) n

omit hℓ in
/-- The combination `tateLevelCombination E n c` is `ℓ^n`-torsion. -/
theorem pow_smul_tateLevelCombination {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ) (n : ℕ)
    (c : ι → ZMod (ℓ ^ n)) : ℓ ^ n • tateLevelCombination E n c = 0 := by
  simp [tateLevelCombination, Finset.smul_sum, smul_comm (ℓ ^ n), pow_smul_seq]

omit hℓ in
/-- The combination with zero coefficients is zero. -/
@[simp]
theorem tateLevelCombination_zero {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ) (n : ℕ) :
    tateLevelCombination E n 0 = 0 := by
  simp [tateLevelCombination]

/-- The `n`-th component of `∑ i, a i • E i` is the combination of the `(E i) n` with coefficients
`a i` modulo `ℓ^n`. -/
theorem seq_linearCombination {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ) (a : ι → ℤ_[ℓ])
    (n : ℕ) :
    ((Fintype.linearCombination ℤ_[ℓ] E a : tateModule M ℓ) : ℕ → M) n =
      tateLevelCombination E n (fun i => toZModPow n (a i)) := by
  rw [Fintype.linearCombination_apply, seq_sum]
  rfl

/-- Reducing the coefficients from `ℤ/ℓ^(n+1)` to `ℤ/ℓ^n` corresponds to multiplying the
combination by `ℓ`. -/
theorem tateLevelCombination_cast {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ) (n : ℕ)
    (c : ι → ZMod (ℓ ^ (n + 1))) :
    tateLevelCombination E n (fun i => ZMod.cast (c i)) =
      ℓ • tateLevelCombination E (n + 1) c := by
  rw [tateLevelCombination, tateLevelCombination, smul_sum_nsmul_seq_succ E fun i => (c i).val]
  exact Finset.sum_congr rfl fun i _ => nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq (E i) n)
    (by rw [ZMod.natCast_zmod_val, ZMod.natCast_val])

omit hℓ in
/-- If the first components of `E` span `M[ℓ]`, then the `n`-th components span `M[ℓ^n]`. -/
theorem exists_eq_sum_of_pow_smul_eq_zero {ι : Type*} [Fintype ι] (E : ι → tateModule M ℓ)
    (h1 : ∀ y : M, ℓ • y = 0 → ∃ c : ι → ℕ, y = ∑ i, c i • (E i : ℕ → M) 1) (n : ℕ) :
    ∀ y : M, ℓ ^ n • y = 0 → ∃ c : ι → ℕ, y = ∑ i, c i • (E i : ℕ → M) n := by
  induction n with
  | zero =>
    intro y hy
    exact ⟨0, by simpa using hy⟩
  | succ n ih =>
    intro y hy
    obtain ⟨c, hc⟩ := ih (ℓ • y) (by rw [smul_smul, ← pow_succ, hy])
    have hc' := hc.trans (smul_sum_nsmul_seq_succ E c n).symm
    obtain ⟨d, hd⟩ := h1 (y - ∑ i, c i • (E i : ℕ → M) (n + 1)) (by rw [smul_sub, hc', sub_self])
    refine ⟨fun i => c i + d i * ℓ ^ n, ?_⟩
    rw [← sub_add_cancel y (∑ i, c i • (E i : ℕ → M) (n + 1)), hd, add_comm,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_nsmul, mul_nsmul, ← pow_smul_seq_add (E i) 1 n, add_comm 1 n, smul_comm (d i)]

variable {r : ℕ}

/-- If the first components of `E` span `M[ℓ]` and `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`, then
`c ↦ ∑ i, c i • (E i) n` is a bijection `(ℤ/ℓ^n)^r → M[ℓ^n]`. -/
theorem tateLevelCombination_bijective {E : Fin r → tateModule M ℓ}
    (h1 : ∀ y : M, ℓ • y = 0 → ∃ c : Fin r → ℕ, y = ∑ i, c i • (E i : ℕ → M) 1) (n : ℕ)
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    Function.Bijective (fun c : Fin r → ZMod (ℓ ^ n) =>
      (⟨tateLevelCombination E n c, AddSubgroup.torsionBy.nsmul_iff.2
        (pow_smul_tateLevelCombination E n c)⟩ : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ))) := by
  refine Function.Surjective.bijective_of_nat_card_le ?_ (Nat.card_congr e.toEquiv).ge
  rintro ⟨y, hy⟩
  obtain ⟨c, hc⟩ :=
    exists_eq_sum_of_pow_smul_eq_zero E h1 n y (AddSubgroup.torsionBy.nsmul_iff.1 hy)
  refine ⟨fun i => (c i : ZMod (ℓ ^ n)), Subtype.ext ?_⟩
  change ∑ i, ((c i : ZMod (ℓ ^ n))).val • (E i : ℕ → M) n = y
  rw [hc]
  exact Finset.sum_congr rfl fun i _ =>
    nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq (E i) n) (ZMod.natCast_zmod_val _)

/-- If the first components of `E` span `M[ℓ]` and `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`, then
`tateLevelCombination E n` is injective. -/
theorem tateLevelCombination_injective {E : Fin r → tateModule M ℓ}
    (h1 : ∀ y : M, ℓ • y = 0 → ∃ c : Fin r → ℕ, y = ∑ i, c i • (E i : ℕ → M) 1) (n : ℕ)
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    Function.Injective (tateLevelCombination E n) := fun _c _d h =>
  (tateLevelCombination_bijective h1 n e).1 (Subtype.ext h)

/-- A compatible family of residues `c n : ℤ/ℓ^n` comes from an `ℓ`-adic integer. -/
theorem exists_padicInt_toZModPow_eq (c : ∀ n : ℕ, ZMod (ℓ ^ n))
    (hc : ∀ n, ZMod.cast (c (n + 1)) = c n) : ∃ a : ℤ_[ℓ], ∀ n, toZModPow n a = c n := by
  have hi : ∀ k, (ℓ : ℤ) ^ k ∣ ((c (k + 1)).val : ℤ) - ((c k).val : ℤ) := by
    intro k
    have h := hc k
    rw [← ZMod.natCast_val, ← ZMod.natCast_zmod_val (c k)] at h
    have h' : (((c k).val : ℤ) : ZMod (ℓ ^ k)) = (((c (k + 1)).val : ℤ) : ZMod (ℓ ^ k)) := by
      simpa only [Int.cast_natCast] using h.symm
    simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h'
  refine ⟨PadicInt.ofIntSeq _ (isCauSeq_padicNorm_of_pow_dvd_sub (fun k => ((c k).val : ℤ)) ℓ hi),
    fun n => ?_⟩
  rw [toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => ((c k).val : ℤ)) ℓ hi n, Int.cast_natCast,
    ZMod.natCast_zmod_val]

/-- If the first components of `E` reduce to the standard basis of `M[ℓ] ≅ (ℤ/ℓ)^r`, they span
`M[ℓ]`. -/
private theorem exists_eq_sum_seq_one_of_tateReduction_eq {E : Fin r → tateModule M ℓ}
    (e₁ : AddSubgroup.torsionBy M ((ℓ ^ 1 : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ 1)))
    (hE : ∀ i, tateReduction ℓ 1 (E i) = e₁.symm (Pi.single i 1)) :
    ∀ y : M, ℓ • y = 0 → ∃ c : Fin r → ℕ, y = ∑ i, c i • (E i : ℕ → M) 1 := by
  intro y hy
  have hy' : y ∈ AddSubgroup.torsionBy M ((ℓ ^ 1 : ℕ) : ℤ) :=
    AddSubgroup.torsionBy.nsmul_iff.2 (by rwa [pow_one])
  refine ⟨fun i => (e₁ ⟨y, hy'⟩ i).val, ?_⟩
  have hv : e₁ ⟨y, hy'⟩ = ∑ i, (e₁ ⟨y, hy'⟩ i).val • Pi.single i (1 : ZMod (ℓ ^ 1)) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j
      (fun i _ hij => by rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have := congrArg (fun v => ((e₁.symm v : AddSubgroup.torsionBy M _) : M)) hv
  simp only [AddEquiv.symm_apply_apply, map_sum, map_nsmul] at this
  refine this.trans ?_
  simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_nsmul, ← hE, coe_tateReduction]

/-- **The Tate module is free.** Let `M` be an `ℓ`-divisible abelian group with
`M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n`. Then `T_ℓ M ≅ ℤ_ℓ^r`. -/
theorem nonempty_linearEquiv_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Nonempty (tateModule M ℓ ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) := by
  classical
  obtain ⟨e₁⟩ := htors 1
  choose E hE using fun i : Fin r =>
    tateReduction_surjective hdiv 1 (e₁.symm (Pi.single i 1))
  have h1 := exists_eq_sum_seq_one_of_tateReduction_eq e₁ hE
  let Φ := Fintype.linearCombination ℤ_[ℓ] E
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext i
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨e⟩ := htors n
    have h := congrArg (fun x : tateModule M ℓ => (x : ℕ → M) n) ha
    simp only [Φ, seq_linearCombination] at h
    have := tateLevelCombination_injective h1 n e (h.trans (tateLevelCombination_zero E n).symm)
    simpa using congrFun this i
  have hsurj : Function.Surjective Φ := by
    intro x
    have hlev : ∀ n, ∃ c : Fin r → ZMod (ℓ ^ n), tateLevelCombination E n c = (x : ℕ → M) n := by
      intro n
      obtain ⟨e⟩ := htors n
      obtain ⟨c, hc⟩ := (tateLevelCombination_bijective h1 n e).2 (tateReduction ℓ n x)
      exact ⟨c, congrArg Subtype.val hc⟩
    choose c hc using hlev
    have hcompat : ∀ n i, ZMod.cast (c (n + 1) i) = c n i := by
      intro n
      obtain ⟨e⟩ := htors n
      refine congrFun (tateLevelCombination_injective h1 n e ?_)
      rw [tateLevelCombination_cast, hc, hc, smul_seq_succ]
    choose a ha using fun i => exists_padicInt_toZModPow_eq (fun n => c n i) (fun n => hcompat n i)
    refine ⟨a, tateModule_ext fun n => ?_⟩
    simp only [Φ, seq_linearCombination, ha, ← hc n]
  exact ⟨(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

/-- If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n`, then `T_ℓ M` is a free
`ℤ_ℓ`-module. -/
theorem module_free_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.Free ℤ_[ℓ] (tateModule M ℓ) :=
  Module.Free.of_equiv (nonempty_linearEquiv_tateModule hdiv htors).some.symm

/-- If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n`, then `T_ℓ M` is a finitely
generated `ℤ_ℓ`-module. -/
theorem module_finite_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.Finite ℤ_[ℓ] (tateModule M ℓ) :=
  Module.Finite.equiv (nonempty_linearEquiv_tateModule hdiv htors).some.symm

/-- If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n`, then `T_ℓ M` has rank `r` over
`ℤ_ℓ`. -/
theorem finrank_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.finrank ℤ_[ℓ] (tateModule M ℓ) = r := by
  rw [(nonempty_linearEquiv_tateModule hdiv htors).some.finrank_eq, Module.finrank_fin_fun]

end Free

section Trace

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n : ℕ}
  {N : Type*} [AddCommGroup N] [Module (ZMod (ℓ ^ n)) N]

/-- In a `ℤ/ℓ^n`-module, `c • z = c.val • z`. -/
theorem smul_eq_val_nsmul (c : ZMod (ℓ ^ n)) (z : N) : c • z = c.val • z := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ n)), ZMod.natCast_zmod_val]

/-- Transported along `e : M[ℓ^n] ≃+ N`, the reduction of `a • x` is `a mod ℓ^n` times the
reduction of `x`. -/
theorem apply_tateReduction_smul (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N)
    (a : ℤ_[ℓ]) (x : tateModule M ℓ) :
    e (tateReduction ℓ n (a • x)) = toZModPow n a • e (tateReduction ℓ n x) := by
  rw [smul_eq_val_nsmul, ← map_nsmul]
  congr 1

/-- Transported along `e : M[ℓ^n] ≃+ N`, the reduction of `∑ i, a i • b i` is the combination of
the reductions of the `b i` with coefficients `a i` modulo `ℓ^n`. -/
theorem apply_tateReduction_linearCombination {ι : Type*} [Fintype ι]
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) (b : ι → tateModule M ℓ)
    (a : ι → ℤ_[ℓ]) :
    e (tateReduction ℓ n (Fintype.linearCombination ℤ_[ℓ] b a)) =
      Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (tateReduction ℓ n (b i)))
        (fun i => toZModPow n (a i)) := by
  simp only [Fintype.linearCombination_apply, map_sum, apply_tateReduction_smul]

/-- The reductions modulo `ℓ^n` of a `ℤ_ℓ`-basis of `T_ℓ M` (transported along `e`) are linearly
independent over `ℤ/ℓ^n`. -/
private theorem linearCombination_tateReduction_injective {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ_[ℓ] (tateModule M ℓ))
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) :
    Function.Injective
      (Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (tateReduction ℓ n (b i)))) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have hred : tateReduction ℓ n
      (Fintype.linearCombination ℤ_[ℓ] b (fun i => ((c i).val : ℤ_[ℓ]))) = 0 := by
    apply e.injective
    rw [apply_tateReduction_linearCombination, map_zero]
    simpa only [map_natCast, ZMod.natCast_zmod_val] using hc
  obtain ⟨y, -, hy⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ((tateReduction_eq_zero_iff n _).1 hred)
  funext i
  have := congrArg (fun x => b.repr x i) hy
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Fintype.linearCombination_apply,
    Module.Basis.repr_sum_self] at this
  rw [Pi.zero_apply, ← ZMod.natCast_zmod_val (c i), ← map_natCast (toZModPow n), ← this,
    map_mul, toZModPow_pow_self, zero_mul]

/-- If `M` is `ℓ`-divisible, a `ℤ_ℓ`-basis of `T_ℓ M` reduces to a `ℤ/ℓ^n`-basis of `M[ℓ^n]`
(transported along `e`). -/
theorem linearCombination_tateReduction_bijective {ι : Type*} [Fintype ι]
    (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (b : Module.Basis ι ℤ_[ℓ] (tateModule M ℓ))
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) :
    Function.Bijective
      (Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (tateReduction ℓ n (b i)))) := by
  refine ⟨linearCombination_tateReduction_injective b e, fun z => ?_⟩
  obtain ⟨x, hx⟩ := tateReduction_surjective hdiv n (e.symm z)
  refine ⟨fun i => toZModPow n (b.repr x i), ?_⟩
  rw [← apply_tateReduction_linearCombination]
  conv_rhs => rw [← e.apply_symm_apply z, ← hx, ← b.sum_repr x]
  rw [Fintype.linearCombination_apply]

/-- The reduction modulo `ℓ^n` of a `ℤ_ℓ`-basis `b` of `T_ℓ M`, a `ℤ/ℓ^n`-basis of `N ≅ M[ℓ^n]`. -/
def tateReductionBasis {ι : Type*} [Fintype ι] (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (b : Module.Basis ι ℤ_[ℓ] (tateModule M ℓ))
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) : Module.Basis ι (ZMod (ℓ ^ n)) N :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective _ (linearCombination_tateReduction_bijective hdiv b e)).symm

/-- The coordinates in `tateReductionBasis hdiv b e` of the combination of the reductions of the
`b i` with coefficients `c` are `c`. -/
theorem tateReductionBasis_repr_linearCombination {ι : Type*} [Fintype ι]
    (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (b : Module.Basis ι ℤ_[ℓ] (tateModule M ℓ))
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) (c : ι → ZMod (ℓ ^ n)) (i : ι) :
    (tateReductionBasis hdiv b e).repr
        (Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (tateReduction ℓ n (b i))) c) i =
      c i := by
  rw [tateReductionBasis, Module.Basis.ofEquivFun_repr_apply]
  exact congrFun ((LinearEquiv.ofBijective _ _).symm_apply_apply c) i

/-- The `i`-th vector of `tateReductionBasis hdiv b e` is the reduction of `b i`, transported along
`e`. -/
theorem tateReductionBasis_apply {ι : Type*} [Fintype ι]
    (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (b : Module.Basis ι ℤ_[ℓ] (tateModule M ℓ))
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) (i : ι) :
    tateReductionBasis hdiv b e i = e (tateReduction ℓ n (b i)) := by
  classical
  simp only [tateReductionBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply, Fintype.linearCombination_apply_single, one_smul]

/-- **Trace of `T_ℓ f` modulo `ℓ^n`.** Let `M` be `ℓ`-divisible with `T_ℓ M` free of finite rank
over `ℤ_ℓ`, and `f` an endomorphism of `M`. Let `e : M[ℓ^n] ≃+ N` be an isomorphism with a
`ℤ/ℓ^n`-module `N`, and `g` an endomorphism of `N` corresponding to `f` under `e`. Then the trace
of `T_ℓ f`, reduced modulo `ℓ^n`, is the trace of `g` over `ℤ/ℓ^n`. -/
theorem toZModPow_trace_tateModuleMap [Module.Free ℤ_[ℓ] (tateModule M ℓ)]
    [Module.Finite ℤ_[ℓ] (tateModule M ℓ)] (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (f : M →+ M)
    (e : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ N) (g : N →+ N)
    (hg : ∀ x, g (e x) = e (torsionMap f _ x)) :
    toZModPow n (LinearMap.trace ℤ_[ℓ] (tateModule M ℓ) (tateModuleMap ℓ f)) =
      LinearMap.trace (ZMod (ℓ ^ n)) N (g.toZModLinearMap (ℓ ^ n)) := by
  classical
  let b := Module.Free.chooseBasis ℤ_[ℓ] (tateModule M ℓ)
  let B := tateReductionBasis hdiv b e
  rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b, LinearMap.trace_eq_matrix_trace (ZMod (ℓ ^ n)) B,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, LinearMap.toMatrix_apply]
  have hgB : g.toZModLinearMap (ℓ ^ n) (B i) =
      Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (tateReduction ℓ n (b i)))
        (fun j => toZModPow n (b.repr (tateModuleMap ℓ f (b i)) j)) := by
    rw [← apply_tateReduction_linearCombination, Fintype.linearCombination_apply,
      ← Finset.sum_congr rfl fun j _ => rfl, b.sum_repr]
    change g (B i) = _
    rw [tateReductionBasis_apply, hg, ← tateReduction_tateModuleMap]
  rw [hgB, tateReductionBasis_repr_linearCombination]

/-- The trace of `T_ℓ f` modulo `ℓ^n` is the trace of `f` on `M[ℓ^n]` over `ℤ/ℓ^n`. -/
theorem toZModPow_trace_tateModuleMap_torsion [Module.Free ℤ_[ℓ] (tateModule M ℓ)]
    [Module.Finite ℤ_[ℓ] (tateModule M ℓ)] (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (f : M →+ M) :
    letI := AddSubgroup.torsionBy.zmodModule (A := M) (n := ℓ ^ n)
    toZModPow n (LinearMap.trace ℤ_[ℓ] (tateModule M ℓ) (tateModuleMap ℓ f)) =
      LinearMap.trace (ZMod (ℓ ^ n)) _ ((torsionMap f ((ℓ ^ n : ℕ) : ℤ)).toZModLinearMap (ℓ ^ n)) :=
  let := AddSubgroup.torsionBy.zmodModule (A := M) (n := ℓ ^ n)
  toZModPow_trace_tateModuleMap hdiv f (AddEquiv.refl _) _ fun _ => rfl

end Trace

end Stacks.AbelianGroup

end
