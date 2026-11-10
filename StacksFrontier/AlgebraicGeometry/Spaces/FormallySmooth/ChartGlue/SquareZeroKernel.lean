module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Tactic.LinearCombination

/-!
# The kernel of a square-zero surjection is a module over the quotient

Let `π : C → D` be a surjective ring map whose kernel `J` has square zero. Then `J` is a
`D`-module: `d • j = c • j` for any `c` with `π c = d`, which is independent of the choice of `c`
because the difference of two choices lies in `J` and `J² = 0`. The `C`-module structure of `J` is
the restriction of this one along `π`.

## Main definitions

* `Stacks.ChartGlue.sqZeroModule`: the `D`-module structure on `J`.

## Main results

* `Stacks.ChartGlue.sqZero_smul_eq`: `π c • j = c • j`.
* `Stacks.ChartGlue.sqZero_isScalarTower`: the two module structures are compatible.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.ChartGlue

variable {C : Type u} {D : Type v} [CommRing C] [CommRing D] {F : Type*} [FunLike F C D]
  [RingHomClass F C D] (π : F)
  (hπ : Function.Surjective π) (hJ : RingHom.ker π ^ 2 = ⊥)

include hJ in
/-- The product of two elements of a square-zero kernel is zero. -/
lemma sqZero_mul_eq_zero {a b : C} (ha : a ∈ RingHom.ker π) (hb : b ∈ RingHom.ker π) :
    a * b = 0 := by
  rw [← Ideal.mem_bot, ← hJ, pow_two]
  exact Ideal.mul_mem_mul ha hb

include hJ in
/-- Two elements of `C` with the same image under `π` act in the same way on the square-zero
kernel. -/
lemma sqZero_smul_congr {c c' : C} (h : π c = π c') (j : RingHom.ker π) : c • j = c' • j := by
  apply Subtype.ext
  have hcc : c - c' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, h, sub_self]
  have := sqZero_mul_eq_zero π hJ hcc j.2
  simp only [Submodule.coe_smul, smul_eq_mul]
  linear_combination this

include hπ hJ in
/-- **The `D`-module structure on the kernel of a square-zero surjection `C → D`.** -/
abbrev sqZeroModule : Module D (RingHom.ker π) where
  smul d j := Function.surjInv hπ d • j
  one_smul j := by
    change Function.surjInv hπ 1 • j = j
    rw [sqZero_smul_congr π hJ (c' := 1) (by rw [Function.surjInv_eq hπ, map_one]), one_smul]
  mul_smul d d' j := by
    change Function.surjInv hπ (d * d') • j = Function.surjInv hπ d • Function.surjInv hπ d' • j
    rw [← mul_smul]
    exact sqZero_smul_congr π hJ (by rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ,
      Function.surjInv_eq hπ]) j
  smul_zero d := smul_zero (Function.surjInv hπ d)
  smul_add d j j' := smul_add (Function.surjInv hπ d) j j'
  add_smul d d' j := by
    change Function.surjInv hπ (d + d') • j = Function.surjInv hπ d • j + Function.surjInv hπ d' • j
    rw [← add_smul]
    exact sqZero_smul_congr π hJ (by rw [map_add, Function.surjInv_eq hπ, Function.surjInv_eq hπ,
      Function.surjInv_eq hπ]) j
  zero_smul j := by
    change Function.surjInv hπ 0 • j = 0
    rw [sqZero_smul_congr π hJ (c' := 0) (by rw [Function.surjInv_eq hπ, map_zero]), zero_smul]

include hπ hJ in
/-- Under `sqZeroModule`, `π c` acts on the kernel as `c` does. -/
lemma sqZero_smul_eq (c : C) (j : RingHom.ker π) :
    (letI := sqZeroModule π hπ hJ; π c • j) = c • j :=
  sqZero_smul_congr π hJ (Function.surjInv_eq hπ (π c)) j

include hπ hJ in
/-- The `C`-module structure on the kernel is the restriction of the `D`-module structure. -/
lemma sqZero_isScalarTower :
    letI := (π : C →+* D).toAlgebra
    letI := sqZeroModule π hπ hJ
    IsScalarTower C D (RingHom.ker π) := by
  let := (π : C →+* D).toAlgebra
  let := sqZeroModule π hπ hJ
  refine ⟨fun c d j ↦ ?_⟩
  change Function.surjInv hπ ((π : C →+* D) c * d) • j = c • (Function.surjInv hπ d • j)
  rw [← mul_smul]
  exact sqZero_smul_congr π hJ (by
    rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, RingHom.coe_coe]) j

include hπ hJ in
/-- The action of `D` on the kernel, computed through any lift. -/
lemma coe_sqZero_smul {c : C} {d : D} (h : π c = d) (j : RingHom.ker π) :
    ((letI := sqZeroModule π hπ hJ; d • j : RingHom.ker π) : C) = c * j := by
  subst h
  rw [sqZero_smul_eq π hπ hJ c j]
  rfl

end Stacks.ChartGlue

end
