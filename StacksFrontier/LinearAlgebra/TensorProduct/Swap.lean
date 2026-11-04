module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Flat.Domain
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# Eigenspaces of the swap map on `V ⊗ V`

Let `k` be a field and `V` a `k`-vector space of finite dimension `n`. The *swap
map* (twist, braiding, symmetry) is the `k`-linear endomorphism
`σ : V ⊗[k] V → V ⊗[k] V` determined on pure tensors by `σ (v ⊗ w) = w ⊗ v`; it
is `TensorProduct.comm k V V` and satisfies `σ ∘ σ = id`. For `lam : k` the
`lam`-eigenspace of `σ` is `{x | σ x = lam • x}` (`Module.End.eigenspace`); the
`+1`-eigenspace consists of the symmetric tensors and the `-1`-eigenspace of the
antisymmetric ones. An endomorphism is *diagonalizable* when the supremum of its
eigenspaces is the whole space; since eigenspaces for distinct eigenvalues are
always independent, this is equivalent to a basis of eigenvectors existing.

## Main definitions

* `swapMap`, `swapEigenspace`, `IsDiagonalizable`.

## Main results

* `swap_eigenspace_dim`: in characteristic `≠ 2`, `dim E₊₁ = (n² + n)/2` and
  `dim E₋₁ = (n² − n)/2`, and `V ⊗ V = E₊₁ ⊕ E₋₁`
  (`swap_isCompl_eigenspaces`), so `σ` is diagonalizable
  (`swap_isDiagonalizable`).
* `swap_not_isDiagonalizable`: in characteristic `2` with `n ≥ 2`, `σ` is not
  diagonalizable.

The dimension count goes through the antisymmetriser `AWedge : ⋀²V → V ⊗ V`,
`v ∧ w ↦ v ⊗ w − w ⊗ v`, whose range is exactly `E₋₁` and which is injective
because `qWedge ∘ AWedge = 2 • id`; so `E₋₁ ≅ ⋀²V` has dimension
`Nat.choose n 2`. In characteristic `2` the only eigenvalue of `σ` is `1`, and
`σ` is not the identity once `n ≥ 2`.
-/

@[expose] public section

open scoped TensorProduct

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The swap map `σ : V ⊗ V → V ⊗ V`, sending `v ⊗ w` to `w ⊗ v`,
as a `k`-linear endomorphism. This is `TensorProduct.comm k V V`. -/
noncomputable def swapMap (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :
    Module.End k (V ⊗[k] V) :=
  (TensorProduct.comm k V V).toLinearMap

/-- Correctness of `swapMap` on pure tensors: `σ (v ⊗ w) = w ⊗ v`. -/
theorem swapMap_tmul (v w : V) :
    swapMap k V (v ⊗ₜ[k] w) = w ⊗ₜ[k] v := by
  simp [swapMap]

/-- Correctness: `σ ∘ σ = id`. -/
theorem swapMap_comp_swapMap :
    (swapMap k V) ∘ₗ (swapMap k V) = LinearMap.id := by
  ext v w
  simp [swapMap]

/-- The `lam`-eigenspace `{x | σ x = lam • x}` of the swap map, as
`Module.End.eigenspace` of `swapMap`. -/
noncomputable def swapEigenspace (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] (lam : k) : Submodule k (V ⊗[k] V) :=
  (swapMap k V).eigenspace lam

/-- Correctness of `swapEigenspace`: membership is exactly `σ x = λ • x`. -/
theorem mem_swapEigenspace (lam : k) (x : V ⊗[k] V) :
    x ∈ swapEigenspace k V lam ↔ swapMap k V x = lam • x := by
  rw [swapEigenspace, Module.End.mem_eigenspace_iff]

/-- An endomorphism `f` of a (finite-dimensional) vector space is
*diagonalizable* if the supremum of its eigenspaces is the whole space.
Since eigenspaces attached to distinct eigenvalues are always independent
(`Module.End.iSupIndep_eigenspace`), this is equivalent to `W` being the
internal direct sum of the eigenspaces, i.e. to the existence of a basis of
eigenvectors. -/
def IsDiagonalizable {W : Type*} [AddCommGroup W] [Module k W] (f : Module.End k W) : Prop :=
  ⨆ lam, f.eigenspace lam = ⊤

/-- `σ` is an involution at the level of elements: `σ (σ x) = x`. This is the
elementwise version of `swapMap_comp_swapMap` and is the workhorse identity
behind the symmetric/antisymmetric decomposition. -/
theorem swapMap_apply_apply (x : V ⊗[k] V) : swapMap k V (swapMap k V x) = x := by
  have h2 := congrFun (congrArg (DFunLike.coe) (swapMap_comp_swapMap (k := k) (V := V))) x
  simpa using h2

variable [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The `+1`- and `-1`-eigenspaces of `σ` are disjoint when `char k ≠ 2`.

Argument: if `x` lies in both, then `σ x = x` and `σ x = -x`, hence `x = -x`,
i.e. `2 • x = 0`. Since `2 ≠ 0` in `k` and `k` is a field, `smul_eq_zero` forces
`x = 0`. -/
theorem swap_disjoint (hk : (2 : k) ≠ 0) :
    Disjoint (swapEigenspace k V (1 : k)) (swapEigenspace k V (-1 : k)) := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [mem_swapEigenspace, one_smul] at h1
  rw [mem_swapEigenspace, neg_one_smul] at h2
  have hxx : x = -x := h1.symm.trans h2
  have h0 : (2 : k) • x = 0 := by
    rw [two_smul]; nth_rewrite 1 [hxx]; abel
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h hk
  · rw [Submodule.mem_bot]; exact h

omit [FiniteDimensional k V] in
/-- The `+1`- and `-1`-eigenspaces of `σ` span the whole space when `char k ≠ 2`.

Argument: the operators `p₊ = ½(id + σ)` and `p₋ = ½(id − σ)` decompose any `x`
as `x = p₊ x + p₋ x`. Using `σ² = id`, one checks `σ (p₊ x) = p₊ x`
(so `p₊ x ∈ E₊₁`) and `σ (p₋ x) = − p₋ x` (so `p₋ x ∈ E₋₁`). The scalar `½`
exists because `2 ≠ 0`. Hence every `x` lies in `E₊₁ ⊔ E₋₁`. -/
theorem swap_codisjoint (hk : (2 : k) ≠ 0) :
    Codisjoint (swapEigenspace k V (1 : k)) (swapEigenspace k V (-1 : k)) := by
  rw [codisjoint_iff, eq_top_iff]
  intro x _
  set s := swapMap k V x with hs
  have hssx : swapMap k V s = x := swapMap_apply_apply x
  have hap : (2⁻¹ : k) • (x + s) ∈ swapEigenspace k V (1 : k) := by
    rw [mem_swapEigenspace, map_smul, map_add, ← hs, hssx]; module
  have ham : (2⁻¹ : k) • (x - s) ∈ swapEigenspace k V (-1 : k) := by
    rw [mem_swapEigenspace, map_smul, map_sub, ← hs, hssx]; module
  have hsum : x = (2⁻¹ : k) • (x + s) + (2⁻¹ : k) • (x - s) := by
    rw [← smul_add]
    have h2x : (x + s) + (x - s) = (2 : k) • x := by rw [two_smul]; abel
    rw [h2x, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [hsum]
  exact Submodule.add_mem_sup hap ham

omit [FiniteDimensional k V] in
/-- When `char k ≠ 2`, the whole space `V ⊗ V` is the internal direct sum of the
`+1`- and `-1`-eigenspaces of `σ`. -/
theorem swap_isCompl_eigenspaces (hk : (2 : k) ≠ 0) :
    IsCompl (swapEigenspace k V (1 : k)) (swapEigenspace k V (-1 : k)) :=
  ⟨swap_disjoint hk, swap_codisjoint hk⟩

omit [FiniteDimensional k V] in
/-- In characteristic `≠ 2`, the swap map is diagonalizable.

Argument: `eigenspace 1 ⊔ eigenspace (-1) = ⊤` by `swap_isCompl_eigenspaces`,
and this sup is `≤ ⨆ λ, eigenspace λ`; hence the latter is `⊤`. -/
theorem swap_isDiagonalizable (hk : (2 : k) ≠ 0) :
    IsDiagonalizable (swapMap k V) := by
  have hcompl := swap_isCompl_eigenspaces (k := k) (V := V) hk
  rw [IsDiagonalizable, eq_top_iff]
  have h1 : (swapMap k V).eigenspace 1 ≤ ⨆ lam, (swapMap k V).eigenspace lam := le_iSup _ 1
  have h2 : (swapMap k V).eigenspace (-1) ≤ ⨆ lam, (swapMap k V).eigenspace lam := le_iSup _ (-1)
  have hsup : (swapEigenspace k V (1 : k)) ⊔ (swapEigenspace k V (-1 : k)) = ⊤ :=
    hcompl.sup_eq_top
  rw [swapEigenspace, swapEigenspace] at hsup
  rw [← hsup]
  exact sup_le h1 h2

/-- Auxiliary multilinear map `(x : Fin 2 → V) ↦ x 0 ⊗ x 1`, used to build the
antisymmetrising alternating map below. -/
noncomputable def muMap : MultilinearMap k (fun _ : Fin 2 => V) (V ⊗[k] V) where
  toFun x := x 0 ⊗ₜ[k] x 1
  map_update_add' := by
    intro inst x i a b
    fin_cases i
    · simp only [Function.update, Fin.isValue, Fin.zero_eta, ↓reduceDIte,
        one_ne_zero]
      rw [TensorProduct.add_tmul]
    · simp only [Function.update, Fin.isValue, Fin.mk_one, zero_ne_one,
        ↓reduceDIte]
      rw [TensorProduct.tmul_add]
  map_update_smul' := by
    intro inst x i c a
    fin_cases i
    · simp only [Function.update, Fin.isValue, Fin.zero_eta, ↓reduceDIte,
        one_ne_zero]
      rw [TensorProduct.smul_tmul']
    · simp only [Function.update, Fin.isValue, Fin.mk_one, zero_ne_one,
        ↓reduceDIte, TensorProduct.tmul_smul]

/-- The alternating map `⋀²V → V ⊗ V` sending `![v, w] ↦ v ⊗ w − w ⊗ v`. -/
noncomputable def alphaMap : V [⋀^Fin 2]→ₗ[k] (V ⊗[k] V) :=
  AlternatingMap.mk (muMap - muMap.domDomCongr (Equiv.swap (0 : Fin 2) 1))
    (by
      intro v i j hij hne
      change muMap v - muMap (fun x => v (Equiv.swap (0:Fin 2) 1 x)) = 0
      have h01 : v 0 = v 1 := by fin_cases i <;> fin_cases j <;> simp_all
      change v 0 ⊗ₜ[k] v 1 - (v (Equiv.swap (0:Fin 2) 1 0)) ⊗ₜ[k] (v (Equiv.swap (0:Fin 2) 1 1)) = 0
      simp [← h01])

omit [FiniteDimensional k V] in
/-- The alternating map `alphaMap` sends `![v, w]` to `v ⊗ w - w ⊗ v`. -/
theorem alphaMap_apply (v w : V) : alphaMap ![v, w] = v ⊗ₜ[k] w - w ⊗ₜ[k] v := by
  have : (alphaMap : V [⋀^Fin 2]→ₗ[k] (V ⊗[k] V)) ![v, w]
      = muMap ![v,w] - muMap (fun x => ![v,w] (Equiv.swap (0:Fin 2) 1 x)) := rfl
  rw [this]
  show (![v,w] 0) ⊗ₜ[k] (![v,w] 1)
      - (![v,w] (Equiv.swap (0:Fin 2) 1 0)) ⊗ₜ[k] (![v,w] (Equiv.swap (0:Fin 2) 1 1)) = _
  simp

/-- Auxiliary bilinear map `(v, w) ↦ v ∧ w` into the second exterior power. -/
noncomputable def Bwedge : V →ₗ[k] V →ₗ[k] (⋀[k]^2 V) :=
  LinearMap.mk₂ k (fun v w => exteriorPower.ιMulti k 2 ![v, w])
    (fun v v' w => by
      have h := (exteriorPower.ιMulti k 2).map_update_add ![v, w] 0 v v'
      have e0 : Function.update ![v, w] 0 (v + v') = ![v + v', w] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![v, w] 0 v = ![v, w] := by funext i; fin_cases i <;> simp
      have e2 : Function.update ![v, w] 0 v' = ![v', w] := by funext i; fin_cases i <;> simp
      rw [e0, e1, e2] at h; exact h)
    (fun c v w => by
      have h := (exteriorPower.ιMulti k 2).map_update_smul ![v, w] 0 c v
      have e0 : Function.update ![v, w] 0 (c • v) = ![c • v, w] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![v, w] 0 v = ![v, w] := by funext i; fin_cases i <;> simp
      rw [e0, e1] at h; exact h)
    (fun v w w' => by
      have h := (exteriorPower.ιMulti k 2).map_update_add ![v, w] 1 w w'
      have e0 : Function.update ![v, w] 1 (w + w') = ![v, w + w'] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![v, w] 1 w = ![v, w] := by funext i; fin_cases i <;> simp
      have e2 : Function.update ![v, w] 1 w' = ![v, w'] := by funext i; fin_cases i <;> simp
      rw [e0, e1, e2] at h; exact h)
    (fun c v w => by
      have h := (exteriorPower.ιMulti k 2).map_update_smul ![v, w] 1 c w
      have e0 : Function.update ![v, w] 1 (c • w) = ![v, c • w] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![v, w] 1 w = ![v, w] := by funext i; fin_cases i <;> simp
      rw [e0, e1] at h; exact h)

/-- The linear map `q : V ⊗ V → ⋀²V`, `v ⊗ w ↦ v ∧ w`. -/
noncomputable def qWedge : (V ⊗[k] V) →ₗ[k] (⋀[k]^2 V) := TensorProduct.lift Bwedge

omit [FiniteDimensional k V] in
/-- The map `q : V ⊗ V → ⋀²V` sends the pure tensor `v ⊗ w` to `v ∧ w`. -/
theorem qWedge_tmul (v w : V) :
    qWedge (v ⊗ₜ[k] w) = exteriorPower.ιMulti k 2 ![v, w] := by
  simp [qWedge, Bwedge]

/-- The linear map `A : ⋀²V → V ⊗ V`, `v ∧ w ↦ v ⊗ w − w ⊗ v` (antisymmetriser). -/
noncomputable def AWedge : (⋀[k]^2 V) →ₗ[k] (V ⊗[k] V) :=
  exteriorPower.alternatingMapLinearEquiv alphaMap

omit [FiniteDimensional k V] in
/-- The antisymmetriser `A : ⋀²V → V ⊗ V` sends `v ∧ w` to `v ⊗ w - w ⊗ v`. -/
theorem AWedge_ιMulti (v w : V) :
    AWedge (exteriorPower.ιMulti k 2 ![v, w]) = v ⊗ₜ[k] w - w ⊗ₜ[k] v := by
  rw [AWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alphaMap_apply]

omit [FiniteDimensional k V] in
/-- Exchanging the two arguments of `v ∧ w` changes its sign. -/
theorem ιMulti_swap (v w : V) :
    exteriorPower.ιMulti k 2 ![w, v] = - exteriorPower.ιMulti k 2 ![v, w] := by
  have h := (exteriorPower.ιMulti k 2).map_swap ![v, w] (i := 0) (j := 1) (by simp)
  have e : (![v, w] ∘ (Equiv.swap (0:Fin 2) 1)) = ![w, v] := by
    funext i; fin_cases i <;> simp
  rw [e] at h; exact h

/-- A function out of `Fin 2` is the vector built from its two values. -/
private theorem eq_vecCons_fin_two {α : Type*} (a : Fin 2 → α) : a = ![a 0, a 1] := by
  funext i; fin_cases i <;> simp

omit [FiniteDimensional k V] in
/-- The composite `q ∘ A` is multiplication by `2` on `⋀²V`. -/
theorem qWedge_comp_AWedge :
    qWedge ∘ₗ AWedge = (2 : k) • LinearMap.id (R := k) (M := ⋀[k]^2 V) := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span k 2 V)
  rintro _ ⟨a, rfl⟩
  rw [eq_vecCons_fin_two a]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [AWedge_ιMulti, map_sub, qWedge_tmul, qWedge_tmul, ιMulti_swap (a 0) (a 1),
    sub_neg_eq_add, two_smul]

omit [FiniteDimensional k V] in
/-- `A` is injective (since `q ∘ A = 2 • id` and `2 ≠ 0`). -/
theorem AWedge_injective (hk : (2 : k) ≠ 0) :
    Function.Injective (AWedge (k := k) (V := V)) := by
  intro x y hxy
  have h : ∀ z, qWedge (AWedge z) = (2 : k) • z := fun z => by
    simpa using LinearMap.congr_fun (qWedge_comp_AWedge (k := k) (V := V)) z
  exact smul_right_injective _ hk (by simp only [← h, hxy])

omit [FiniteDimensional k V] in
/-- The range of `A` is exactly the `-1`-eigenspace (antisymmetric tensors). -/
theorem range_AWedge (hk : (2 : k) ≠ 0) :
    LinearMap.range (AWedge (k := k) (V := V)) = swapEigenspace k V (-1 : k) := by
  apply le_antisymm
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    rw [← exteriorPower.ιMulti_span k 2 V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [eq_vecCons_fin_two a, SetLike.mem_coe, Submodule.mem_comap,
      mem_swapEigenspace, AWedge_ιMulti]
    rw [map_sub, swapMap_tmul, swapMap_tmul, neg_one_smul, neg_sub]
  · intro x hx
    rw [mem_swapEigenspace, neg_one_smul] at hx
    have hxeq : x = (2⁻¹ : k) • (x - swapMap k V x) := by
      rw [hx, sub_neg_eq_add, ← two_smul k x, smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hP : ∀ y : V ⊗[k] V, y - swapMap k V y ∈ LinearMap.range (AWedge (k := k) (V := V)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v w =>
        rw [swapMap_tmul]
        exact ⟨exteriorPower.ιMulti k 2 ![v, w], by rw [AWedge_ιMulti]⟩
      | add a b ha hb =>
        have heq : (a + b) - swapMap k V (a + b)
            = (a - swapMap k V a) + (b - swapMap k V b) := by rw [map_add]; abel
        rw [heq]
        exact Submodule.add_mem _ ha hb
    rw [hxeq]
    exact Submodule.smul_mem _ _ (hP x)

/-- The dimension of the `-1`-eigenspace of `σ` (the antisymmetric tensors) is
`(n^2 - n)/2 = C(n,2)`.

Argument: let `(eᵢ)` be a basis of `V`
indexed by `Fin n`, so `(eᵢ ⊗ eⱼ)` is a basis of `V ⊗ V`. In characteristic
`≠ 2`, the antisymmetric tensors `E₋₁` have as a basis the family
`{eᵢ ⊗ eⱼ − eⱼ ⊗ eᵢ : i < j}`, which has `C(n,2) = (n^2 − n)/2` elements.
Equivalently, `E₋₁` is `k`-linearly isomorphic to the second exterior power
`⋀²[k] V`, whose dimension is `Nat.choose n 2` by `exteriorPower.finrank_eq`;
and `Nat.choose n 2 = (n^2 − n)/2`. Concretely: the projection
`p₋ = ½(id − σ)` maps `eᵢ ⊗ eⱼ ↦ ½(eᵢ⊗eⱼ − eⱼ⊗eᵢ)` onto `E₋₁`, the alternating
map `eᵢ ∧ eⱼ ↦ eᵢ⊗eⱼ − eⱼ⊗eᵢ` is a linear iso `⋀²V ≅ E₋₁`, and counting the
`i < j` gives `C(n,2)`. -/
theorem swap_finrank_antisymm
    (hk : (2 : k) ≠ 0) (n : ℕ) (hn : Module.finrank k V = n) :
    Module.finrank k (swapEigenspace k V (-1 : k)) = (n ^ 2 - n) / 2 := by
  -- `E₋₁ = range A ≅ ⋀²V`, and `finrank ⋀²V = C(n,2) = (n²−n)/2`.
  rw [← range_AWedge hk, LinearMap.finrank_range_of_inj (AWedge_injective hk),
    exteriorPower.finrank_eq, hn, Nat.choose_two_right]
  congr 1
  cases n with
  | zero => simp
  | succ m => simp [pow_two, Nat.succ_mul, Nat.mul_succ]

/-- Eigenspace dimensions in characteristic `≠ 2`.
Assume `char k ≠ 2` and `dim_k V = n`. Then the `+1`-eigenspace of the swap
map has dimension `(n^2 + n)/2` and the `-1`-eigenspace has dimension
`(n^2 - n)/2`.

Argument: the `-1`-eigenspace has dimension `(n^2 − n)/2` by
`swap_finrank_antisymm`. Since `E₊₁` and `E₋₁` are complementary
(`swap_isCompl_eigenspaces`), their dimensions add to
`finrank (V ⊗ V) = n * n = n^2` (`Submodule.finrank_add_eq_of_isCompl` and
`Module.finrank_tensorProduct`). The remaining `+1`-dimension is then
`n^2 − (n^2 − n)/2 = (n^2 + n)/2`, a nat-arithmetic identity (both `n^2 ± n`
are even). -/
@[stacks 00M4]
theorem swap_eigenspace_dim
    (hk : (2 : k) ≠ 0) (n : ℕ) (hn : Module.finrank k V = n) :
    Module.finrank k (swapEigenspace k V (1 : k)) = (n ^ 2 + n) / 2 ∧
    Module.finrank k (swapEigenspace k V (-1 : k)) = (n ^ 2 - n) / 2 := by
  have hminus : Module.finrank k (swapEigenspace k V (-1 : k)) = (n ^ 2 - n) / 2 :=
    swap_finrank_antisymm hk n hn
  refine ⟨?_, hminus⟩
  -- Sum of dimensions of complementary eigenspaces is finrank (V ⊗ V) = n^2.
  have hsum : Module.finrank k (swapEigenspace k V (1 : k)) +
      Module.finrank k (swapEigenspace k V (-1 : k)) = n ^ 2 := by
    have hc := Submodule.finrank_add_eq_of_isCompl (swap_isCompl_eigenspaces (k := k) (V := V) hk)
    rw [hc]
    rw [Module.finrank_tensorProduct, hn]
    ring
  -- Nat arithmetic: a + b = n^2 and b = (n^2 - n)/2 ⇒ a = (n^2 + n)/2.
  set a := Module.finrank k (swapEigenspace k V (1 : k)) with ha
  have hev : n ≤ n ^ 2 := by nlinarith [Nat.zero_le n, sq_nonneg n]
  have h2 : 2 ∣ (n ^ 2 - n) := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := he; ring_nf; omega
    · obtain ⟨m, rfl⟩ := ho; ring_nf; omega
  omega

omit [FiniteDimensional k V] in
/-- In characteristic `2`, every eigenspace of `σ` is contained in the
`+1`-eigenspace, because `1` is the only eigenvalue.

Argument: if `σ x = λ x` then applying `σ` again (`σ² = id`) gives `λ² x = x`,
i.e. `(λ² − 1) x = 0`. In characteristic `2`, `λ² − 1 = (λ − 1)²`. If `λ ≠ 1`
then `(λ − 1)² ≠ 0` (a field has no zero divisors), forcing `x = 0`. Hence the
`λ`-eigenspace is `{0}` for `λ ≠ 1` and the `1`-eigenspace otherwise. -/
theorem swap_eigenspace_le_one_char2 (hk : (2 : k) = 0) (lam : k) :
    (swapMap k V).eigenspace lam ≤ (swapMap k V).eigenspace 1 := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  by_cases hl : lam = 1
  · subst hl; exact hx
  · have hsq : lam ^ 2 • x = x := by
      have h := swapMap_apply_apply (k := k) (V := V) x
      rw [hx, map_smul, hx, smul_smul] at h
      rw [sq]; exact h
    have hchar : (lam - 1) ^ 2 = lam ^ 2 - 1 := by
      linear_combination (-lam + 1) * hk
    have hfac : (lam - 1) ^ 2 • x = 0 := by
      rw [hchar, sub_smul, hsq, one_smul, sub_self]
    have hne : (lam - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hl)
    have hx0 : x = 0 := by
      rcases smul_eq_zero.mp hfac with h | h
      · exact absurd h hne
      · exact h
    rw [hx0, map_zero, smul_zero]

omit [FiniteDimensional k V] in
/-- The swap map is not the identity when `dim_k V ≥ 2`: there is a tensor `z`
with `σ z ≠ z`.

Argument: from `dim V ≥ 2` (so `rank V > 1`) pick a linearly independent pair
`v, w`. By `LinearIndependent.tmul_of_isDomain`, the four pure tensors
`(eᵢ ⊗ eⱼ)` (with `e = ![v, w]`) are linearly independent, in particular
distinct for distinct index pairs; so `v ⊗ w ≠ w ⊗ v = σ (v ⊗ w)`. -/
theorem swap_ne_id (hn : 2 ≤ Module.finrank k V) :
    ∃ z : V ⊗[k] V, swapMap k V z ≠ z := by
  have hrank : 1 < Module.rank k V := Module.lt_rank_of_lt_finrank (by omega)
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank k V)
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  obtain ⟨w, hvw⟩ := exists_linearIndependent_pair_of_one_lt_rank hrank hv
  refine ⟨v ⊗ₜ[k] w, ?_⟩
  rw [swapMap_tmul]
  have hli : LinearIndependent k
      (fun p : Fin 2 × Fin 2 => (![v, w] p.fst) ⊗ₜ[k] (![v, w] p.snd)) :=
    hvw.tmul_of_isDomain hvw
  intro heq
  have hinj := hli.injective
  have hpair : ((1 : Fin 2), (0 : Fin 2)) = ((0 : Fin 2), (1 : Fin 2)) := by
    apply hinj
    simpa using heq
  simp at hpair

omit [FiniteDimensional k V] in
/-- Non-diagonalizability in characteristic `2`.
Assume `char k = 2` and `dim_k V ≥ 2`. Then the swap map is not
diagonalizable.

Argument: if `σ` were diagonalizable then `⨆ λ, eigenspace λ = ⊤`. But in
characteristic `2` every eigenspace is contained in `eigenspace 1`
(`swap_eigenspace_le_one_char2`), so `⨆ λ, eigenspace λ ≤ eigenspace 1`, whence
`eigenspace 1 = ⊤`, i.e. `σ x = x` for all `x`. This contradicts `swap_ne_id`,
which produces a tensor moved by `σ`. -/
@[stacks 00M4]
theorem swap_not_isDiagonalizable
    (hk : (2 : k) = 0) (hn : 2 ≤ Module.finrank k V) :
    ¬ IsDiagonalizable (swapMap k V) := by
  rw [IsDiagonalizable]
  intro hdiag
  -- ⨆ eigenspace ≤ eigenspace 1
  have hle : (⨆ lam, (swapMap k V).eigenspace lam) ≤ (swapMap k V).eigenspace 1 :=
    iSup_le (fun lam => swap_eigenspace_le_one_char2 hk lam)
  rw [hdiag] at hle
  -- so eigenspace 1 = ⊤
  have htop : (swapMap k V).eigenspace 1 = ⊤ := top_le_iff.mp hle
  -- hence σ x = x for all x
  obtain ⟨z, hz⟩ := swap_ne_id (k := k) (V := V) hn
  apply hz
  have hmem : z ∈ (swapMap k V).eigenspace 1 := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff, one_smul] at hmem
  exact hmem
