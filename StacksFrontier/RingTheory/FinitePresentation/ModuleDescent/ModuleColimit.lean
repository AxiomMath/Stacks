module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits and maps of finite presentation: the module colimit condition

Let `A` be a commutative ring and `M, N` be `A`-modules. Suppose
`R = colim_{i ∈ I} R_i` is a directed colimit of `A`-algebras, where `(I, ≤)`
is a directed poset and `i ↦ R_i` is a functor to `A`-algebras with transition
maps `φ_{ij} : R_i → R_j` for `i ≤ j` and canonical maps `φ_i : R_i → R`.

The key tool is that tensoring a fixed `A`-module `P` with the family commutes
with directed colimits:  `P ⊗_A R = colim_i (P ⊗_A R_i)` as `R`-modules. This file sets up
the directed system, the canonical maps `R_i ⊗_A P → R ⊗_A P` and the statement
`IsModuleColimit` of this colimit property.

## Main results

* `statement_one`: if `M` is finite and `u, u' : M → N` agree after base change to `R`,
  they already agree after base change to some `R_i`.
* `baseChange_surjective_iff_coker_subsingleton`: a base change of `u : M → N` is surjective
  iff the base change of its cokernel vanishes.

## Conventions

All rings are commutative with unit; all algebra maps are unital `A`-algebra
homomorphisms.  We use Mathlib's base change `S ⊗[A] M` (the algebra on the left), which
is canonically isomorphic to `M ⊗_A S`.
-/

@[expose] public section

universe u v

@[expose] public section


open scoped TensorProduct

namespace Stacks.FinitePresentation.ColimitDescent

section Setup

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]

/-- The transition `A`-algebra maps `φ_{ij} : R_i → R_j` of the directed
system, together with the functoriality laws `φ_{ii} = id` and
`φ_{jk} ∘ φ_{ij} = φ_{ik}`. -/
structure TransitionSystem
    (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j) : Prop where
  refl : ∀ (i : ι) (x : R i), φ (le_refl i) x = x
  trans : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : R i),
    φ hjk (φ hij x) = φ (le_trans hij hjk) x

/-- Compatibility of the canonical maps `φ_i : R_i → R` with the transition
maps: `φ_j ∘ φ_{ij} = φ_i` for `i ≤ j`. -/
def IsCoconeAlg (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (ψ : ∀ i, R i →ₐ[A] S) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : i ≤ j) (x : R i), ψ j (φ hij x) = ψ i x

/-- The canonical `A`-linear map `R_i ⊗_A P → S ⊗_A P` induced by the algebra
map `ψ i : R_i → S` (i.e. `(ψ i) ⊗ id_P`). -/
noncomputable def canonMod (ψ : ∀ i, R i →ₐ[A] S)
    (P : Type*) [AddCommGroup P] [Module A P] (i : ι) :
    (R i) ⊗[A] P →ₗ[A] S ⊗[A] P :=
  TensorProduct.map (ψ i).toLinearMap LinearMap.id

/-- The transition `A`-linear map `R_i ⊗_A P → R_j ⊗_A P` induced by
`φ_{ij} : R_i → R_j` (i.e. `φ_{ij} ⊗ id_P`). -/
noncomputable def transMod (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (P : Type*) [AddCommGroup P] [Module A P] ⦃i j : ι⦄ (hij : i ≤ j) :
    (R i) ⊗[A] P →ₗ[A] (R j) ⊗[A] P :=
  TensorProduct.map (φ hij).toLinearMap LinearMap.id

section MovedHelpers

variable {P : Type*} [AddCommGroup P] [Module A P]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

omit [Preorder ι] in
omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `canonMod ψ P i` sends `r ⊗ p` to `ψ i r ⊗ p`. -/
@[simp] lemma canonMod_tmul (ψ : ∀ i, R i →ₐ[A] S) (i : ι) (r : R i) (p : P) :
    canonMod ψ P i (r ⊗ₜ[A] p) = (ψ i r) ⊗ₜ[A] p := rfl

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `transMod φ P hij` sends `r ⊗ p` to `φ hij r ⊗ p`. -/
@[simp] lemma transMod_tmul (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    ⦃i j : ι⦄ (hij : i ≤ j) (r : R i) (p : P) :
    transMod φ P hij (r ⊗ₜ[A] p) = (φ hij r) ⊗ₜ[A] p := rfl

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- The transition map fixes elements `1 ⊗ p`. -/
lemma transMod_one_tmul (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    ⦃i j : ι⦄ (hij : i ≤ j) (p : P) :
    transMod φ P hij ((1 : R i) ⊗ₜ[A] p) = (1 : R j) ⊗ₜ[A] p := by
  simp [transMod_tmul]

omit [AddCommGroup P] [Module A P] in
/-- A base change `1 ⊗ p`-equality, transported from `i` to a common `j` over a
finite set, via induction. -/
lemma exists_forall_one_tmul_eq
    (Q : ι → P → Prop)
    (hmono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ p, Q i p → Q j p)
    (s : Finset P) (hs : ∀ p ∈ s, ∃ i, Q i p) :
    ∃ j, ∀ p ∈ s, Q j p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | @insert a t ha ih =>
      obtain ⟨ja, hja⟩ := hs a (Finset.mem_insert_self a t)
      obtain ⟨jt, hjt⟩ := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
      obtain ⟨k, hak, htk⟩ := directed_of (· ≤ ·) ja jt
      refine ⟨k, fun p hp => ?_⟩
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hmono hak _ hja
      · exact hmono htk _ (hjt p hp)

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- Monotonicity: `1 ⊗ p = 1 ⊗ q` at level `i` propagates to any `j ≥ i`. -/
lemma one_tmul_eq_of_le
    (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j) {i j : ι} (hij : i ≤ j) {p q : P}
    (h : (1 : R i) ⊗ₜ[A] p = (1 : R i) ⊗ₜ[A] q) :
    (1 : R j) ⊗ₜ[A] p = (1 : R j) ⊗ₜ[A] q := by
  have := congrArg (transMod φ P hij) h
  rwa [transMod_one_tmul, transMod_one_tmul] at this

omit [Preorder ι] in
omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- Naturality of `canonMod` with respect to a base-changed map. -/
lemma canonMod_baseChange (ψ : ∀ i, R i →ₐ[A] S) (u : M →ₗ[A] N) (i : ι)
    (y : (R i) ⊗[A] M) :
    canonMod ψ N i ((LinearMap.baseChange (R i) u) y)
      = (LinearMap.baseChange S u) (canonMod ψ M i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp [canonMod_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- Naturality of `transMod` with respect to a base-changed map. -/
lemma transMod_baseChange (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (u : M →ₗ[A] N) ⦃i j : ι⦄ (hij : i ≤ j) (y : (R i) ⊗[A] M) :
    transMod φ N hij ((LinearMap.baseChange (R i) u) y)
      = (LinearMap.baseChange (R j) u) (transMod φ M hij y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp [transMod_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

end MovedHelpers

/-- The statement that `S ⊗_A P = colim_i (R_i ⊗_A P)`: the canonical maps
`canonMod` are jointly surjective, and two
elements of `R_i ⊗_A P` have the same image in `S ⊗_A P` iff they agree in
`R_j ⊗_A P` for some `j ≥ i`.  This is the conclusion of "tensor product
commutes with directed colimits" applied to the module `P`. -/
structure IsModuleColimit (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (ψ : ∀ i, R i →ₐ[A] S)
    (P : Type*) [AddCommGroup P] [Module A P] : Prop where
  /-- Joint surjectivity: every element of `S ⊗_A P` comes from some `R_i ⊗_A P`. -/
  jointly_surjective : ∀ x : S ⊗[A] P, ∃ (i : ι) (y : (R i) ⊗[A] P),
    canonMod ψ P i y = x
  /-- Equalizer condition: elements of `R_i ⊗_A P` mapping to the same element of
  `S ⊗_A P` already agree in `R_j ⊗_A P` for some `j ≥ i`. -/
  exists_eq_of_canonMod_eq : ∀ (i : ι) (y z : (R i) ⊗[A] P),
    canonMod ψ P i y = canonMod ψ P i z →
    ∃ (j : ι) (hij : i ≤ j), transMod φ P hij y = transMod φ P hij z

end Setup

section Statements

variable {A : Type*} [CommRing A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]
variable (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
variable (ψ : ∀ i, R i →ₐ[A] S)

/-- **Statement (1).** If `M` is a finite `A`-module and `u, u' : M → N` are
`A`-module maps whose base changes to `R` agree, then their base changes to some
`R_i` already agree. -/
@[stacks 05LI "(1)"]
theorem statement_one
    (hcolimN : IsModuleColimit φ ψ N)
    (hM : Module.Finite A M)
    (u u' : M →ₗ[A] N)
    (h : LinearMap.baseChange S u = LinearMap.baseChange S u') :
    ∃ i : ι, LinearMap.baseChange (R i) u = LinearMap.baseChange (R i) u' := by
  classical
  -- For each `m`, `1 ⊗ u m = 1 ⊗ u' m` in `S ⊗ N`.
  have hS : ∀ m : M, (1 : S) ⊗ₜ[A] u m = (1 : S) ⊗ₜ[A] u' m := by
    intro m
    have := congrArg (fun f => f ((1 : S) ⊗ₜ[A] m)) h
    simpa using this
  -- Define the predicate `Q i m : 1 ⊗ u m = 1 ⊗ u' m in R i ⊗ N`.
  set Q : ι → M → Prop := fun i m => (1 : R i) ⊗ₜ[A] u m = (1 : R i) ⊗ₜ[A] u' m
    with hQ
  have hmono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ m, Q i m → Q j m := by
    intro i j hij m hm
    exact one_tmul_eq_of_le φ hij hm
  -- finite generating set of M
  obtain ⟨s, hspan⟩ := hM.fg_top
  have hsgood : ∀ m ∈ s, ∃ i, Q i m := by
    intro m _
    -- inline `exists_one_tmul_eq` for `p := u m`, `q := u' m`
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hcm : canonMod ψ N i₀ ((1 : R i₀) ⊗ₜ[A] u m)
        = canonMod ψ N i₀ ((1 : R i₀) ⊗ₜ[A] u' m) := by
      simp only [canonMod_tmul, map_one]
      exact hS m
    obtain ⟨j, hij, hj⟩ := hcolimN.exists_eq_of_canonMod_eq i₀ _ _ hcm
    rw [transMod_one_tmul, transMod_one_tmul] at hj
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := exists_forall_one_tmul_eq Q hmono s hsgood
  -- Now `Q j m` holds for all `m` in the span = ⊤, hence all `m`.
  have hjall : ∀ m : M, Q j m := by
    intro m
    have hmem : m ∈ Submodule.span A (s : Set M) := by rw [hspan]; exact Submodule.mem_top
    induction hmem using Submodule.span_induction with
    | mem x hx => exact hj x hx
    | zero => simp [hQ]
    | add x y _ _ hx hy =>
        simp only [hQ] at hx hy ⊢
        rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.tmul_add, hx, hy]
    | smul a x _ hx =>
        simp only [hQ] at hx ⊢
        rw [map_smul, map_smul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, hx]
  refine ⟨j, ?_⟩
  -- baseChange equal: check on r ⊗ m
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro r m
  change LinearMap.baseChange (R j) u (r ⊗ₜ[A] m)
      = LinearMap.baseChange (R j) u' (r ⊗ₜ[A] m)
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
  have := hjall m
  simp only [hQ] at this
  have key : ∀ n : N, r ⊗ₜ[A] n = r • ((1 : R j) ⊗ₜ[A] n) := fun n => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [key, key, this]

/-- **Reduction lemma for (2).** For any `A`-algebra `T`, the base change
`LinearMap.baseChange T u : T ⊗ M → T ⊗ N` is surjective iff `T ⊗ (coker u)`
vanishes (is a subsingleton).  This is right-exactness of tensor product applied
to `M → N → coker u → 0`. -/
lemma baseChange_surjective_iff_coker_subsingleton
    {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (T : Type*) [CommRing T] [Algebra A T]
    (u : M →ₗ[A] N) :
    Function.Surjective (LinearMap.baseChange T u) ↔
      Subsingleton (T ⊗[A] (N ⧸ LinearMap.range u)) := by
  set C := N ⧸ LinearMap.range u
  set q : N →ₗ[A] C := (LinearMap.range u).mkQ
  have hqsurj : Function.Surjective (LinearMap.baseChange T q) :=
    LinearMap.baseChange_surjective T (Submodule.mkQ_surjective _)
  have hex : Function.Exact u q := LinearMap.exact_map_mkQ_range u
  have hexT : Function.Exact (LinearMap.baseChange T u) (LinearMap.baseChange T q) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact T hex (Submodule.mkQ_surjective _)
  have hkey : Function.Surjective (LinearMap.baseChange T u) ↔ LinearMap.baseChange T q = 0 :=
    ⟨fun hu => LinearMap.ext fun w => (hexT w).mpr (hu w),
      fun h0 z => (hexT z).mp (by rw [h0]; rfl)⟩
  rw [hkey]
  refine ⟨fun h0 => ⟨fun a b => ?_⟩, fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  obtain ⟨x, rfl⟩ := hqsurj a
  obtain ⟨y, rfl⟩ := hqsurj b
  simp [h0]

end Statements

end Stacks.FinitePresentation.ColimitDescent
