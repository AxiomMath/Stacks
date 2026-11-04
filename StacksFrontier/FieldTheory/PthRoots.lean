module

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
public import Mathlib.FieldTheory.Relrank
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Derivation.MapPowChar

/-!
# Adjoining `p`-th roots of elements with linearly independent differentials

Let `k` be a field of characteristic `p > 0`, that is, an `𝔽_p = ZMod p`-algebra, and let
`a : ι → k` be a finite family of elements whose differentials `d aᵢ` are `k`-linearly independent
in `Ω[k⁄ZMod p]`. If `b : ι → K` is a family of `p`-th roots of the `aᵢ` in an extension field
`K/k`, then `[k(bᵢ : i) : k] = p ^ #ι`. Such a family `b` is unique, Frobenius being injective in
characteristic `p`, so `IntermediateField.adjoin k (Set.range b)` is the field
`k(a_1^{1/p}, …, a_n^{1/p})`.

## Main results

* `Stacks.FieldTheory.PthRootDegree.solution`: if the `d aᵢ` are linearly independent in
  `Ω[k⁄ZMod p]` and `bᵢ ^ p = aᵢ` in an extension `K/k`, then `[k(bᵢ : i) : k] = p ^ #ι`.
* `IntermediateField.finrank_adjoin_eq_pow_of_linearIndependent_D`: the same statement.

## References

* [StacksProject 07DZ](https://stacks.math.columbia.edu/tag/07DZ)
-/

@[expose] public section

@[expose] public section

namespace Stacks.FieldTheory.PthRootDegree

open Module Polynomial
open scoped IntermediateField

/-- `F(S ∪ {x}) = F(x)` whenever `S ⊆ F`. -/
private lemma adjoin_insert_of_subset_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    {S : Set E} (hS : S ⊆ (⊥ : IntermediateField F E)) (x : E) :
    IntermediateField.adjoin F (insert x S) = F⟮x⟯ := by
  rw [Set.insert_eq, IntermediateField.adjoin_union,
    IntermediateField.adjoin_eq_bot_iff.2 hS, sup_bot_eq]

/-- The tower law for adjoining one more element:
`[k(S ∪ {x}) : k] = [k(S) : k] * [k(S)(x) : k(S)]`, with no finiteness hypothesis. -/
private lemma finrank_adjoin_insert {k K : Type*} [Field k] [Field K] [Algebra k K] (S : Set K)
    (x : K) :
    finrank k (IntermediateField.adjoin k (insert x S))
      = finrank k (IntermediateField.adjoin k S)
        * finrank (IntermediateField.adjoin k S) (IntermediateField.adjoin k S)⟮x⟯ := by
  have hle : IntermediateField.adjoin k S ≤ IntermediateField.adjoin k (insert x S) :=
    IntermediateField.adjoin.mono k _ _ (Set.subset_insert _ _)
  rw [← IntermediateField.finrank_bot_mul_relfinrank hle,
    IntermediateField.relfinrank_eq_finrank_of_le hle,
    IntermediateField.extendScalars_adjoin hle,
    adjoin_insert_of_subset_bot (fun y hy ↦ ⟨⟨y, IntermediateField.subset_adjoin k S hy⟩, rfl⟩) x]

/-- If `x : K` has `x ^ p = y ∈ F` with `p` prime and `y` not a `p`-th power in `F`, then
`X ^ p - y` is the minimal polynomial of `x` and `[F(x) : F] = p`. -/
private lemma finrank_adjoin_simple_of_pow_eq {F K : Type*} [Field F] [Field K] [Algebra F K]
    {p : ℕ} (hp : p.Prime) (x : K) (y : F) (hxy : x ^ p = algebraMap F K y)
    (hy : ∀ c : F, c ^ p ≠ y) : finrank F F⟮x⟯ = p := by
  have hmonic : (X ^ p - C y).Monic := monic_X_pow_sub_C y hp.ne_zero
  have hroot : Polynomial.aeval x (X ^ p - C y) = 0 := by simp [hxy]
  rw [IntermediateField.adjoin.finrank ⟨_, hmonic, hroot⟩,
    ← minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hp hy) hroot hmonic,
    natDegree_X_pow_sub_C]

/-- Let `k` be a field of characteristic `p > 0`, let `K/k` be an extension and let
`W ⊆ Ω[k⁄𝔽_p]` be a `k`-submodule. The elements of `K` whose `p`-th power lies in `k` and has
differential in `W` form an intermediate field of `K/k`: if every element of `S ⊆ K` has that
property then so does every element of `k(S)`. -/
private lemma exists_pow_eq_and_D_mem {k K : Type*} [Field k] [Field K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) k] [Algebra k K] (W : Submodule k (Ω[k⁄ZMod p])) {S : Set K}
    (hS : ∀ x ∈ S, ∃ y : k, x ^ p = algebraMap k K y ∧ KaehlerDifferential.D (ZMod p) k y ∈ W)
    {c : K} (hc : c ∈ IntermediateField.adjoin k S) :
    ∃ y : k, c ^ p = algebraMap k K y ∧ KaehlerDifferential.D (ZMod p) k y ∈ W := by
  have : CharP k p := charP_of_injective_algebraMap (algebraMap (ZMod p) k).injective p
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : ExpChar K p := .prime Fact.out
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap x =>
      exact ⟨x ^ p, by rw [map_pow], by rw [Derivation.map_pow_char_eq_zero]; exact W.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨u, hu, hu'⟩ := hx
      obtain ⟨v, hv, hv'⟩ := hy
      exact ⟨u + v, by rw [add_pow_char, hu, hv, map_add], by
        rw [map_add]; exact W.add_mem hu' hv'⟩
  | inv x _ hx =>
      obtain ⟨u, hu, hu'⟩ := hx
      exact ⟨u⁻¹, by rw [map_inv₀, ← hu, inv_pow], by
        rw [Derivation.leibniz_inv]; exact W.smul_mem _ hu'⟩
  | mul x y _ _ hx hy =>
      obtain ⟨u, hu, hu'⟩ := hx
      obtain ⟨v, hv, hv'⟩ := hy
      exact ⟨u * v, by rw [mul_pow, hu, hv, map_mul], by
        rw [Derivation.leibniz]; exact W.add_mem (W.smul_mem _ hv') (W.smul_mem _ hu')⟩

/-- If `d (a j)` does not lie in the span of the `d (a i)` for `i ∈ s`, then `a j` is not a `p`-th
power in `k(bᵢ : i ∈ s)`, the `bᵢ` being `p`-th roots of the `aᵢ`. -/
private lemma pow_ne_algebraMap_of_D_notMem_span {k K : Type*} [Field k] [Field K] (p : ℕ)
    [Fact p.Prime] [Algebra (ZMod p) k] [Algebra k K] {ι : Type*} (a : ι → k) (b : ι → K)
    (hb : ∀ i, b i ^ p = algebraMap k K (a i)) {s : Set ι} {j : ι}
    (hj : KaehlerDifferential.D (ZMod p) k (a j) ∉
      Submodule.span k ((fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) '' s))
    (c : IntermediateField.adjoin k (b '' s)) :
    c ^ p ≠ algebraMap k (IntermediateField.adjoin k (b '' s)) (a j) := fun hc ↦ by
  have hcK : (c : K) ^ p = algebraMap k K (a j) := by
    rw [← IntermediateField.algebraMap_apply, ← map_pow, hc, ← IsScalarTower.algebraMap_apply]
  obtain ⟨y, hy, hy'⟩ := exists_pow_eq_and_D_mem p
    (Submodule.span k ((fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) '' s))
    (fun x hx ↦ by
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨a i, hb i, Submodule.subset_span (Set.mem_image_of_mem _ hi)⟩) c.2
  exact hj ((algebraMap k K).injective (hy.symm.trans hcK) ▸ hy')

/-- If the `d aᵢ` are linearly independent and `bᵢ ^ p = aᵢ`, then for every finite subset `s` of
the index type, `[k(bᵢ : i ∈ s) : k] = p ^ #s`. -/
private lemma finrank_adjoin_image_eq_pow {k K : Type*} [Field k] [Field K] (p : ℕ)
    [Fact p.Prime] [Algebra (ZMod p) k] [Algebra k K] {ι : Type*} (a : ι → k) (b : ι → K)
    (hb : ∀ i, b i ^ p = algebraMap k K (a i))
    (h : LinearIndependent k fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) (s : Finset ι) :
    finrank k (IntermediateField.adjoin k (b '' (s : Set ι))) = p ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, finrank_adjoin_insert, ih,
      finrank_adjoin_simple_of_pow_eq Fact.out (b j) _
        (by rw [← IsScalarTower.algebraMap_apply, hb])
        (pow_ne_algebraMap_of_D_notMem_span p a b hb
          (h.notMem_span_image (s := (s : Set ι)) (by simpa using hj))),
      Finset.card_insert_of_notMem hj, pow_succ]

/-- Let `k` be a field of characteristic `p > 0` and let `a : ι → k` be a finite family such that
the differentials `d aᵢ` are linearly independent in `Ω[k⁄𝔽_p]`. If `b : ι → K` is a family of
`p`-th roots of the `aᵢ` in an extension field `K/k`, then `[k(bᵢ : i) : k] = p ^ #ι`. -/
public theorem solution {k K : Type*}
    [Field k] [Field K] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [Algebra k K] {ι : Type*}
    [Fintype ι] (a : ι → k) (b : ι → K) (hb : ∀ i, b i ^ p = algebraMap k K (a i))
    (h : LinearIndependent k fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) :
    Module.finrank k (IntermediateField.adjoin k (Set.range b)) = p ^ Fintype.card ι := by
  have := finrank_adjoin_image_eq_pow p a b hb h Finset.univ
  rwa [Finset.coe_univ, Set.image_univ, Finset.card_univ] at this

end Stacks.FieldTheory.PthRootDegree

end

@[expose] public section

/-- **Adjoining `p`-th roots of elements with independent differentials.** Let `k` be a field of
characteristic `p > 0` and let `a : ι → k` be a finite family such that the differentials `d aᵢ`
are linearly independent in `Ω[k⁄𝔽_p]`. If `b : ι → K` is a family of `p`-th roots of the `aᵢ` in
an extension field `K/k`, then the field extension `k(a_1^{1/p}, …, a_n^{1/p}) = k(bᵢ : i)` has
degree `p ^ #ι` over `k`. -/
@[stacks 07DZ "The source's `Ω_{k/𝔽_p}` is `Ω[k⁄ZMod p]`, characteristic `p > 0` is
`[Fact p.Prime] [Algebra (ZMod p) k]`, and `k(a_1^{1/p}, …, a_n^{1/p})` is
`IntermediateField.adjoin k (Set.range b)` for a family `b` of `p`-th roots in an ambient extension
`K/k`, which is unique since Frobenius is injective. See the module docstring."]
public theorem IntermediateField.finrank_adjoin_eq_pow_of_linearIndependent_D {k K : Type*}
    [Field k] [Field K] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [Algebra k K] {ι : Type*}
    [Fintype ι] (a : ι → k) (b : ι → K) (hb : ∀ i, b i ^ p = algebraMap k K (a i))
    (h : LinearIndependent k fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) :
    Module.finrank k (IntermediateField.adjoin k (Set.range b)) = p ^ Fintype.card ι :=
  Stacks.FieldTheory.PthRootDegree.solution p a b hb h

end
