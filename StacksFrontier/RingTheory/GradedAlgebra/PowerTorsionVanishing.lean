module

public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.RingTheory.GradedAlgebra.Veronese

/-!
# A graded module whose generators are power-torsion vanishes in large degrees

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring generated over `𝒮 0` by homogeneous elements
`f₁, …, f_r` of degrees `e₁, …, e_r`, and let `M` be a `ℤ`-graded `S`-module. Suppose a family
`y₁, …, y_m` of homogeneous elements of `M`, of degrees `c₁, …, c_m`, is such that each `f_i`
kills each `y_j` after raising it to some power `N_{ij}`. Then every homogeneous element of `M`
that lies in the `S`-span of the `y_j` and whose degree exceeds

`max_j (c_j + ∑_i N_{ij} e_i)`

is zero.

This is the paragraph of [Stacks, Tag 0B5R] beginning "Let `K` be a finite `A`-module such that
`K̃ = 0`", with its two halves separated: the hypothesis here is the power-torsion conclusion that
the vanishing of the associated sheaf produces, and the content is the counting argument that
turns it into vanishing in large degrees. The source states the bound as
`n > max_j (d_j + ∑_i n_{ij} deg(f_i))`, which is exactly the bound above.

The counting is a pigeonhole. A homogeneous element of `S` of degree `k` is an `𝒮 0`-combination
of monomials `∏_i f_i^{a_i}` with `∑_i a_i e_i = k` (`Stacks.Veronese.mem_span_monomials`); if
`k > ∑_i N_{ij} e_i` then no such monomial can have every exponent `a_i` below `N_{ij}`, so each
of them is divisible by some `f_i^{N_{ij}}` and therefore kills `y_j`.

## Why the span hypothesis is on the element, not on the module

The family `y` is *not* required to generate `M`. In the intended application the `y_j` generate
only the Veronese part `M⁽ᵈ⁾ = ⨁_n M_{nd}` over the Veronese subring `S⁽ᵈ⁾`, because that is all
the vanishing of the associated sheaf gives: `M̃ = 0` says the degree-zero part of each
localization `M_{f_i}` vanishes, which bounds only the homogeneous elements whose degree is a
multiple of `deg f_i`. Asking `y` to generate the whole of `M` would be genuinely stronger and is
genuinely unavailable: for `S = k[f]` with `f` of degree `2` and `M = S(1)`, the sheaf `M̃` on
`Proj S` is zero while the generator of `M`, sitting in degree `-1`, is killed by no power of
`f`. Requiring only that the *particular* element lie in the span keeps the statement usable in
both situations.

## Main results

* `Stacks.GradedModule.exists_le_of_sum_mul_lt`: the pigeonhole on exponent vectors.
* `Stacks.GradedModule.smul_eq_zero_of_prod_pow`: a monomial of large enough weighted degree
  kills a power-torsion element.
* `Stacks.GradedModule.smul_eq_zero_of_mem_grade`: every homogeneous scalar of large enough
  degree kills it.
* `Stacks.GradedModule.eq_zero_of_mem_span_of_sum_lt`: the vanishing statement above.

The family `y` is indexed by an arbitrary finite type rather than by `Fin m`: in the application
its index is a sigma type over a `Finset` of module generators and the degrees occurring in their
homogeneous decompositions, and reindexing that to `Fin` would serve no purpose.

## Implementation notes

The first two results mention neither grading, so they are stated outside the graded variable
block: `Stacks.GradedModule.smul_eq_zero_of_prod_pow` is about a commutative ring acting on a
module and a family of elements with their chosen weights, and the weights enter only through the
pigeonhole.

`Stacks.Veronese.mem_span_monomials` is the single input about the graded ring. It is stated with
the span taken over `Stacks.Veronese.gradeZero 𝒮`, so the set of scalars annihilating a fixed
element is met as `Submodule.restrictScalars` of the kernel of `LinearMap.toSpanSingleton`, which
is the shape `Submodule.span_le` consumes.

The degree-`n` component of `c • y` for `y` homogeneous is computed by decomposing `c` rather
than by a general formula: the only term of the decomposition that can contribute is the one
whose degree closes the gap to `n`, and that term is annihilated by the hypothesis.

The `VAdd ℕ ℤ` on degrees is the shared scoped instance
`Stacks.GradedLocalization.instVAddNatInt`, not a file-local copy, so that
`SetLike.GradedSMul 𝒮 𝒨` here is the same class instance the `Proj` files use.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
-/

@[expose] public section

open DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.GradedModule

universe u v w t

/-! ### The pigeonhole -/

/-- **Pigeonhole on exponent vectors.** If the weighted total `∑ i, e i * deg i` of an exponent
vector exceeds that of a bound vector `N`, then some exponent reaches its bound. -/
theorem exists_le_of_sum_mul_lt {r : ℕ} (deg N e : Fin r → ℕ)
    (h : ∑ i, N i * deg i < ∑ i, e i * deg i) : ∃ i, N i ≤ e i := by
  by_contra hcon
  push Not at hcon
  exact absurd (Finset.sum_le_sum fun i _ =>
    Nat.mul_le_mul_right (deg i) (le_of_lt (hcon i))) (not_le.mpr h)

/-! ### A monomial of large weighted degree kills a power-torsion element -/

/-- **A monomial whose weighted degree exceeds `∑ i, N i * deg i` kills `y`.** Some exponent
reaches its bound, so the monomial has `f i ^ N i` as a factor. -/
theorem smul_eq_zero_of_prod_pow {S : Type u} {M : Type v} [CommRing S] [AddCommGroup M]
    [Module S M] {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (y : M)
    (N : Fin r → ℕ) (hN : ∀ i, f i ^ N i • y = 0)
    (e : Fin r → ℕ) (he : ∑ i, N i * deg i < ∑ i, e i * deg i) :
    (∏ i, f i ^ e i) • y = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_le_of_sum_mul_lt deg N e he
  have hsplit : (∏ i, f i ^ e i) =
      (f i₀ ^ (e i₀ - N i₀) * ∏ i ∈ Finset.univ.erase i₀, f i ^ e i) * f i₀ ^ N i₀ := by
    have hpow : f i₀ ^ e i₀ = f i₀ ^ (e i₀ - N i₀) * f i₀ ^ N i₀ := by
      rw [← pow_add, Nat.sub_add_cancel hi₀]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i ^ e i) (Finset.mem_univ i₀), hpow]
    ring
  rw [hsplit, mul_smul, hN i₀, smul_zero]

section Graded

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-! ### Components of a finite sum -/

omit [GradedRing 𝒮] [SetLike.GradedSMul 𝒮 𝒨] in
/-- The degree-`n` component of a finite sum is the sum of the degree-`n` components. -/
theorem coe_decompose_sum {κ : Type*} (s : Finset κ) (g : κ → M) (n : ℤ) :
    ((DirectSum.decompose 𝒨 (∑ i ∈ s, g i) n : 𝒨 n) : M)
      = ∑ i ∈ s, ((DirectSum.decompose 𝒨 (g i) n : 𝒨 n) : M) := by
  rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finsetSum]

/-! ### Every homogeneous scalar of large degree kills a power-torsion element -/

omit [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- **Every homogeneous scalar of degree exceeding `∑ i, N i * deg i` kills `y`.** A homogeneous
element of degree `k` is an `𝒮 0`-combination of monomials of weighted degree `k`
(`Stacks.Veronese.mem_span_monomials`), and each such monomial kills `y`. -/
theorem smul_eq_zero_of_mem_grade {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ)
    (hfdeg : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    (y : M) (N : Fin r → ℕ) (hN : ∀ i, f i ^ N i • y = 0)
    {k : ℕ} (hk : ∑ i, N i * deg i < k) {a : S} (ha : a ∈ 𝒮 k) :
    a • y = 0 := by
  classical
  have hmon : {x : S | ∃ e : Fin r → ℕ, (∑ i, e i * deg i = k) ∧ x = ∏ i, f i ^ e i} ⊆
      ((LinearMap.ker (LinearMap.toSpanSingleton S M y)).restrictScalars
        (Stacks.Veronese.gradeZero 𝒮) : Set S) := by
    rintro x ⟨e, he, rfl⟩
    exact smul_eq_zero_of_prod_pow f deg y N hN e (he ▸ hk)
  exact (Submodule.span_le.mpr hmon)
    (Stacks.Veronese.mem_span_monomials 𝒮 f deg hfdeg hgen k ha)

/-! ### Vanishing in large degrees -/

/-- **A homogeneous element of large degree in the span of power-torsion homogeneous elements is
zero.** This is the counting half of the paragraph of [Stacks, Tag 0B5R] about a finite module
with vanishing associated sheaf: with `y₁, …, y_m` homogeneous of degrees `c₁, …, c_m` and
`f i ^ N i j • y j = 0`, every homogeneous element whose degree exceeds every
`c j + ∑ i, N i j * deg i` and which lies in the `S`-span of the `y j` vanishes.

Decomposing a coefficient of the span expression into homogeneous pieces, the only piece that
contributes to the degree-`n` component of its term is the one of degree `n - c j`, and that
degree is large enough for `Stacks.GradedModule.smul_eq_zero_of_mem_grade` to apply. -/
theorem eq_zero_of_mem_span_of_sum_lt {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ)
    (hfdeg : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {ι : Type*} [Fintype ι] (y : ι → M) (c : ι → ℤ) (hy : ∀ j, y j ∈ 𝒨 (c j))
    (N : Fin r → ι → ℕ) (hN : ∀ i j, f i ^ N i j • y j = 0)
    {n : ℤ} (hn : ∀ j, c j + ((∑ i, N i j * deg i : ℕ) : ℤ) < n)
    {x : M} (hx : x ∈ 𝒨 n) (hspan : x ∈ Submodule.span S (Set.range y)) :
    x = 0 := by
  classical
  obtain ⟨cf, hcf⟩ := Submodule.mem_span_range_iff_exists_fun S |>.mp hspan
  -- the degree-`n` component of each term of the span expression vanishes
  have key : ∀ j : ι, ((DirectSum.decompose 𝒨 (cf j • y j) n : 𝒨 n) : M) = 0 := by
    intro j
    have hsum : cf j • y j =
        ∑ k ∈ (DirectSum.decompose 𝒮 (cf j)).support,
          ((DirectSum.decompose 𝒮 (cf j) k : S)) • y j := by
      rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒮 (cf j)]
    rw [hsum, coe_decompose_sum 𝒨]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hmem : ((DirectSum.decompose 𝒮 (cf j) k : S)) • y j ∈ 𝒨 ((k : ℤ) + c j) :=
      SetLike.GradedSMul.smul_mem (DirectSum.decompose 𝒮 (cf j) k).2 (hy j)
    by_cases hkn : (k : ℤ) + c j = n
    · have hlt : ∑ i, N i j * deg i < k := by
        have hnj := hn j
        omega
      rw [smul_eq_zero_of_mem_grade 𝒮 f deg hfdeg hgen (y j) (fun i => N i j)
        (fun i => hN i j) hlt (DirectSum.decompose 𝒮 (cf j) k).2]
      simp
    · rw [DirectSum.decompose_of_mem_ne 𝒨 hmem hkn]
  -- so the degree-`n` component of `x` vanishes, and `x` is its own degree-`n` component
  have hxn : ((DirectSum.decompose 𝒨 x n : 𝒨 n) : M) = 0 := by
    rw [← hcf, coe_decompose_sum 𝒨]
    exact Finset.sum_eq_zero fun j _ => key j
  rwa [DirectSum.decompose_of_mem_same 𝒨 hx] at hxn

end Graded

end Stacks.GradedModule

end
