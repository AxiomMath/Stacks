module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Graded prime avoidance

Let `S = ⨁_{d ≥ 0} S_d` be a graded ring: a commutative ring with a direct sum
decomposition into additive subgroups `S_d` (the homogeneous components of degree `d`)
indexed by the non-negative integers, satisfying `S_d * S_e ⊆ S_{d+e}`.

The main result says that if `𝔭₁, …, 𝔭_r` are homogeneous prime ideals of `S` and
`I ⊆ S₊ = ⨁_{d ≥ 1} S_d` is a graded ideal with `I ⊄ 𝔭ᵢ` for every `i`, then there is a
homogeneous element `x ∈ I` of positive degree with `x ∉ 𝔭ᵢ` for every `i`.

## Formalization notes

* The grading is indexed by `ℕ`. A graded ring is a family `𝒜 : ℕ → σ` of additive
  submonoids of `S` together with a `GradedRing 𝒜` instance.
* A graded (homogeneous) ideal is a `HomogeneousIdeal 𝒜`, with underlying ideal
  `HomogeneousIdeal.toIdeal`; it is prime when `(p i).toIdeal.IsPrime`.
* The irrelevant ideal `S₊` is `HomogeneousIdeal.irrelevant 𝒜`.
* "Homogeneous of positive degree" is rendered as `∃ d, 1 ≤ d ∧ x ∈ 𝒜 d`, which captures
  both homogeneity (membership in a single graded piece) and positivity of the degree.
* The primes are indexed by `Fin r`; the degenerate case `r = 0` is included.

## Shape of the argument

We may assume there are no inclusions among the `𝔭ᵢ`. The case `r = 1` is immediate. Given
the result for `r - 1`, pick `x ∈ I` homogeneous of positive degree with `x ∉ 𝔭ᵢ` for
`i < r`. If `x ∉ 𝔭_r` we are done, so assume `x ∈ 𝔭_r`. If `I * 𝔭₁ ⋯ 𝔭_{r-1} ⊆ 𝔭_r` then
`I ⊆ 𝔭_r`, a contradiction, so pick `y ∈ I * 𝔭₁ ⋯ 𝔭_{r-1}` homogeneous with `y ∉ 𝔭_r`;
then `x ^ (deg y) + y ^ (deg x)` works.

This is formalized through a `Finset`-indexed generalization `graded_silly_finset`, proved by
strong induction on `s.card`, for which removing a redundant prime is a `Finset.erase`. The
arithmetic kernels are isolated as `homog_witness`, `cross_witness` and `add_pow_avoid`, and
`graded_silly` is the specialization to `s = Finset.univ`.
-/

@[expose] public section

open scoped DirectSum

variable {σ : Type*} {S : Type*} [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A homogeneous positive-degree avoider: for a homogeneous ideal `J` contained in the
irrelevant ideal and a homogeneous prime `q` with `¬ J ≤ q`, there is a *homogeneous*
element `y ∈ J` of *positive* degree (`∃ e ≥ 1, y ∈ 𝒜 e`) with `y ∉ q`.

Since `¬ J ≤ q` there is some `x ∈ J` with `x ∉ q`. As `q` is homogeneous, `x ∉ q` forces
some homogeneous component `xⱼ` of `x` to lie outside `q`, and `xⱼ ∈ J` because `J` too is
homogeneous. Finally `j ≥ 1`: if `j = 0` then `xⱼ` is the degree-`0` part of an element of
the irrelevant ideal, hence `0`, which does lie in `q`. Take `y := xⱼ`. -/
theorem homog_witness
    (J : HomogeneousIdeal 𝒜) (hJ : J ≤ HomogeneousIdeal.irrelevant 𝒜)
    (q : HomogeneousIdeal 𝒜) (hJq : ¬ J ≤ q) :
    ∃ y : S, y ∈ J.toIdeal ∧ (∃ e : ℕ, 1 ≤ e ∧ y ∈ 𝒜 e) ∧ y ∉ q.toIdeal := by
  obtain ⟨x, hxJ, hxq⟩ := IsConcreteLE.not_le_iff_exists.mp hJq
  obtain ⟨j, hj⟩ : ∃ j, ((DirectSum.decompose 𝒜 x j : 𝒜 j) : S) ∉ q.toIdeal := by
    by_contra! h
    exact hxq ((Ideal.IsHomogeneous.mem_iff 𝒜 q.isHomogeneous).mpr h)
  refine ⟨_, (Ideal.IsHomogeneous.mem_iff 𝒜 J.isHomogeneous).mp (hxJ : x ∈ J.toIdeal) j,
    ⟨j, Nat.one_le_iff_ne_zero.mpr ?_, SetLike.coe_mem _⟩, hj⟩
  rintro rfl
  have hx : x ∈ HomogeneousIdeal.irrelevant 𝒜 := hJ hxJ
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  rw [hx] at hj
  exact hj (zero_mem _)

/-- A homogeneous avoider of `p k` lying in all the *other* primes: given homogeneous ideals
`p i`, a homogeneous ideal `I ≤ irrelevant`, a finite index set `s` and a designated index
`k` with `p k` prime, `¬ I ≤ p k` and no inclusion `p i ≤ p k` for `i ∈ s`, `i ≠ k`, there is
a homogeneous positive-degree `b ∈ I` with `b ∈ p i` for every `i ∈ s`, `i ≠ k`, and
`b ∉ p k`.

Primality of `p k` cannot be dropped: in `ℚ[x, y]` with `p k = (xy)` the factorization step
below fails.

Put `K := I * ∏_{i ∈ s.erase k} p i`, again a homogeneous ideal. Then `K ≤ I`, so
`K ≤ irrelevant`, and `K ≤ p i` for each `i ∈ s.erase k`, a product being contained in each
factor. Moreover `¬ K ≤ p k`: as `p k` is prime, `K ≤ p k` would force either `I ≤ p k` or
`p i ≤ p k` for some `i ∈ s.erase k`, both excluded. Applying `homog_witness` to `K` and
`p k` gives a homogeneous positive-degree `b ∈ K` with `b ∉ p k`; then `b ∈ I` and
`b ∈ p i` for `i ∈ s`, `i ≠ k`. -/
theorem cross_witness {ι : Type*} (p : ι → HomogeneousIdeal 𝒜)
    (I : HomogeneousIdeal 𝒜) (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (s : Finset ι) (k : ι)
    (hpk : (p k).toIdeal.IsPrime)
    (hIk : ¬ I ≤ p k)
    (hnoincl : ∀ i ∈ s, i ≠ k → ¬ p i ≤ p k) :
    ∃ b : S, b ∈ I.toIdeal ∧ (∃ e : ℕ, 1 ≤ e ∧ b ∈ 𝒜 e) ∧
      (∀ i ∈ s, i ≠ k → b ∈ (p i).toIdeal) ∧ b ∉ (p k).toIdeal := by
  classical
  have hprodhom : ∀ t : Finset ι, (∏ i ∈ t, (p i).toIdeal).IsHomogeneous 𝒜 := by
    intro t
    induction t using Finset.induction with
    | empty => simpa using Ideal.IsHomogeneous.top 𝒜
    | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      exact (p a).isHomogeneous.mul ih
  let Q : HomogeneousIdeal 𝒜 := ⟨∏ i ∈ s.erase k, (p i).toIdeal, hprodhom _⟩
  let K : HomogeneousIdeal 𝒜 := I * Q
  have hKtoIdeal : K.toIdeal = I.toIdeal * (∏ i ∈ s.erase k, (p i).toIdeal) := by
    change (I * Q).toIdeal = _
    rw [HomogeneousIdeal.toIdeal_mul]
  have hKI : K.toIdeal ≤ I.toIdeal := by
    rw [hKtoIdeal]
    exact Ideal.mul_le_left
  have hKpi : ∀ i ∈ s.erase k, K.toIdeal ≤ (p i).toIdeal := by
    intro i hi
    rw [hKtoIdeal]
    exact Ideal.mul_le_right.trans (Ideal.prod_le_inf.trans (Finset.inf_le hi))
  have hKpk : ¬ K ≤ p k := by
    intro hle
    have hle' : K.toIdeal ≤ (p k).toIdeal := hle
    rw [hKtoIdeal] at hle'
    rcases hpk.mul_le.mp hle' with h1 | h2
    · exact hIk h1
    · obtain ⟨i, hi, hipk⟩ := hpk.prod_le.mp h2
      exact hnoincl i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) hipk
  obtain ⟨b, hbK, hbdeg, hbpk⟩ := homog_witness 𝒜 K (hKI.trans hI) (p k) hKpk
  exact ⟨b, hKI hbK, hbdeg, fun i hi hik => hKpi i (Finset.mem_erase.mpr ⟨hik, hi⟩) hbK, hbpk⟩

/-- The keystone combination: given homogeneous `a ∈ 𝒜 da` and `b ∈ 𝒜 db` with `da, db ≥ 1`,
and an index `k` with `a ∈ p k`, `b ∉ p k`, while `a ∉ p i` and `b ∈ p i` for every other
`i`, the element `a ^ db + b ^ da` is homogeneous of positive degree `da * db` and avoids
*every* prime `p i`.

Both `a ^ db` and `b ^ da` lie in `𝒜 (da * db)`, hence so does their sum, and `da * db ≥ 1`.
At `k` we have `a ^ db ∈ p k` and `b ^ da ∉ p k`, the latter by primality; at `i ≠ k` we have
`a ^ db ∉ p i` and `b ^ da ∈ p i`. In either case the sum of a member and a non-member of a
prime is a non-member, since `a = (a + b) - b`. -/
theorem add_pow_avoid
    {ι : Type*} (p : ι → HomogeneousIdeal 𝒜)
    (hp : ∀ i, (p i).toIdeal.IsPrime)
    (a b : S) (da db : ℕ) (hda : 1 ≤ da) (hdb : 1 ≤ db)
    (ha : a ∈ 𝒜 da) (hb : b ∈ 𝒜 db)
    (k : ι)
    (hak : a ∈ (p k).toIdeal) (hbk : b ∉ (p k).toIdeal)
    (hother : ∀ i, i ≠ k → a ∉ (p i).toIdeal ∧ b ∈ (p i).toIdeal) :
    (a ^ db + b ^ da) ∈ 𝒜 (da * db) ∧ (∀ i, (a ^ db + b ^ da) ∉ (p i).toIdeal) := by
  have hda0 : 0 < da := hda
  have hdb0 : 0 < db := hdb
  refine ⟨?_, fun i => ?_⟩
  · have h1 : a ^ db ∈ 𝒜 (db • da) := SetLike.pow_mem_graded db ha
    have h2 : b ^ da ∈ 𝒜 (da • db) := SetLike.pow_mem_graded da hb
    rw [smul_eq_mul, mul_comm db da] at h1
    rw [smul_eq_mul] at h2
    exact add_mem h1 h2
  · rcases eq_or_ne i k with rfl | hik
    · rw [add_mem_cancel_left (Ideal.pow_mem_of_mem _ hak _ hdb0), (hp i).pow_mem_iff_mem _ hda0]
      exact hbk
    · obtain ⟨hai, hbi⟩ := hother i hik
      rw [add_mem_cancel_right (Ideal.pow_mem_of_mem _ hbi _ hda0), (hp i).pow_mem_iff_mem _ hdb0]
      exact hai

/-- Graded prime avoidance for a finite index set `s`: if `I ≤ irrelevant` is a homogeneous
ideal and `p i` is prime with `¬ I ≤ p i` for every `i ∈ s`, then `I` contains a homogeneous
element of positive degree avoiding every `p i`, `i ∈ s`.

The proof is by strong induction on `s`, generalizing over `p` and `I`. For `s = ∅` take
`x = 0`. Otherwise pick `k ∈ s`.

If some `p i ≤ p j` with `i, j ∈ s` distinct, then `p i` is redundant: recurse on
`s.erase i`, and the resulting `x`, avoiding `p j ⊇ p i`, also avoids `p i`. This is the
reduction to the case of no inclusions.

With no inclusions among the `p i`, `i ∈ s`, apply the inductive hypothesis over `s.erase k`
to get a homogeneous positive-degree `x₀ ∈ I` avoiding `p i` for `i ≠ k`. If `x₀ ∉ p k` we
are done. Otherwise `cross_witness` supplies a homogeneous positive-degree `b ∈ I` with
`b ∈ p i` for `i ∈ s`, `i ≠ k`, and `b ∉ p k`, and `add_pow_avoid` applied to `x₀` and `b`
produces `x := x₀ ^ (deg b) + b ^ (deg x₀) ∈ I`, homogeneous of positive degree
`deg x₀ * deg b` and avoiding every `p i`, `i ∈ s`. Since `add_pow_avoid` quantifies its
hypothesis over all indices, it is applied with `p` reindexed along the subtype
`{i // i ∈ s}`. -/
theorem graded_silly_finset {ι : Type*} (p : ι → HomogeneousIdeal 𝒜)
    (I : HomogeneousIdeal 𝒜) (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (s : Finset ι)
    (hp : ∀ i ∈ s, (p i).toIdeal.IsPrime)
    (hIp : ∀ i ∈ s, ¬ I ≤ p i) :
    ∃ x : S, x ∈ I.toIdeal ∧ (∃ d : ℕ, 1 ≤ d ∧ x ∈ 𝒜 d) ∧ ∀ i ∈ s, x ∉ (p i).toIdeal := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    obtain rfl | ⟨k, hk⟩ := s.eq_empty_or_nonempty
    · exact ⟨0, zero_mem _, ⟨1, le_rfl, zero_mem _⟩, by simp⟩
    have IH' := fun i (hi : i ∈ s) => IH (s.erase i) (Finset.erase_ssubset hi)
      (fun l hl => hp l (Finset.mem_of_mem_erase hl))
      (fun l hl => hIp l (Finset.mem_of_mem_erase hl))
    by_cases hincl : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p i ≤ p j
    · obtain ⟨i, hi, j, hj, hij, hpij⟩ := hincl
      obtain ⟨x, hxI, hxd, hxavoid⟩ := IH' i hi
      refine ⟨x, hxI, hxd, fun l hl => ?_⟩
      rcases eq_or_ne l i with rfl | hli
      · exact fun hmem => hxavoid j (Finset.mem_erase.mpr ⟨hij.symm, hj⟩) (hpij hmem)
      · exact hxavoid l (Finset.mem_erase.mpr ⟨hli, hl⟩)
    · push Not at hincl
      obtain ⟨x₀, hx₀I, ⟨d₀, hd₀, hx₀mem⟩, hx₀avoid⟩ := IH' k hk
      by_cases hx₀k : x₀ ∈ (p k).toIdeal
      · obtain ⟨b, hbI, ⟨e, he, hbmem⟩, hbavoid, hbk⟩ :=
          cross_witness 𝒜 p I hI s k (hp k hk) (hIp k hk) fun i hi hik => hincl i hi k hk hik
        obtain ⟨hxdeg, hxavoid⟩ :=
          add_pow_avoid 𝒜 (fun j : {i // i ∈ s} => p j.1) (fun j => hp j.1 j.2) x₀ b d₀ e hd₀
            he hx₀mem hbmem ⟨k, hk⟩ hx₀k hbk fun j hj =>
              have hjk : j.1 ≠ k := fun h => hj (Subtype.ext h)
              ⟨hx₀avoid j.1 (Finset.mem_erase.mpr ⟨hjk, j.2⟩), hbavoid j.1 j.2 hjk⟩
        exact ⟨x₀ ^ e + b ^ d₀, Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx₀I _ he)
          (Ideal.pow_mem_of_mem _ hbI _ hd₀),
          ⟨d₀ * e, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hxdeg⟩,
          fun i hi => hxavoid ⟨i, hi⟩⟩
      · refine ⟨x₀, hx₀I, ⟨d₀, hd₀, hx₀mem⟩, fun i hi => ?_⟩
        rcases eq_or_ne i k with rfl | hik
        · exact hx₀k
        · exact hx₀avoid i (Finset.mem_erase.mpr ⟨hik, hi⟩)

/-- Graded prime avoidance: if `p₁, …, p_r` are homogeneous prime ideals of a graded ring and
`I` is a homogeneous ideal contained in the irrelevant ideal with `¬ I ≤ pᵢ` for every `i`,
then `I` contains a homogeneous element of positive degree lying outside every `pᵢ`. -/
@[stacks 00JS, sga "3 V 7.2" "partial"]
theorem graded_silly
    {r : ℕ} (p : Fin r → HomogeneousIdeal 𝒜) (hp : ∀ i, (p i).toIdeal.IsPrime)
    (I : HomogeneousIdeal 𝒜) (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (hIp : ∀ i, ¬ I ≤ p i) :
    ∃ x : S, x ∈ I.toIdeal ∧ (∃ d : ℕ, 1 ≤ d ∧ x ∈ 𝒜 d) ∧ ∀ i, x ∉ (p i).toIdeal := by
  obtain ⟨x, hxI, hxd, hxavoid⟩ :=
    graded_silly_finset 𝒜 p I hI Finset.univ (fun i _ => hp i) (fun i _ => hIp i)
  exact ⟨x, hxI, hxd, fun i => hxavoid i (Finset.mem_univ i)⟩
