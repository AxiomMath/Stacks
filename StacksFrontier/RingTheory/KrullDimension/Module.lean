module

public import Mathlib.RingTheory.KrullDimension.Module
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
public import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

/-!
# The dimension of the support in a short exact sequence

Proof of `Module.supportDim_of_exact` (Stacks 0B51): for a short exact sequence
`0 → M → N → P → 0` of modules over a commutative ring `R` one has
`dim Supp(N) = max (dim Supp(M)) (dim Supp(P))`.

The support of the middle term of a short exact sequence is the union of the supports of the
outer two, `Supp(N) = Supp(M) ∪ Supp(P)` (`Module.support_of_exact`), so the content of the
lemma is that the Krull dimension of a union of two supports is the larger of the two
dimensions. That is not true of an arbitrary union — in the poset `{𝔭 < 𝔮}` the two singletons
have dimension `0` and their union dimension `1` — and the property of supports that makes it
true is that they are stable under specialization, that is, are upper sets of primes
(`Module.mem_support_mono`). A chain `𝔭₀ < ⋯ < 𝔭ₙ` inside an upper set `u` union another one has
its smallest member `𝔭₀` in one of the two pieces, and every `𝔭ᵢ` lies above `𝔭₀`, hence in that
same piece; so no chain of the union is longer than the longest chain of a single piece.

## Main results

* `Stacks.KrullDimension.SupportDimension.solution`:
  `dim Supp(N) = max (dim Supp(M)) (dim Supp(P))` for a short exact sequence `0 → M → N → P → 0`.

## Implementation notes

The passage from the union to the maximum is isolated as `krullDim_iUnion_of_isUpperSet`, the
equality `krullDim (⋃ i, sᵢ) = ⨆ i, krullDim sᵢ` for an arbitrary family of upper sets of an
arbitrary preorder, with the binary case `krullDim_union_of_isUpperSet` deduced from it; Mathlib
has neither. Both are stated for upper sets of a preorder rather than for supports of modules,
because that is the only hypothesis the argument uses, and the family version is no harder than
the binary one: a chain of the union has all of its members in a single member of the family
(`exists_forall_mem_of_isUpperSet`), because its smallest member has one and an upper set
containing a prime contains everything above it. The reverse inequality is monotonicity of the
Krull dimension in the subset order, `krullDim_le_of_subset`, which Mathlib also lacks.

The source's argument runs instead through the closedness of the three supports (Stacks 00L2),
which needs `R` Noetherian and the three modules finite: it computes `dim Supp` as the
topological dimension of a closed subset of `Spec(R)`, for which the decomposition of a
`Supp(M) ∪ Supp(P)`-chain of irreducible closed subsets into a chain of one piece is the same
step as above. In the formulation by `Module.supportDim`, the Krull dimension of `Supp` as a
partially ordered set of primes, stability under specialization does that work directly, so
neither hypothesis is used here. For the same reason the local case of the source's proof, which
deduces the lemma from the additivity to leading order of the Hilbert–Samuel degree
(Stacks 00KC) through `d(-) = dim Supp(-)` (Stacks 00L8), is not needed either.

## References

* [StacksProject 0B51](https://stacks.math.columbia.edu/tag/0B51)
-/

@[expose] public section

namespace Stacks.KrullDimension.SupportDimension

open Order

/-- The Krull dimension of a subset of a preorder is monotone in that subset. -/
private lemma krullDim_le_of_subset {α : Type*} [Preorder α] {s t : Set α} (h : s ⊆ t) :
    krullDim s ≤ krullDim t :=
  krullDim_le_of_strictMono (Set.inclusion h) fun _ _ hab ↦ hab

/-- A chain in a union of upper sets has all of its members in a single member of the family:
its smallest member `l 0` lies in some `s i`, and every `l j` is above `l 0`, hence in `s i`. -/
private lemma exists_forall_mem_of_isUpperSet {α ι : Type*} [Preorder α] {s : ι → Set α}
    (hs : ∀ i, IsUpperSet (s i)) (l : LTSeries (⋃ i, s i : Set α)) :
    ∃ i, ∀ j, (l j : α) ∈ s i :=
  have ⟨i, h0⟩ := Set.mem_iUnion.mp (l 0).2
  ⟨i, fun j ↦ hs i (l.monotone (Fin.zero_le j)) h0⟩

/-- The Krull dimension of a union of upper sets is the supremum of their Krull dimensions.

Some hypothesis on the family is necessary: the two singletons of a two-element chain have Krull
dimension `0` while their union has Krull dimension `1`. -/
private lemma krullDim_iUnion_of_isUpperSet {α ι : Type*} [Preorder α] {s : ι → Set α}
    (hs : ∀ i, IsUpperSet (s i)) :
    krullDim (⋃ i, s i : Set α) = ⨆ i, krullDim (s i) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ krullDim_le_of_subset (Set.subset_iUnion s i))
  rw [krullDim]
  refine iSup_le fun l ↦ ?_
  obtain ⟨i, hi⟩ := exists_forall_mem_of_isUpperSet hs l
  refine le_trans ?_ (le_iSup (fun i ↦ krullDim (s i)) i)
  exact LTSeries.length_le_krullDim ⟨l.length, fun j ↦ ⟨l j, hi j⟩, l.step⟩

/-- The Krull dimension of the union of two upper sets is the larger of their Krull dimensions. -/
private lemma krullDim_union_of_isUpperSet {α : Type*} [Preorder α] {s t : Set α}
    (hs : IsUpperSet s) (ht : IsUpperSet t) :
    krullDim (s ∪ t : Set α) = max (krullDim s) (krullDim t) := by
  rw [Set.union_eq_iUnion, krullDim_iUnion_of_isUpperSet (Bool.forall_bool.mpr ⟨ht, hs⟩),
    iSup_bool_eq, Bool.cond_true, Bool.cond_false]

/-- The support of a module is an upper set of primes: it is stable under specialization. -/
private lemma isUpperSet_support (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] : IsUpperSet (Module.support R M) :=
  fun _ _ hpq hp ↦ Module.mem_support_mono hpq hp

/-- For a short exact sequence `0 → M → N → P → 0` of `R`-modules, given by `f` injective, `g`
surjective and `Function.Exact f g`, the support dimension of `N` is the larger of those of `M`
and `P`. -/
public theorem solution {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.supportDim R N = max (Module.supportDim R M) (Module.supportDim R P) := by
  unfold Module.supportDim
  rw [Module.support_of_exact h hf hg]
  exact krullDim_union_of_isUpperSet (isUpperSet_support R M) (isUpperSet_support R P)

end Stacks.KrullDimension.SupportDimension

/-!
# Dimension of the support in a short exact sequence

For an `R`-module `M` the *support dimension* `Module.supportDim R M` is the Krull dimension of
`Supp(M) ⊆ Spec(R)`, the set of primes `𝔭` with `M_𝔭 ≠ 0`. Given a short exact sequence
`0 → M → N → P → 0` of `R`-modules one has `Supp(N) = Supp(M) ∪ Supp(P)`
(`Module.support_of_exact`), and the dimension of that union is the larger of the two
dimensions:
`dim Supp(N) = max (dim Supp(M)) (dim Supp(P))`.

Only one property of supports is needed for the passage from the union to the maximum, namely
that a support is stable under specialization (`Module.stableUnderSpecialization_support`): a
chain of primes inside `Supp(M) ∪ Supp(P)` has its smallest member in one of the two pieces,
and then all of its members lie in that same piece, so no chain is longer than the longest
chain of a single piece.

## Main results

* `Module.supportDim_of_exact`: `dim Supp(N) = max (dim Supp(M)) (dim Supp(P))` for a short
  exact sequence `0 → M → N → P → 0`.

## Implementation notes

Neither `IsNoetherianRing R` nor finiteness of the three modules is assumed, although the
source states the lemma for finite modules over a Noetherian ring. The source's argument runs
through the closedness of the three supports (Stacks 00L2), which does need finiteness; but
closedness enters only to make `Supp` a closed subset whose dimension is computed by chains of
irreducible closed subsets, and in the formulation by `Module.supportDim` — the Krull dimension
of `Supp` as a set of primes — stability under specialization already does that work, and holds
for every module over every commutative ring. The statement here is therefore the source's
lemma with its two hypotheses dropped, which is strictly stronger.

The short exact sequence is spelled as in the sibling `Module.support_of_exact`: an exact pair
of `R`-linear maps `f : M →ₗ[R] N`, `g : N →ₗ[R] P` with `f` injective and `g` surjective,
rather than as a `CategoryTheory.ShortComplex (ModuleCat R)`. The equation is oriented with the
middle term alone on the left, again as in `Module.support_of_exact`, where the source writes
the maximum on the left.

The dimensions live in `WithBot ℕ∞`, with `⊥` for an empty support: `max` is then the lattice
join of the linear order `WithBot ℕ∞`, and the equation also covers the degenerate cases
`M = 0` and `P = 0`, where it reads `dim Supp(N) = dim Supp(P)` resp. `dim Supp(M)` because
`max ⊥ x = x`.

Faithfulness. (1) Every hypothesis is used by the conclusion: without `hf` one may take
`f = 0 : R →ₗ[R] R` with `g = id`, and without `hg` one may take `g = 0 : R →ₗ[R] R` with
`f = 0`, and in both cases `Supp` of the outer module is unrelated to the equation; without
exactness, `M = P = 0` and `N = R` breaks it. (2) The scalars are the source's: all three
modules are `R`-modules, the maps are `R`-linear, and all three dimensions are Krull dimensions
of subsets of `Spec(R)`, not of a localization or a quotient. (3) The invariants are pinned,
not merely bounded: the statement is the equality of `Module.supportDim R N` with the maximum,
so both `≤` and `≥` are part of it, and `Module.supportDim` is the canonical invariant
`krullDim (Module.support R _)` rather than an unspecified dimension function. (4) The
instantiation is not degenerate: for `R = ℤ` and `0 → ℤ →ₗ ℤ → ℤ ⧸ 2 → 0` (multiplication by
`2`, then the quotient map) the equation reads `1 = max 1 0`, with the two sides of the maximum
different and both supports nonempty.

## References

* [StacksProject 0B51](https://stacks.math.columbia.edu/tag/0B51)

## Tags

support, dimension, short exact sequence, krull dimension

-/

namespace Module

/-- **Stacks 0B51**.
Let `R` be a commutative ring and let `0 → M → N → P → 0` be a short exact sequence of
`R`-modules, given by `f : M →ₗ[R] N` injective, `g : N →ₗ[R] P` surjective and
`Function.Exact f g`. Then `dim Supp(N) = max (dim Supp(M)) (dim Supp(P))`.

The source assumes `R` Noetherian and the three modules finite; neither hypothesis is needed
for this formulation of the dimension of the support. -/
@[stacks 0B51]
public theorem supportDim_of_exact {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    supportDim R N = max (supportDim R M) (supportDim R P) :=
  Stacks.KrullDimension.SupportDimension.solution h hf hg

end Module
