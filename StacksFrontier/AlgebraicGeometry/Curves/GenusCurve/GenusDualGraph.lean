module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusUnion

/-!
# The genus of a union of many closed subschemes, and its dual graph

Let `k` be a field, `X` a scheme over `k` and `Z : ℕ → X.IdealSheafData` an enumerated family of
closed subschemes.  Write `W n` for the scheme-theoretic union of the first `n` pieces, cut out
by `(Finset.range n).inf Z` — the order on ideal sheaves being the order on ideals, a union of
closed subschemes is an *infimum* of ideal sheaves; see
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusUnion.lean`, whose convention this file
inherits.  Then, with `h⁰(·) = Module.finrank k (structureSheafCohomology · 0)` the dimension of
the ring of global functions and `deg` the same quantity read as the degree of a finite scheme,

`genus (W (m+1)) + ∑ᵢ h⁰(Zᵢ) = ∑ᵢ genus Zᵢ + ∑ⱼ deg (W (j+1) ∩ Z (j+1)) + h⁰(W (m+1))`,

which is `AlgebraicGeometry.genus_finsetInf_range`.  This is the telescoped `n`-piece form of the
two-piece identity `AlgebraicGeometry.genus_union` and has exactly its hypotheses: the whole
union is proper over `k`, and each of the `m` intersections `W (j+1) ∩ Z (j+1)` has vanishing
`H¹` — which "the pieces meet in finitely many points" supplies, through
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`.  Nothing is assumed about the
dimension of `X`, about reducedness, about the singularities, or about connectedness.

## The genus formula

When every piece and every partial union has only the constants as global functions the `h⁰`
terms collapse and the identity becomes

`genus (W (m+1)) + m = ∑ᵢ genus Zᵢ + ∑ⱼ deg (W (j+1) ∩ Z (j+1))`,

which is `AlgebraicGeometry.genus_finsetInf_range_add_card`.  The hypothesis `h⁰(W (j+1)) = 1` at
**every** stage, not only the last, is what the connectedness of the dual graph provides: it says
that every partial union is connected with `k` as its field of constants, which an ordering
compatible with a spanning tree of the dual graph gives when the pieces are geometrically
connected and reduced.  It is also exactly what forces
each step to meet what came before, `0 < deg (W (j+1) ∩ Z (j+1))`
(`AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range`, from
`AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup`), so that
`∑ⱼ deg (W (j+1) ∩ Z (j+1)) - m` is a genuine, nonnegative first Betti number.

Under one further hypothesis the step degrees are replaced by the pairwise ones.  If

`∑_{i ≤ j} deg (Zᵢ ∩ Z (j+1)) = deg (W (j+1) ∩ Z (j+1))`

for each `j < m` — the hypothesis `hnode` below — then

`genus (W (m+1)) + m = ∑ᵢ genus Zᵢ + ∑_{i < j} deg (Zᵢ ∩ Zⱼ)`,

`AlgebraicGeometry.genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount`, whose integer form
`AlgebraicGeometry.genus_finsetInf_range_cast` is **the genus formula**

`genus X = ∑ (genus of a component) + b₁(dual graph)`,

with `b₁ = E - n + 1` for `E = ∑_{i < j} deg (Zᵢ ∩ Zⱼ)` the number of nodes and `n = m + 1` the
number of pieces.  `hnode` is the one place where the local structure of the singularities
enters, and it is stated as the degree identity it is used through rather than as a hypothesis on
`X`: it says that `Z (j+1)` meets the union of the earlier pieces in the *disjoint* union of its
intersections with them, which holds for a curve with at-worst-nodal singularities and distinct
reduced irreducible components — there two components meet in a reduced point at each node, and
no point lies on three of them.  What is formally free is only the termwise bound:
`Zᵢ ⊔ Z (j+1) ≥ (Finset.range (j+1)).inf Z ⊔ Z (j+1)`, so each `Zᵢ ∩ Z (j+1)` is a closed
subscheme of `W (j+1) ∩ Z (j+1)` and its degree is at most `deg (W (j+1) ∩ Z (j+1))`; neither
direction of the identity between the *sum* of those degrees and the total one is formal, and
both are what a triple point, or a non-reduced intersection, breaks.

## Genus zero

At `genus (W (m+1)) = 0` the two nonnegative summands of the formula must both vanish, and that
is the theorem this file is for:

* `AlgebraicGeometry.genus_eq_zero_of_genus_finsetInf_range_eq_zero`: every piece has genus zero;
* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_finsetInf_range_eq_one`: every step
  meets the earlier pieces in a scheme of degree exactly one, so `b₁ = 0`;
* `AlgebraicGeometry.isTree_dualGraph_of_genus_eq_zero`: the dual graph is a **tree**.

The dual graph `AlgebraicGeometry.dualGraph` is the simple graph on `Fin n` joining two distinct
indices whose pieces meet, meeting being read off the degree of the scheme-theoretic
intersection.  That a degree-one step forces a unique earlier neighbour is where `hnode` is used
a second time: the sum of the pairwise degrees over the earlier indices is `1`, so exactly one of
them is nonzero.  Tree-ness is then the combinatorial statement
`SimpleGraph.isTree_of_existsUnique_lt_adj`, proved here: a graph on `Fin (m+1)` in which every
vertex other than `0` has exactly one neighbour below it is connected, and has `m` edges, hence
is a tree by `SimpleGraph.isTree_iff_connected_and_card`.

## `ℕ` or `ℤ`

`AlgebraicGeometry.genus` is `Module.finrank` and so `ℕ`-valued, and in `ℕ` the subtraction of
the classical formula is truncated and the formula false where it truncates.  Every statement
here except the last is therefore an equality of natural numbers **with no subtraction at all**:
the `h⁰` terms of `AlgebraicGeometry.genus_finsetInf_range` are carried explicitly, and the
`- (n-1)` of the Betti number appears as `+ m` on the other side of the equality.  Only
`AlgebraicGeometry.genus_finsetInf_range_cast`, where the Betti number is wanted as a single
quantity, casts to `ℤ`; there the subtraction is the honest one.  This is the convention of
`AlgebraicGeometry.genus_union`, `AlgebraicGeometry.genus_union_add_one` and
`AlgebraicGeometry.genus_union_cast`, from which everything here is derived.

## Main results

* `AlgebraicGeometry.genus_finsetInf_range`: the `n`-piece identity, with the `h⁰` terms present
  and no hypothesis beyond properness of the union and vanishing `H¹` on the intersections.
* `AlgebraicGeometry.genus_finsetInf_range_add_card`: the same when every piece and every partial
  union has only the constants as global functions.
* `AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range`: each
  piece meets the union of the earlier ones.
* `AlgebraicGeometry.genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount` and
  `AlgebraicGeometry.genus_finsetInf_range_cast`: **the genus formula**, the genus of the union
  as the sum of the genera of the pieces plus the first Betti number of the dual graph.
* `AlgebraicGeometry.genus_eq_zero_of_genus_finsetInf_range_eq_zero` and
  `AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_finsetInf_range_eq_one`: genus zero
  kills both summands.
* `SimpleGraph.isTree_of_existsUnique_lt_adj`: a graph with exactly one earlier neighbour at every
  vertex but the first is a tree.
* `AlgebraicGeometry.isTree_dualGraph_of_genus_eq_zero`: **a genus-zero union of pieces with only
  the constants as global functions is a tree of pieces of genus zero.**

## Implementation notes

**Why an enumeration and not a finite family.** The Betti number of the dual graph is computed
along a spanning tree, and the telescoping of `AlgebraicGeometry.genus_union` needs the pieces in
an order.  A family indexed by `ℕ` of which only `Z 0, …, Z m` are used records that order with
no `Fin` arithmetic; the partial unions are then `(Finset.range n).inf Z` and the induction is on
`n`.  The dual graph, which needs a finite vertex type for its edge count, is on `Fin (m+1)`.

**What is not proved here, and why.** Two further steps separate this from the literal statement
"a connected genus-zero nodal curve is a tree of rational curves".  First, `deg (Zᵢ ∩ Zⱼ)` is the
`k`-length of the intersection, not visibly the number of nodes joining the two components; the
identification, and the hypothesis `hnode`, are facts about the étale-local structure of a node
([Stacks, Tag 0C47]) and belong in a module about nodal singularities, not here.  Second, taking
the `Zᵢ` to be *the* irreducible components of a curve requires the decomposition
`Scheme.irreducibleComponentIdeal`, whose infimum over the components is the nilradical rather
than `⊥`, so that the union of the components is the reduction of `X` and not `X`.  Both are
orthogonal to the cohomological content, which is what is proved.

**Why not through `AlgebraicGeometry.NumericalType`.** A numerical type carries multiplicities,
weights and an intersection matrix; it is the combinatorial shadow of a semistable model over a
discrete valuation ring, and no declaration in the tree attaches one to a scheme — no file
mentioning `NumericalType` mentions `Scheme` at all, and
`AlgebraicGeometry.NumericalType.topologicalGenus` is related to nothing but its own
nonnegativity.  Manufacturing a numerical type from a curve over a field would need an
intersection theory that is not here and is not what the genus formula is about, so the link
between the combinatorial genus and `H¹` of a scheme is built directly, with the degree of a
scheme-theoretic intersection in place of an intersection number.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The identity for many pieces -/

/-- Peeling off the last piece of an infimum over `Finset.range`. -/
private lemma inf_range_succ_succ (Z : ℕ → X.IdealSheafData) (j : ℕ) :
    (Finset.range (j + 1 + 1)).inf Z = (Finset.range (j + 1)).inf Z ⊓ Z (j + 1) := by
  rw [Finset.range_add_one, Finset.inf_insert, inf_comm]

/-- Properness of the whole union passes to the union of the first `j + 2` pieces. -/
private lemma isProper_inf_range_succ_inf (Z : ℕ → X.IdealSheafData) {j m : ℕ}
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f)) (hj : j + 1 ≤ m) :
    IsProper ((((Finset.range (j + 1)).inf Z ⊓ Z (j + 1)).subschemeι ≫ f)) := by
  have hle : (Finset.range (m + 1)).inf Z ≤ (Finset.range (j + 1 + 1)).inf Z :=
    Finset.inf_mono (Finset.range_subset_range.mpr (by omega))
  rw [← inf_range_succ_succ]
  exact isProper_subschemeι_comp_of_le k f hle

/-- **The genus of a union of finitely many closed subschemes, in order.**  For
`Z : ℕ → X.IdealSheafData`, writing `W n` for the closed subscheme cut out by
`(Finset.range n).inf Z`, that is for the scheme-theoretic union `Z 0 ∪ ⋯ ∪ Z (n-1)`,

`genus (W (m+1)) + ∑ᵢ h⁰(Zᵢ) = ∑ᵢ genus Zᵢ + ∑ⱼ deg (W (j+1) ∩ Z (j+1)) + h⁰(W (m+1))`,

the sums over `i` running over `0, …, m` and the one over `j` over `0, …, m-1`.

This is `AlgebraicGeometry.genus_union` telescoped: at the `j`-th step it is applied to the
previous union `W (j+1)` and the new piece `Z (j+1)`, whose union is `W (j+2)` and whose
intersection is cut out by `(Finset.range (j+1)).inf Z ⊔ Z (j+1)`, and all the intermediate
`h⁰(W (j+1))` cancel.  The hypotheses are the source's: properness of the whole union, which the
partial unions inherit by `AlgebraicGeometry.isProper_subschemeι_comp_of_le`, and vanishing `H¹`
on each of the `m` intersections that occur.  There is no connectedness, no reducedness and no
dimension hypothesis, and no subtraction: the `h⁰` terms are carried explicitly because `genus`
is `ℕ`-valued. -/
theorem genus_finsetInf_range (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1)) :
    genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f)
        + ∑ i ∈ Finset.range (m + 1),
            Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0)
      = (∑ i ∈ Finset.range (m + 1), genus ((Z i).subschemeι ≫ f))
        + (∑ j ∈ Finset.range m, Module.finrank k (structureSheafCohomology
            (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0))
        + Module.finrank k
            (structureSheafCohomology (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) 0) := by
  induction m with
  | zero =>
    have h1 : (Finset.range (0 + 1)).inf Z = Z 0 := by
      rw [Nat.zero_add, Finset.range_one, Finset.inf_singleton]
    rw [h1]
    simp
  | succ m ih =>
    have heq := inf_range_succ_succ Z m
    have hle : (Finset.range (m + 2)).inf Z ≤ (Finset.range (m + 1)).inf Z :=
      Finset.inf_mono (Finset.range_subset_range.mpr (by omega))
    have hpW : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) :=
      isProper_subschemeι_comp_of_le k f hle
    have := isProper_inf_range_succ_inf k f Z hp (le_refl (m + 1))
    have key := genus_union k f ((Finset.range (m + 1)).inf Z) (Z (m + 1)) (hint m (by omega))
    have ihh := ih hpW fun j hj => hint j (by omega)
    rw [heq]
    rw [Finset.sum_range_succ (f := fun i => Module.finrank k
        (structureSheafCohomology ((Z i).subschemeι ≫ f) 0)),
      Finset.sum_range_succ (f := fun i => genus ((Z i).subschemeι ≫ f)),
      Finset.sum_range_succ (f := fun j => Module.finrank k (structureSheafCohomology
        (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0))]
    omega

/-- **The genus of a union of pieces with only the constants as global functions.**  If
`h⁰(W (m+1)) = 1` and `h⁰(Zᵢ) = 1` for every `i ≤ m` then

`genus (W (m+1)) + m = ∑ᵢ genus Zᵢ + ∑ⱼ deg (W (j+1) ∩ Z (j+1))`.

This is the classical `g = ∑ gᵢ + (number of nodes) - (number of components) + 1` with the
subtraction moved to the other side of the equality, which is how it is stated in `ℕ` without
truncation. -/
theorem genus_finsetInf_range_add_card (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : Module.finrank k
      (structureSheafCohomology (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1) :
    genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) + m
      = (∑ i ∈ Finset.range (m + 1), genus ((Z i).subschemeι ≫ f))
        + ∑ j ∈ Finset.range m, Module.finrank k (structureSheafCohomology
            (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) := by
  have key := genus_finsetInf_range k f Z m hp hint
  have hsum : ∑ i ∈ Finset.range (m + 1),
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = m + 1 := by
    rw [Finset.sum_congr rfl fun i hi => hZ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    simp
  rw [hsum, hU] at key
  omega

/-- **Each piece meets the union of the earlier ones.**  If every partial union and every piece
has only the constants as global functions then `0 < deg (W (j+1) ∩ Z (j+1))` for each `j < m`.

This is `AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup` at the `j`-th step,
and it is what makes `∑ⱼ deg (W (j+1) ∩ Z (j+1)) - m` a nonnegative Betti number rather than a
truncated difference. -/
theorem zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range
    (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hU : ∀ j ≤ m, Module.finrank k
      (structureSheafCohomology (((Finset.range (j + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (j : ℕ) (hj : j < m) :
    0 < Module.finrank k (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) := by
  have := isProper_inf_range_succ_inf k f Z hp (show j + 1 ≤ m by omega)
  have hW : Module.finrank k (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊓ Z (j + 1)).subschemeι ≫ f) 0) = 1 := by
    rw [← inf_range_succ_succ]
    exact hU (j + 1) (by omega)
  exact zero_lt_finrank_structureSheafCohomology_zero_sup k f
    ((Finset.range (j + 1)).inf Z) (Z (j + 1)) hW (hU j (by omega)) (hZ (j + 1) (by omega))

/-! ### Genus zero -/

/-- A family of positive natural numbers whose sum is at most the number of terms is constant
equal to one. -/
private lemma eq_one_of_sum_le_card {ι : Type*} {c : ι → ℕ} :
    ∀ s : Finset ι, (∀ i ∈ s, 1 ≤ c i) → ∑ i ∈ s, c i ≤ s.card → ∀ i ∈ s, c i = 1 := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    intro h1 hsum i hi
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha] at hsum
    have hs : s.card ≤ ∑ j ∈ s, c j := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hca : 1 ≤ c a := h1 a (Finset.mem_insert_self a s)
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · omega
    · exact ih (fun j hj => h1 j (Finset.mem_insert_of_mem hj)) (by omega) i hi'

/-- The two consequences of `genus (W (m+1)) = 0`: the genera of the pieces sum to zero, and the
step degrees sum to `m`.  Both summands of the genus formula being nonnegative, the formula
forces each; the two public corollaries read off one component each. -/
private lemma sum_genus_eq_zero_and_sum_finrank_eq (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : ∀ j ≤ m, Module.finrank k
      (structureSheafCohomology (((Finset.range (j + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hg : genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) = 0) :
    (∑ i ∈ Finset.range (m + 1), genus ((Z i).subschemeι ≫ f)) = 0 ∧
      ∑ j ∈ Finset.range m, Module.finrank k (structureSheafCohomology
        (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) = m := by
  have key := genus_finsetInf_range_add_card k f Z m hp hint (hU m le_rfl) hZ
  have hpos : ∀ j ∈ Finset.range m, 1 ≤ Module.finrank k (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) := fun j hj =>
    zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range k f Z m hp hU hZ j
      (Finset.mem_range.mp hj)
  have hle : m ≤ ∑ j ∈ Finset.range m, Module.finrank k (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) := by
    simpa using Finset.sum_le_sum hpos
  rw [hg] at key
  omega

/-- **Every piece of a genus-zero union has genus zero.**  The genera of the pieces are one of
the two nonnegative summands of the genus formula, so they all vanish when the union has genus
zero.  For two pieces this is `AlgebraicGeometry.genus_add_le_genus_union`; the content here is
that the hypothesis `h⁰ = 1` at every stage, which the two-piece inequality does not need, is
available for the partial unions of a connected enumeration. -/
theorem genus_eq_zero_of_genus_finsetInf_range_eq_zero (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : ∀ j ≤ m, Module.finrank k
      (structureSheafCohomology (((Finset.range (j + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hg : genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) = 0)
    (i : ℕ) (hi : i ≤ m) : genus ((Z i).subschemeι ≫ f) = 0 :=
  Finset.sum_eq_zero_iff.mp (sum_genus_eq_zero_and_sum_finrank_eq k f Z m hp hint hU hZ hg).1
    i (Finset.mem_range.mpr (by omega))

/-- **Every step of a genus-zero union meets the earlier pieces in a scheme of degree one.**
`deg (W (j+1) ∩ Z (j+1)) = 1` for each `j < m`: the step degrees are at least one and sum to
`m`, so each is exactly one, and the first Betti number of the dual graph is zero.  This is the
tree-ness of the dual graph in the form in which the genus formula produces it; the statement as
`SimpleGraph.IsTree` is `AlgebraicGeometry.isTree_dualGraph_of_genus_eq_zero`. -/
theorem finrank_structureSheafCohomology_zero_sup_finsetInf_range_eq_one
    (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : ∀ j ≤ m, Module.finrank k
      (structureSheafCohomology (((Finset.range (j + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hg : genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) = 0)
    (j : ℕ) (hj : j < m) :
    Module.finrank k (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0) = 1 := by
  refine eq_one_of_sum_le_card (Finset.range m) (fun j hj =>
    zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range k f Z m hp hU hZ j
      (Finset.mem_range.mp hj)) ?_ j (Finset.mem_range.mpr hj)
  rw [(sum_genus_eq_zero_and_sum_finrank_eq k f Z m hp hint hU hZ hg).2, Finset.card_range]

/-! ### The genus formula -/

/-- **The genus formula, in `ℕ`.**  Under the hypothesis `hnode` that each piece meets the union
of the earlier ones in the disjoint union of its intersections with them — for a curve with
at-worst-nodal singularities and distinct reduced components, that no point lies on three
components — the step degrees of `AlgebraicGeometry.genus_finsetInf_range_add_card` are replaced
by the pairwise ones:

`genus (W (m+1)) + m = ∑ᵢ genus Zᵢ + ∑_{i < j} deg (Zᵢ ∩ Zⱼ)`,

the double sum being the number of nodes.  Equivalently, in `ℤ`, the genus of the union is the
sum of the genera of the pieces plus `E - n + 1`, the first Betti number of the dual graph; that
is `AlgebraicGeometry.genus_finsetInf_range_cast`.

`hnode` is the only hypothesis here that is not cohomological, and it is deliberately stated as
the identity of degrees it is used through.  Each `Zᵢ ∩ Z (j+1)` is a closed subscheme of
`W (j+1) ∩ Z (j+1)`, since `Zᵢ ⊔ Z (j+1)` dominates `(Finset.range (j+1)).inf Z ⊔ Z (j+1)`, so
each term of the sum is bounded by the right-hand side; `hnode` says that these closed
subschemes are pairwise disjoint and exhaust the intersection, which is what a triple point, or
a non-reduced intersection, breaks. -/
theorem genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount
    (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : Module.finrank k
      (structureSheafCohomology (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hnode : ∀ j < m, ∑ i ∈ Finset.range (j + 1), Module.finrank k
        (structureSheafCohomology ((Z i ⊔ Z (j + 1)).subschemeι ≫ f) 0)
      = Module.finrank k (structureSheafCohomology
          (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0)) :
    genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) + m
      = (∑ i ∈ Finset.range (m + 1), genus ((Z i).subschemeι ≫ f))
        + ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range j, Module.finrank k
            (structureSheafCohomology ((Z i ⊔ Z j).subschemeι ≫ f) 0) := by
  rw [genus_finsetInf_range_add_card k f Z m hp hint hU hZ]
  congr 1
  rw [Finset.sum_range_succ' (fun j => ∑ i ∈ Finset.range j, Module.finrank k
    (structureSheafCohomology ((Z i ⊔ Z j).subschemeι ≫ f) 0)) m]
  simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
  exact (Finset.sum_congr rfl fun j hj => hnode j (Finset.mem_range.mp hj)).symm

/-- **The genus formula.**  `genus X = ∑ (genus of a piece) + b₁(dual graph)`: for `n = m + 1`
pieces with only the constants as global functions, and no point on three of them,

`genus (W n) = ∑ᵢ genus Zᵢ + (E - (n - 1))`,  `E = ∑_{i < j} deg (Zᵢ ∩ Zⱼ)`,

the bracket being `E - n + 1`, the first Betti number of the dual graph.  This is
`AlgebraicGeometry.genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount` cast to `ℤ`, which
is where the subtraction may be written: in `ℕ` it would be truncated.  It does not truncate
here, each of the `m` step degrees being at least one
(`AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup_finsetInf_range`), but the
`ℤ` form is the one in which the Betti number is a single quantity. -/
theorem genus_finsetInf_range_cast (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : Module.finrank k
      (structureSheafCohomology (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hnode : ∀ j < m, ∑ i ∈ Finset.range (j + 1), Module.finrank k
        (structureSheafCohomology ((Z i ⊔ Z (j + 1)).subschemeι ≫ f) 0)
      = Module.finrank k (structureSheafCohomology
          (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0)) :
    (genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) : ℤ)
      = (∑ i ∈ Finset.range (m + 1), (genus ((Z i).subschemeι ≫ f) : ℤ))
        + ((∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range j, (Module.finrank k
            (structureSheafCohomology ((Z i ⊔ Z j).subschemeι ≫ f) 0) : ℤ)) - m) := by
  have key := genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount k f Z m hp hint hU hZ hnode
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) key
  push_cast at hcast
  omega

end AlgebraicGeometry

/-! ### A graph in which every vertex but the first has exactly one earlier neighbour -/

namespace SimpleGraph

/-- **A graph on `Fin (m+1)` in which every vertex other than `0` has exactly one neighbour
below it is a tree.**  Connectedness is an induction on the value of the vertex: the unique
earlier neighbour of a nonzero vertex is reachable from `0`.  Acyclicity is the edge count — the
edges are in bijection with the pairs (vertex, its unique earlier neighbour), of which there are
`m` — through `SimpleGraph.isTree_iff_connected_and_card`.

This is the combinatorial half of `AlgebraicGeometry.isTree_dualGraph_of_genus_eq_zero`: an
enumeration of the pieces along which the union is built up connectedly, with each new piece
meeting the earlier ones in a single point, is exactly a vertex ordering of this kind. -/
theorem isTree_of_existsUnique_lt_adj {m : ℕ} (G : SimpleGraph (Fin (m + 1)))
    (h : ∀ j : Fin (m + 1), j ≠ 0 → ∃! i : Fin (m + 1), i < j ∧ G.Adj i j) :
    G.IsTree := by
  classical
  have hreach : ∀ (d : ℕ) (j : Fin (m + 1)), (j : ℕ) ≤ d → G.Reachable 0 j := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hj0 : j = 0 := Fin.val_eq_zero_iff.mp (by omega)
      exact hj0 ▸ Reachable.rfl
    | succ d ih =>
      intro j hj
      rcases Nat.lt_or_ge (j : ℕ) (d + 1) with hlt | hge
      · exact ih j (by omega)
      · have hj0 : j ≠ 0 := by
          intro h0
          rw [h0] at hge
          simp at hge
        obtain ⟨i, ⟨hij, hadj⟩, -⟩ := h j hj0
        have hiv : (i : ℕ) ≤ d := by
          rw [Fin.lt_def] at hij
          omega
        exact (ih i hiv).trans hadj.reachable
  have hconn : G.Connected := by
    refine ⟨fun u v => ?_⟩
    exact (hreach m u u.is_le).symm.trans (hreach m v v.is_le)
  have hfib : ∀ j : Fin (m + 1), j ≠ 0 →
      {i ∈ (Finset.univ : Finset (Fin (m + 1))) | i < j ∧ G.Adj i j}.card = 1 := by
    intro j hj
    obtain ⟨i, hi, huniq⟩ := h j hj
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.eq_singleton_iff_unique_mem.mpr ⟨by simpa using hi, fun x hx => ?_⟩⟩
    exact huniq x (by simpa using hx)
  have hfib0 : {i ∈ (Finset.univ : Finset (Fin (m + 1))) |
      i < (0 : Fin (m + 1)) ∧ G.Adj i 0}.card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    rintro ⟨hlt, -⟩
    exact absurd hlt (by simp)
  have hsum : ∑ j : Fin (m + 1),
      {i ∈ (Finset.univ : Finset (Fin (m + 1))) | i < j ∧ G.Adj i j}.card = m := by
    rw [Fin.sum_univ_succ, hfib0, Nat.zero_add,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hfib j.succ (Fin.succ_ne_zero j)]
    simp
  have hbij : (Finset.univ.sigma fun j : Fin (m + 1) =>
      {i ∈ (Finset.univ : Finset (Fin (m + 1))) | i < j ∧ G.Adj i j}).card
        = G.edgeFinset.card := by
    refine Finset.card_bij (fun x _ => s(x.2, x.1)) ?_ ?_ ?_
    · rintro ⟨j, i⟩ hx
      have h2 : i < j ∧ G.Adj i j := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
      simpa using h2.2
    · rintro ⟨j, i⟩ hx ⟨j', i'⟩ hy he
      have h2 : i < j ∧ G.Adj i j := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
      have h3 : i' < j' ∧ G.Adj i' j' := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).2
      have hij : (i : ℕ) < (j : ℕ) := h2.1
      have hij' : (i' : ℕ) < (j' : ℕ) := h3.1
      rcases Sym2.eq_iff.mp he with ⟨h4, h5⟩ | ⟨h4, h5⟩
      · simp only at h4 h5
        rw [h4, h5]
      · exfalso
        simp only at h4 h5
        rw [h4, h5] at hij
        omega
    · intro e he
      induction e using Sym2.inductionOn with
      | hf a b =>
        have hadj : G.Adj a b := by simpa using he
        rcases lt_or_gt_of_ne hadj.ne with hab | hab
        · refine ⟨⟨b, a⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hab, hadj⟩
        · refine ⟨⟨a, b⟩, ?_, Sym2.eq_swap⟩
          simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hab, hadj.symm⟩
  have hedge : Nat.card G.edgeSet = m := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, ← hbij, Finset.card_sigma, hsum]
  refine isTree_iff_connected_and_card.mpr ⟨hconn, ?_⟩
  rw [hedge, Nat.card_eq_fintype_card, Fintype.card_fin]

end SimpleGraph

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The dual graph -/

/-- The **dual graph** of a family `Z 0, …, Z (n-1)` of closed subschemes of a scheme over `k`:
two distinct indices are joined when their scheme-theoretic intersection has positive degree,
that is when the two pieces meet.  For the irreducible components of a nodal curve this is the
usual dual graph, its edges being the nodes. -/
def dualGraph (Z : ℕ → X.IdealSheafData) (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ 0 < Module.finrank k
    (structureSheafCohomology ((Z ↑a ⊔ Z ↑b).subschemeι ≫ f) 0)
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [sup_comm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Two indices are adjacent in the dual graph exactly when they are distinct and the global
sections of the structure sheaf of `Z a ⊔ Z b` have positive dimension over `k`. -/
@[simp] theorem dualGraph_adj (Z : ℕ → X.IdealSheafData) (n : ℕ) (a b : Fin n) :
    (dualGraph k f Z n).Adj a b ↔ a ≠ b ∧ 0 < Module.finrank k
      (structureSheafCohomology ((Z ↑a ⊔ Z ↑b).subschemeι ≫ f) 0) := Iff.rfl

/-- A family of natural numbers indexed by `Finset.range n` whose sum is one is nonzero at
exactly one index. -/
private lemma existsUnique_lt_of_sum_eq_one {c : ℕ → ℕ} {n : ℕ}
    (h : ∑ i ∈ Finset.range n, c i = 1) : ∃! i, i < n ∧ 0 < c i := by
  classical
  have hcard : {i ∈ Finset.range n | 0 < c i}.card = 1 := by
    have hle : {i ∈ Finset.range n | 0 < c i}.card • 1
        ≤ ∑ i ∈ {i ∈ Finset.range n | 0 < c i}, c i :=
      Finset.card_nsmul_le_sum _ _ _ fun i hi => (Finset.mem_filter.mp hi).2
    have hle2 : ∑ i ∈ {i ∈ Finset.range n | 0 < c i}, c i ≤ ∑ i ∈ Finset.range n, c i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hpos : 0 < {i ∈ Finset.range n | 0 < c i}.card := by
      rcases Finset.eq_empty_or_nonempty {i ∈ Finset.range n | 0 < c i} with he | hne
      · refine absurd h ?_
        rw [Finset.sum_eq_zero fun i hi => ?_]
        · omega
        · by_contra hc
          have hmem : i ∈ {i ∈ Finset.range n | 0 < c i} :=
            Finset.mem_filter.mpr ⟨hi, Nat.pos_of_ne_zero hc⟩
          rw [he] at hmem
          exact absurd hmem (Finset.notMem_empty i)
      · exact Finset.card_pos.mpr hne
    simp only [smul_eq_mul, mul_one] at hle
    omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcard
  have hmem : i₀ ∈ {i ∈ Finset.range n | 0 < c i} := by rw [hi₀]; simp
  refine ⟨i₀, ⟨Finset.mem_range.mp (Finset.mem_filter.mp hmem).1,
    (Finset.mem_filter.mp hmem).2⟩, fun x hx => ?_⟩
  have hx' : x ∈ {i ∈ Finset.range n | 0 < c i} :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hx.2⟩
  rw [hi₀] at hx'
  simpa using hx'

/-- **A connected genus-zero union of pieces is a tree of pieces of genus zero.**  For an
enumeration `Z 0, …, Z m` of closed subschemes of `X` whose union `W (m+1)` is proper over `k`,
whose partial unions and pieces have only the constants as global functions, whose consecutive
intersections have vanishing `H¹`, and in which no point lies on three pieces — the hypothesis
`hnode` — vanishing of `genus (W (m+1))` makes `AlgebraicGeometry.dualGraph` a tree.

Together with `AlgebraicGeometry.genus_eq_zero_of_genus_finsetInf_range_eq_zero`, which says that
every piece then has genus zero, this is the statement that a connected genus-zero curve with
at-worst-nodal singularities is a tree of rational curves, the components being the pieces.

The proof is the genus formula: at genus zero each step degree is one
(`AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_finsetInf_range_eq_one`), so by
`hnode` the pairwise degrees against the earlier pieces sum to one and exactly one of them is
nonzero; `SimpleGraph.isTree_of_existsUnique_lt_adj` turns that into tree-ness. -/
theorem isTree_dualGraph_of_genus_eq_zero (Z : ℕ → X.IdealSheafData) (m : ℕ)
    (hp : IsProper (((Finset.range (m + 1)).inf Z).subschemeι ≫ f))
    (hint : ∀ j < m, IsZero (structureSheafCohomology
      (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 1))
    (hU : ∀ j ≤ m, Module.finrank k
      (structureSheafCohomology (((Finset.range (j + 1)).inf Z).subschemeι ≫ f) 0) = 1)
    (hZ : ∀ i ≤ m,
      Module.finrank k (structureSheafCohomology ((Z i).subschemeι ≫ f) 0) = 1)
    (hnode : ∀ j < m, ∑ i ∈ Finset.range (j + 1), Module.finrank k
        (structureSheafCohomology ((Z i ⊔ Z (j + 1)).subschemeι ≫ f) 0)
      = Module.finrank k (structureSheafCohomology
          (((Finset.range (j + 1)).inf Z ⊔ Z (j + 1)).subschemeι ≫ f) 0))
    (hg : genus (((Finset.range (m + 1)).inf Z).subschemeι ≫ f) = 0) :
    (dualGraph k f Z (m + 1)).IsTree := by
  refine SimpleGraph.isTree_of_existsUnique_lt_adj _ fun j hj => ?_
  have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hj)
  have hjle : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
  obtain ⟨p, hp'⟩ : ∃ p, (j : ℕ) = p + 1 := ⟨(j : ℕ) - 1, by omega⟩
  have hpm : p < m := by omega
  have hs : ∑ i ∈ Finset.range (p + 1), Module.finrank k
      (structureSheafCohomology ((Z i ⊔ Z (p + 1)).subschemeι ≫ f) 0) = 1 :=
    (hnode p hpm).trans
      (finrank_structureSheafCohomology_zero_sup_finsetInf_range_eq_one k f Z m hp hint hU hZ hg
        p hpm)
  obtain ⟨i₀, ⟨hi₀lt, hi₀pos⟩, huniq⟩ := existsUnique_lt_of_sum_eq_one hs
  have hi₀m : i₀ < m + 1 := by omega
  refine ⟨⟨i₀, hi₀m⟩, ⟨?_, ?_⟩, fun x hx => ?_⟩
  · exact Fin.lt_def.mpr (show i₀ < (j : ℕ) by omega)
  · rw [dualGraph_adj]
    refine ⟨fun hcon => ?_, ?_⟩
    · exact absurd (congrArg Fin.val hcon) (show i₀ ≠ (j : ℕ) by omega)
    · show 0 < Module.finrank k (structureSheafCohomology ((Z i₀ ⊔ Z ↑j).subschemeι ≫ f) 0)
      rw [hp']
      exact hi₀pos
  · obtain ⟨hxlt, hxadj⟩ := hx
    rw [dualGraph_adj] at hxadj
    rw [Fin.lt_def, hp'] at hxlt
    have hxpos := hxadj.2
    rw [hp'] at hxpos
    exact Fin.val_injective (by simpa using huniq (x : ℕ) ⟨hxlt, hxpos⟩)

end AlgebraicGeometry

end
