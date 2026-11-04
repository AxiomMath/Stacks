module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegreeComponents

/-!
# The genus of a union of finitely many closed subschemes, with pairwise intersection degrees

Let `k` be a field, `X` a scheme over `k` and `P : ι → X.IdealSheafData` a family of closed
subschemes `Zᵢ` indexed by a type `ι`.  For a finite set `s : Finset ι` the scheme-theoretic
union of the pieces indexed by `s` is cut out by `s.inf P` — the order on ideal sheaves being
the order on ideals, a union of closed subschemes is an *infimum* of ideal sheaves and an
intersection a *supremum*; see
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusUnion.lean`, whose convention this file
inherits.  Writing `h⁰(·)` for `Module.finrank k (structureSheafCohomology · 0)`, the dimension
over `k` of the ring of global functions, and reading it as the degree `deg` of a finite scheme
where it is one, the identity proved here is

`2 h⁰(⋃ᵢ Zᵢ) + 2 ∑ᵢ genus Zᵢ + ∑ᵢ ∑_{j ≠ i} deg (Zᵢ ∩ Zⱼ) = 2 ∑ᵢ h⁰(Zᵢ) + 2 genus (⋃ᵢ Zᵢ)`,

all sums over `s`, which is `AlgebraicGeometry.genus_finsetInf_pairwise`.

## What it is, and how it differs from the enumerated form

This is the many-piece identity `AlgebraicGeometry.genus_finsetInf_range` with the *step*
degrees of the telescoping — the degree of the intersection of each new piece with the union of
the earlier ones — replaced by the *pairwise* ones `deg (Zᵢ ∩ Zⱼ)`.  The replacement is legitimate
because no point lies on three of the pieces, which is the hypothesis `hthree`:
`P i ⊔ P j ⊔ P l = ⊤` for distinct `i`, `j`, `l` says that the scheme-theoretic intersection of
any three distinct pieces is empty.  Under it the intersection of a new piece with the union of
the earlier ones is the *disjoint* union of its intersections with them, by
`AlgebraicGeometry.Scheme.IdealSheafData.finsetInf_sup_of_pairwise`, so its degree is the sum of
their degrees by `AlgebraicGeometry.finrank_structureSheafCohomology_zero_finsetInf_eq_sum`.

`AlgebraicGeometry.genus_finsetInf_range_add_card_eq_sum_genus_add_nodeCount` performs the same
replacement for a family enumerated by `ℕ`, but it assumes `h⁰ = 1` on every piece and on the
total union — the statement there is the classical form, with the `h⁰` terms eliminated — and it
takes the decomposition of each step degree as a hypothesis rather than deducing it.  The
statement here is over an unordered `Finset`, carries the `h⁰` terms explicitly and assumes
nothing about connectedness; the two are therefore independent, neither being an instance of the
other.

## Why the factor `2`

The double sum `∑ᵢ ∑_{j ∈ s.erase i} deg (Zᵢ ∩ Zⱼ)` runs over *ordered* pairs of distinct
indices, so it counts each unordered pair `{i, j}` twice.  Writing the identity with that sum
rather than with a sum over unordered pairs — which would need an order on `ι`, or a quotient —
therefore doubles every other term.  Everything stays in `ℕ` with no subtraction: `genus` is a
`Module.finrank` and hence `ℕ`-valued, and the truncated difference that the classical form
`genus (⋃ Zᵢ) = ∑ genus Zᵢ + (number of nodes) - (number of pieces) + 1` would involve is
avoided exactly as in `AlgebraicGeometry.genus_union`, by keeping the `h⁰` terms.

## The hypotheses

They are those of `AlgebraicGeometry.genus_union`, taken along the induction, plus `hthree`.
Properness is required of the total union only; the union of any subfamily, every piece and every
pairwise intersection inherits it along `≤` by
`AlgebraicGeometry.isProper_subschemeι_comp_of_le`.  The vanishing of `H¹` is required of each
intersection of a piece with a union of other pieces, which is the hypothesis `hint`; it holds
whenever those intersections are affine, by
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`, so in particular whenever the
pieces meet in finitely many points.  There is no connectedness, reducedness or dimension
hypothesis.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The off-diagonal double sum over an enlarged index set -/

/-- **Adding one index to an off-diagonal double sum of a symmetric function.**  For `a ∉ t` the
sum of `g i j` over the ordered pairs of distinct indices drawn from `insert a t` is the
corresponding sum over `t` plus `2 * ∑ j ∈ t, g a j`: the row `i = a` contributes
`∑ j ∈ t, g a j`, and each row `i ∈ t` gains the single new entry `j = a`, contributing
`g i a = g a i`.  This is the bookkeeping behind the induction in
`AlgebraicGeometry.genus_finsetInf_pairwise`. -/
private theorem sum_sum_erase_insert {ι : Type*} [DecidableEq ι] (g : ι → ι → ℕ)
    (hsymm : ∀ i j, g i j = g j i) {a : ι} {t : Finset ι} (ha : a ∉ t) :
    ∑ i ∈ insert a t, ∑ j ∈ (insert a t).erase i, g i j
      = (∑ i ∈ t, ∑ j ∈ t.erase i, g i j) + 2 * ∑ j ∈ t, g a j := by
  have hrow : ∀ i ∈ t, ∑ j ∈ (insert a t).erase i, g i j
      = g i a + ∑ j ∈ t.erase i, g i j := by
    intro i hi
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne,
      Finset.sum_insert fun h => ha (Finset.mem_of_mem_erase h)]
  have hdiag : ∑ i ∈ t, g i a = ∑ j ∈ t, g a j :=
    Finset.sum_congr rfl fun i _ => hsymm i a
  rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.sum_congr rfl hrow,
    Finset.sum_add_distrib]
  omega

/-- **The degree of the intersection of a union with a closed subscheme, no point lying on two
pieces and on `Q`.**  If `P i ⊔ P j ⊔ Q = ⊤` for distinct `i`, `j` in `t`, the dimension of the
global functions on the intersection of `Q` with the union of the pieces indexed by `t` is the sum
of the corresponding dimensions for the intersections of `Q` with each piece. -/
private theorem finrank_structureSheafCohomology_zero_finsetInf_sup_eq_sum
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {ι : Type*} (P : ι → X.IdealSheafData) (Q : X.IdealSheafData) (t : Finset ι)
    (hpairwise : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → P i ⊔ P j ⊔ Q = ⊤)
    (hp : IsProper ((t.inf P ⊔ Q).subschemeι ≫ f)) :
    Module.finrank k (structureSheafCohomology ((t.inf P ⊔ Q).subschemeι ≫ f) 0)
      = ∑ j ∈ t, Module.finrank k (structureSheafCohomology ((P j ⊔ Q).subschemeι ≫ f) 0) := by
  have hdistr := Scheme.IdealSheafData.finsetInf_sup_of_pairwise P Q t hpairwise
  rw [hdistr]
  refine finrank_structureSheafCohomology_zero_finsetInf_eq_sum k f _ t
    (fun i hi j hj hij => ?_) (by rwa [← hdistr])
  rw [sup_sup_sup_comm, sup_idem]
  exact hpairwise i hi j hj hij

/-! ### The identity -/

/-- **The genus of a union of finitely many closed subschemes, no three of which meet.**  Let `k`
be a field, `X` a scheme over `k` and `P : ι → X.IdealSheafData` a family of closed subschemes
`Zᵢ`.  For a finite set `s` of indices write `W` for the scheme-theoretic union of the pieces
indexed by `s`, cut out by `s.inf P`.  If no point lies on three distinct pieces — `hthree`, the
scheme-theoretic intersection of any three distinct pieces being empty — then

`2 h⁰(W) + 2 ∑ᵢ genus Zᵢ + ∑ᵢ ∑_{j ≠ i} deg (Zᵢ ∩ Zⱼ) = 2 ∑ᵢ h⁰(Zᵢ) + 2 genus W`,

where `h⁰` is the dimension over `k` of the ring of global functions and `deg` the same quantity
read as the degree of a finite scheme.

This is `AlgebraicGeometry.genus_union` telescoped over `s` in an arbitrary order, with the step
degree at each stage — the degree of the intersection of the new piece with the union of the
earlier ones — rewritten as the sum of the pairwise degrees.  That rewriting is
`AlgebraicGeometry.Scheme.IdealSheafData.finsetInf_sup_of_pairwise` followed by
`AlgebraicGeometry.finrank_structureSheafCohomology_zero_finsetInf_eq_sum`, and `hthree` is
exactly what they need.

The double sum is over *ordered* pairs of distinct indices and so counts each pair twice, which
is where the factor `2` on the other terms comes from; the `h⁰` terms are carried explicitly
because `genus` is `ℕ`-valued and the classical form would need a truncated subtraction.
Properness is assumed of the union only, the pieces and the subfamily unions inheriting it by
`AlgebraicGeometry.isProper_subschemeι_comp_of_le`, and `hint` asks for the vanishing of `H¹` on
each intersection of a piece with a union of other pieces, which is what "the pieces meet in
finitely many points" provides. -/
theorem genus_finsetInf_pairwise
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {ι : Type*} [DecidableEq ι] (P : ι → X.IdealSheafData) (s : Finset ι)
    (hthree : ∀ i ∈ s, ∀ j ∈ s, ∀ l ∈ s, i ≠ j → i ≠ l → j ≠ l → P i ⊔ P j ⊔ P l = ⊤)
    (hp : IsProper ((s.inf P).subschemeι ≫ f))
    (hint : ∀ t : Finset ι, t ⊆ s → ∀ a ∈ s, a ∉ t →
      IsZero (structureSheafCohomology ((P a ⊔ t.inf P).subschemeι ≫ f) 1)) :
    2 * Module.finrank k (structureSheafCohomology ((s.inf P).subschemeι ≫ f) 0)
        + 2 * ∑ i ∈ s, genus ((P i).subschemeι ≫ f)
        + ∑ i ∈ s, ∑ j ∈ s.erase i,
            Module.finrank k (structureSheafCohomology ((P i ⊔ P j).subschemeι ≫ f) 0)
      = 2 * ∑ i ∈ s, Module.finrank k (structureSheafCohomology ((P i).subschemeι ≫ f) 0)
        + 2 * genus ((s.inf P).subschemeι ≫ f) := by
  revert hthree hp hint
  induction s using Finset.induction with
  | empty =>
      intro _ _ _
      rw [Finset.inf_empty]
      simp only [Finset.sum_empty, genus_eq_finrank_structureSheafCohomology,
        finrank_structureSheafCohomology_eq_zero_of_isEmpty k f (⊤ : X.IdealSheafData)]
      omega
  | insert a t ha ih =>
      intro hthree hp hint
      have hsub : t ⊆ insert a t := Finset.subset_insert a t
      have hat : a ∈ insert a t := Finset.mem_insert_self a t
      have hinsert : (insert a t).inf P = P a ⊓ t.inf P := Finset.inf_insert
      have hpinf : IsProper ((P a ⊓ t.inf P).subschemeι ≫ f) := by rwa [← hinsert]
      have hpt : IsProper ((t.inf P).subschemeι ≫ f) :=
        isProper_subschemeι_comp_of_le k f (inf_le_right : P a ⊓ t.inf P ≤ t.inf P)
      -- No point lies on two pieces indexed by `t` and on the piece `P a`.
      have hpairwise : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → P i ⊔ P j ⊔ P a = ⊤ := fun i hi j hj hij =>
        hthree i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) a hat hij
          (fun e => ha (e ▸ hi)) (fun e => ha (e ▸ hj))
      -- Hence the intersection of `P a` with the union of the pieces indexed by `t` is the
      -- disjoint union of the pairwise intersections, and its degree is the sum of theirs.
      have key := genus_union k f (P a) (t.inf P) (hint t hsub a hat ha)
      rw [sup_comm (P a) (t.inf P),
        finrank_structureSheafCohomology_zero_finsetInf_sup_eq_sum f P (P a) t hpairwise
          (isProper_subschemeι_comp_of_le k f le_sup_left)] at key
      have ihh := ih
        (fun i hi j hj l hl => hthree i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl)) hpt
        (fun t' ht' b hb hbt' =>
          hint t' (ht'.trans hsub) b (Finset.mem_insert_of_mem hb) hbt')
      have hcomm : ∑ j ∈ t, Module.finrank k
            (structureSheafCohomology ((P a ⊔ P j).subschemeι ≫ f) 0)
          = ∑ j ∈ t, Module.finrank k
            (structureSheafCohomology ((P j ⊔ P a).subschemeι ≫ f) 0) :=
        Finset.sum_congr rfl fun j _ => by rw [sup_comm]
      rw [hinsert, sum_sum_erase_insert
          (fun i j => Module.finrank k
            (structureSheafCohomology ((P i ⊔ P j).subschemeι ≫ f) 0))
          (fun i j => by rw [sup_comm]) ha,
        Finset.sum_insert ha, Finset.sum_insert ha]
      omega

end AlgebraicGeometry
