module

public import StacksFrontier.AlgebraicGeometry.Size.RelativeProjContains
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# From degreewise bounds on the homogeneous pieces to the relative `Proj` in the site

`Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj` puts the relative projective
spectrum of a quasi-coherent graded `𝒪_S`-algebra `A` inside a big fppf site `B`, given a single
cardinal below `B.cutoff` bounding the graded *section ring* `A.sectionRing U` over every affine
open `U` of the base. Its module documentation records that the step turning *degreewise* bounds
on the homogeneous pieces into such a bound on the section ring is not performed there. This file
performs it.

The section ring is the direct sum `⨁ n : ℕ, Γ(A.piece n, U)` of the nonnegative homogeneous
pieces, so it embeds in the product over `ℕ` of those pieces, and a cardinal `c` bounding each
piece bounds the ring by `c ^ ℵ₀`. That power stays below the cutoff because the cutoff is an
uncountable strong prelimit, which is exactly `Cardinal.power_lt_of_isStrongPrelimit`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjSize.mk_sectionRing_le_power`: a cardinal bounding every
  homogeneous piece over an open bounds the graded section ring there by its `ℵ₀`-th power.
* `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj_of_pieces`: the relative `Proj`
  lies in the site under a bound on the pieces uniform in the degree and the affine open.
* `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj_of_pieces_degreewise`: the same
  with one cardinal per degree, the degrees being countable in number and the cutoff of
  uncountable cofinality.

## Implementation notes

**Which properties of the cutoff are spent, and which are not.** The passage from the pieces to
the section ring spends `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`, through the power
`c ^ ℵ₀`; `contains_relativeProj` itself spends only
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff`. The uncountable cofinality
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` is spent *only* by the degreewise form, to
collapse the countable family of per-degree cardinals to one; the form whose bound is already
uniform in the degree does not need it. So a consumer holding a bound uniform in the degree owes
the cofinality field nothing.

**The bound must still be uniform in the affine open.** Nothing here weakens that requirement of
`contains_relativeProj`, and nothing here can: the cutoff is a strong prelimit of uncountable
cofinality but is not assumed regular, so a supremum of fewer than `B.cutoff` cardinals each below
`B.cutoff` can equal `B.cutoff`, while the base may have as many affine opens as the cofinality of
the cutoff. The hypotheses below are therefore quantified over the affine opens *inside* the
bound, exactly as that lemma's are.

**Why the embedding is into a product and not a computation of the direct sum.** Only an upper
bound is wanted, and `DirectSum` is `DFinsupp`, whose coercion to the full product of the summands
is injective. Computing the cardinality of the direct sum itself would need the pieces to be
nontrivial in infinitely many degrees or not, a case distinction with nothing to pay for it.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open AlgebraicGeometry Cardinal CategoryTheory DirectSum
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjSize

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **A uniform bound on the homogeneous pieces bounds the graded section ring by its `ℵ₀`-th
power.** The section ring over `U` is the direct sum `⨁ n : ℕ, Γ(A.piece n, U)`, which embeds in
the product of its summands over `ℕ`; a cardinal `c` bounding every summand bounds that product
by `c ^ ℵ₀`.

No hypothesis on `c` is needed, and none on the open: the statement is pure cardinal arithmetic in
the sections. -/
theorem mk_sectionRing_le_power {c : Cardinal.{u}} (U : S.Opens)
    (hpiece : ∀ n : ℕ, Cardinal.mk (A.sectionPieces U n) ≤ c) :
    Cardinal.mk (A.sectionRing U) ≤ c ^ ℵ₀ := by
  refine (Cardinal.mk_le_of_injective (f := fun (x : A.sectionRing U) n => x n)
    fun x y hxy => DFinsupp.ext fun n => congrFun hxy n).trans ?_
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ (fun _ => c) hpiece).trans ?_
  rw [Cardinal.prod_const]
  simp

/-- **Relative `Proj` lies in the site under a bound on the homogeneous pieces.** If the base is a
scheme of `B` and a single cardinal `c` below `B.cutoff` bounds the sections of every homogeneous
piece over every affine open of the base, then the relative projective spectrum of `A` is a scheme
of `B`.

This is `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj` with its section-ring
bound supplied by `Stacks.AlgebraicGeometry.RelativeProjSize.mk_sectionRing_le_power`, the power
`c ^ ℵ₀` staying below the cutoff by `Cardinal.power_lt_of_isStrongPrelimit`.

The bound is uniform in the affine open, as it must be — see the implementation notes — but the
hypothesis is on the *pieces*, which is the shape in which a graded algebra presents its sections,
rather than on the section ring. -/
theorem contains_relativeProj_of_pieces (hbase : B.Contains S) {c : Cardinal.{u}}
    (hc : c < B.cutoff)
    (hpiece : ∀ (n : ℕ) (U : S.Opens), IsAffineOpen U →
      Cardinal.mk (A.sectionPieces U n) ≤ c) :
    B.Contains (relativeProj A).scheme :=
  contains_relativeProj B A hbase
    (Cardinal.power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hc
      B.aleph0_lt_cutoff)
    fun U hU => mk_sectionRing_le_power A U fun n => hpiece n U hU

/-- **Relative `Proj` lies in the site under one bound per degree.** The homogeneous pieces are
indexed by the nonnegative integers, so a family of cardinals below `B.cutoff` bounding them
degree by degree has a supremum below `B.cutoff`: the family is countable and the cutoff has
uncountable cofinality.

This is the form a consumer actually holds, the sections of a graded algebra being bounded one
degree at a time. The bound in each degree must still be uniform in the affine open. -/
theorem contains_relativeProj_of_pieces_degreewise (hbase : B.Contains S) (c : ℕ → Cardinal.{u})
    (hc : ∀ n : ℕ, c n < B.cutoff)
    (hpiece : ∀ (n : ℕ) (U : S.Opens), IsAffineOpen U →
      Cardinal.mk (A.sectionPieces U n) ≤ c n) :
    B.Contains (relativeProj A).scheme := by
  have hsup : (⨆ n : ULift.{u} ℕ, c n.down) < B.cutoff :=
    Cardinal.iSup_lt_of_lt_cof_ord (α := ULift.{u} ℕ)
      ((Cardinal.mk_le_aleph0 :
        Cardinal.mk (ULift.{u} ℕ) ≤ Cardinal.aleph0).trans_lt B.aleph0_lt_cutoff_cof)
      fun n => hc n.down
  refine contains_relativeProj_of_pieces B A hbase hsup fun n U hU => (hpiece n U hU).trans ?_
  exact le_ciSup Cardinal.bddAbove_of_small (⟨n⟩ : ULift.{u} ℕ)

end Stacks.AlgebraicGeometry.RelativeProjSize

end
