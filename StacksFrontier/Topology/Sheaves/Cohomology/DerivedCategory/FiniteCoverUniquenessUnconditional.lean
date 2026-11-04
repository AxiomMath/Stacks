module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverAFiniteCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionUnconditional

/-!
# The uniqueness half of Tag 0D6A, on exactly the source's hypotheses

[Stacks, Tag 0D6A] is, in Situation [Stacks, Tag 0D67] and under the three hypotheses

1. `X = U_1 ∪ … ∪ U_n` with `U_i` in the displayed collection,
2. for `U, V` in the collection, `U ∩ V` is the union of the members contained in it,
3. for `U` in the collection, `Ext^i(K_U, K_U) = 0` for `i < 0`,

the assertion that *a solution exists and is unique up to unique isomorphism*.

Its **uniqueness** half needs nothing beyond those three hypotheses.  Hypothesis (1) gives that
the collection covers `X`, which with (2) and (3) is exactly what
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional` — the uniqueness clause
of [Stacks, Tag 0D68], proved with nothing granted — consumes.  This file is that one-line
derivation, recorded because the two registrations that carry the uniqueness half of Tag 0D6A
both take an input the source does not have:
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` takes
`Stacks.DerivedGlueing.HasGluingForHomsOver` and the `add_to_stacks` registration in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingFromTransport` takes
`Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤`.  Neither is needed.

Following the rule that a strengthening is a *new* declaration and not an edit of an existing
one, nothing below is deleted from either of those: they quantify differently — the first drops
the nonemptiness of the finite cover, the second drops both covering hypotheses — so neither is
implied by the statement here, and the statement here is not implied by them.

## Main results

* `Stacks.DerivedGlueing.sSup_opens_eq_top_of_finsetSup`: a finite family of members whose union
  is `X` makes the whole collection cover `X`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover_unconditional`: **the
  uniqueness half of [Stacks, Tag 0D6A], on exactly hypotheses (1), (2) and (3) of the source and
  with nothing granted.**

## No `@[stacks 0D6A]` attribute here

Under the covering-set rule a tag's attribute belongs on a declaration stating the *whole* tag,
and this is one of its two halves.  The other half, existence, is not available at these
hypotheses: every existence carrier in this development still takes an input the source does not
have, and the reduction is recorded in the section *What this does not give, and what is still
owed* of the module documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingOverASubcollection`.  Once that
input is discharged the two halves are a conjunction, and the attribute belongs on it.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)

Tags covered: none.  See the section *No `@[stacks 0D6A]` attribute here* above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Hypothesis (1) of [Stacks, Tag 0D6A] implies that the displayed collection covers `X`.**
If finitely many members of the collection have union `X`, then the supremum of the whole
collection is `X`: it is above each of them, hence above their union. -/
theorem sSup_opens_eq_top_of_finsetSup (S : LocallyGiven X) (s : Finset (Opens X.carrier))
    (hmem : ∀ U ∈ s, U ∈ S.opens) (hcover : s.sup id = ⊤) :
    sSup S.opens = ⊤ :=
  top_le_iff.mp (hcover.ge.trans (Finset.sup_le fun U hU => le_sSup (hmem U hU)))

/-- **The uniqueness half of [Stacks, Tag 0D6A], on exactly the source's hypotheses and with
nothing granted.**  In Situation [Stacks, Tag 0D67], assume that `X = U_1 ∪ … ∪ U_n` with the
`U_i` in the displayed collection, that the intersection of two members of the collection is the
union of the members contained in it, and that the prescribed objects have no negative self-`Ext`.
Then any two solutions are identified by exactly one isomorphism of solutions.

The conclusion `Stacks.DerivedGlueing.Solution.IsCompatibleHom A B ψ.hom` is by definition
`∀ (U : Opens X.carrier) (hU : U ∈ S.opens), (S.restriction U ⊤ le_top).map ψ.hom ≫
(B.rho U hU).hom = (A.rho U hU).hom`, which is "compatible with the `ρ_U`" as the source means it.

This is `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional`, the uniqueness
clause of [Stacks, Tag 0D68], with the covering hypothesis supplied from the finite cover by
`Stacks.DerivedGlueing.sSup_opens_eq_top_of_finsetSup`.  The source's own proof of Tag 0D6A opens
with *"Uniqueness was seen in Lemma 20.45.4"*, which is Tag 0D68; this is that sentence.

The hypothesis `_hs` is not used in the proof.  It is kept because the source's hypothesis (1) is
`X = U_1 ∪ … ∪ U_n`, which has `n ≥ 1`: dropping it would state something *stronger* than the
source, and the hypotheses here are meant to be exactly the source's. -/
theorem exists_unique_solutionIso_of_finite_cover_unconditional (S : LocallyGiven X)
    (s : Finset (Opens X.carrier)) (_hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_of_covers_unconditional S
    (sSup_opens_eq_top_of_finsetSup S s hmem hcover) hinter hExt A B

end Stacks.DerivedGlueing

end
