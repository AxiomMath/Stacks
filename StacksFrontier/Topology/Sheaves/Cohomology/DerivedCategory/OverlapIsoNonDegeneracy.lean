module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.FiniteCoverGlueingNonDegeneracy

/-!
# A non-degenerate instance of the comparison isomorphism of Tag 0D69

`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers` are the two clauses of
[Stacks, Tag 0D69] at the hypotheses the source reads them under: the half of hypothesis (1) of
[Stacks, Tag 0D68] saying that the intersection of two members is the union of the members
contained in it, and its hypothesis (2), the vanishing of negative self-`Ext`.  That the
collection covers the space — the other half of hypothesis (1) — is not taken, being redundant;
see the section on the global covering hypothesis in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtAnOpenFromTheCover`.
Both quantify over the system, so they say nothing unless that hypothesis bundle is
satisfiable — and satisfiable away from the case in which the conclusion is already available
without the glueing argument at all.

That case is `⊤ ∈ ℬ`: when the whole space is a member,
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` proves the uniqueness clause of
Tag 0D68 outright, and over a member the sheaf condition of [Stacks, Tag 0D66] part (2) holds by
`Stacks.DerivedGlueing.hasGluingForHomsAt_of_mem` with nothing to glue.  So the certificate owed
is one system satisfying all three hypotheses whose collection does **not** contain `⊤`.

`Stacks.DerivedGlueing.exists_locallyGiven_overlapIso_top_notMem` is that certificate: the opens
contained in one of two proper opens covering the space, carrying the restrictions of a single
global object, with the comparison isomorphism over the overlap of the two produced from it.  The
prescribed object is an arbitrary sheaf of modules placed in degree zero, so the witness is not
the zero system either.  The hypotheses on the two opens are met on a concrete carrier:
`Stacks.DerivedGlueing.sup_idempotentOpen_eq_top`,
`Stacks.DerivedGlueing.idempotentOpen_fst_ne_top` and
`Stacks.DerivedGlueing.idempotentOpen_snd_ne_top` cover `Spec (ℤ × ℤ)` by the two complementary
basic opens of its idempotents, both proper.

Nothing beyond the collection is new here: the covering condition on intersections is
`Stacks.DerivedGlueing.inf_eq_sSup_opensLEPair`, the vanishing is
`Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`, and the absence of
`⊤` is `Stacks.DerivedGlueing.top_notMem_opensLEPair`, all three for
`Stacks.DerivedGlueing.opensLEPair`.

## Main results

* `Stacks.DerivedGlueing.sSup_opensLEPair_eq_top`: the opens contained in one of two opens
  covering the space cover it.
* `Stacks.DerivedGlueing.exists_locallyGiven_overlapIso_top_notMem`: the hypothesis bundle of the
  two clauses of Tag 0D69, satisfied at a collection missing `⊤`, together with the conclusion of
  the first of them.

## Tags covered

None.  The statement below is a single instance of
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers`, not a clause of Tag 0D69; the tag is
registered on the general statements, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection` and
elsewhere.

## References

* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The opens contained in one of two opens covering the space cover the space.** Both opens are
members of the collection, so its supremum is at least their union. -/
theorem sSup_opensLEPair_eq_top {U V : Opens X.carrier} (hUV : U ⊔ V = ⊤) :
    sSup (opensLEPair U V) = ⊤ :=
  le_antisymm le_top
    (hUV.ge.trans
      (sup_le (le_sSup (mem_opensLEPair_left U V)) (le_sSup (mem_opensLEPair_right U V))))

/-- **The hypothesis bundle of the two clauses of [Stacks, Tag 0D69], satisfied at a collection
that does not contain `⊤`, with the comparison isomorphism over an overlap produced from it.**

The system is the one of `Stacks.DerivedGlueing.locallyGivenOfGlobal`, carried by the opens
contained in one of two proper opens `U`, `V` covering the space, prescribing on each of them the
restriction of an arbitrary sheaf of modules placed in degree zero.  Both hypotheses of
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` hold for it — and so does the covering
of the space, which that theorem no longer asks for and which the conclusion below records
anyway — `⊤` is not a member, and `U` and `V` are, so the comparison isomorphism `ρ_{U,V}` over
their overlap exists and is unique.

This is the non-degeneracy certificate for that theorem and for
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`, whose further binders are three
compatible isomorphisms over the three overlaps — exactly what the first clause produces, at this
same system.  See the module documentation for the concrete carrier on which the hypotheses on
`U` and `V` are met. -/
theorem exists_locallyGiven_overlapIso_top_notMem (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (hU : U ≠ ⊤) (hV : V ≠ ⊤) (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) :
    ∃ (S : LocallyGiven X) (hUS : U ∈ S.opens) (hVS : V ∈ S.opens),
      sSup S.opens = ⊤ ∧
      (∀ A ∈ S.opens, ∀ B ∈ S.opens, A ⊓ B = sSup {W | W ∈ S.opens ∧ W ≤ A ⊓ B}) ∧
      (∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
        Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i)) ∧
      (⊤ : Opens X.carrier) ∉ S.opens ∧
      ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hUS) ≅
          (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hVS),
        IsOverlapHom S hUS hVS inf_le_left inf_le_right φ.hom := by
  have hinf := inf_eq_sSup_opensLEPair U V
  have hvan := subsingleton_shiftedHom_locallyGivenOfGlobal_single X (opensLEPair U V) F
  exact ⟨_, mem_opensLEPair_left U V, mem_opensLEPair_right U V, sSup_opensLEPair_eq_top hUV,
    hinf, hvan, top_notMem_opensLEPair hU hV,
    exists_unique_overlapIso_of_covers _ hinf hvan U V (mem_opensLEPair_left U V)
      (mem_opensLEPair_right U V)⟩

end Stacks.DerivedGlueing

end
