module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput

/-!
# A non-degenerate instance of the finite-cover glueing theorem

Let `(X, 𝒪_X)` be a ringed space and `(ℬ, K_U, ρ^U_V)` a system of locally given derived objects
on it, as in Situation 0D67.  `Stacks.DerivedGlueing.exists_solution_of_finite_cover` is the
existence half of [Stacks, Tag 0D6A], granted the case of a cover by two opens
(`Stacks.DerivedGlueing.GluesAlongTwoOpens`).  Its companion
`Stacks.DerivedGlueing.exists_solution_of_top_mem` proves the same conclusion with no granted
hypothesis whenever `⊤ ∈ ℬ`, that is in the case `n = 1`.

A conditional theorem whose hypotheses, at every system the development can actually produce,
force `⊤ ∈ ℬ` therefore says nothing its `n = 1` companion does not.  That is exactly the state
the existing witness leaves it in: `Stacks.DerivedGlueing.nonempty_solutionOver_sup_opensLE`
satisfies `GluesAlongTwoOpens` at the collection `{W | W ≤ P}` of all opens below a fixed open,
which contains `⊤` only when `P = ⊤`; but the *cover* hypothesis of
`exists_solution_of_finite_cover` asks for finitely many members whose union is `⊤`, and below a
fixed `P` that forces `P = ⊤` and hence `⊤ ∈ ℬ`.  That implication is
`Stacks.DerivedGlueing.top_mem_opensLE_of_finsetSup_eq_top` below, and it is a constraint on every
future witness for the collection `{W | W ≤ P}`, not a defect of this one.

This file supplies a collection for which the implication fails, and with it an instance of
`Stacks.DerivedGlueing.exists_solution_of_finite_cover` whose every binder is discharged and whose
collection does **not** contain `⊤`.  Take two opens `U`, `V` covering `X` and let `ℬ` be the
collection of all opens contained in `U` or in `V`.  Then

* `U` and `V` are members and their union is `⊤`, so the cover hypothesis holds with the
  two-element cover `{U, V}`, and the induction of
  `Stacks.DerivedGlueing.exists_solutionOver_finsetSup` genuinely performs one two-open glueing
  step;
* the intersection of two members is itself a member, so it covers itself and the covering
  condition on intersections holds;
* `⊤` is a member only if `U = ⊤` or `V = ⊤`, so for two *proper* opens the collection misses `⊤`
  and `Stacks.DerivedGlueing.exists_solution_of_top_mem` does not apply.

The system is `Stacks.DerivedGlueing.locallyGivenOfGlobal` prescribed by a sheaf of modules placed
in degree zero, for which the granted two-open case holds outright by
`Stacks.DerivedGlueing.gluesAlongTwoOpens_locallyGivenOfGlobal` — note that lemma assumes nothing
whatever about the collection, which is what makes the present collection admissible.  What is
*not* claimed is that the glueing step glues anything: the prescribed objects are restrictions of
one global object, so a solution over any open is available directly.  The claim is only that the
hypotheses of `exists_solution_of_finite_cover` are jointly satisfiable away from the case `⊤ ∈ ℬ`
in which its conclusion is already unconditional, which is what a non-degeneracy certificate for a
conditional theorem has to say.

## Main definitions

* `Stacks.DerivedGlueing.opensLEPair`: the opens contained in one of two given opens.

## Main results

* `Stacks.DerivedGlueing.top_mem_opensLE_of_finsetSup_eq_top`: a finite cover of `X` by opens below
  a fixed open `P` forces `⊤ ≤ P`, so the collection of all opens below `P` cannot witness the
  cover hypothesis of [Stacks, Tag 0D6A] without containing `⊤`.
* `Stacks.DerivedGlueing.inf_eq_sSup_opensLEPair`: the covering condition on intersections for the
  opens below one of two given opens.
* `Stacks.DerivedGlueing.top_notMem_opensLEPair`: that collection misses `⊤` when both opens are
  proper.
* `Stacks.DerivedGlueing.nonempty_solution_opensLEPair`: **[Stacks, Tag 0D6A], existence, with
  every binder of `Stacks.DerivedGlueing.exists_solution_of_finite_cover` discharged at a
  collection that misses `⊤` as soon as the two covering opens are proper.**

## References

* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The collection of all opens below a fixed open cannot carry a cover -/

/-- **A finite cover of `X` by opens contained in a fixed open `P` forces `⊤ ≤ P`.** The supremum
of the cover is below `P`, and it is `⊤`.

Consequently the collection `{W | W ≤ P}` of all opens contained in `P` — the collection at which
`Stacks.DerivedGlueing.nonempty_solutionOver_sup_opensLE` satisfies
`Stacks.DerivedGlueing.GluesAlongTwoOpens` — can satisfy the cover hypothesis of
[Stacks, Tag 0D6A] only when it contains `⊤`, by
`Stacks.DerivedGlueing.top_mem_opensLE_iff`, and there
`Stacks.DerivedGlueing.exists_solution_of_top_mem` already proves the conclusion with nothing
granted.  So no witness built from that collection certifies the conditional existence theorem
beyond its case `n = 1`. -/
theorem top_mem_opensLE_of_finsetSup_eq_top (P : Opens X.carrier)
    (s : Finset (Opens X.carrier)) (hmem : ∀ W ∈ s, W ∈ {W' : Opens X.carrier | W' ≤ P})
    (hcover : s.sup id = ⊤) :
    (⊤ : Opens X.carrier) ∈ {W' : Opens X.carrier | W' ≤ P} := by
  change (⊤ : Opens X.carrier) ≤ P
  rw [← hcover]
  exact Finset.sup_le fun W hW => hmem W hW

/-! ### The opens below one of two given opens -/

/-- **The opens contained in one of two given opens.** Unlike
`Stacks.DerivedGlueing.opensBelowPair` this is a collection of opens in its own right rather than a
subcollection of a given one, and it is the collection of the system constructed below. -/
def opensLEPair (U V : Opens X.carrier) : Set (Opens X.carrier) :=
  {W | W ≤ U ∨ W ≤ V}

/-- The first open `U` belongs to `opensLEPair U V`. -/
theorem mem_opensLEPair_left (U V : Opens X.carrier) : U ∈ opensLEPair U V := Or.inl le_rfl

/-- The second open `V` belongs to `opensLEPair U V`. -/
theorem mem_opensLEPair_right (U V : Opens X.carrier) : V ∈ opensLEPair U V := Or.inr le_rfl

/-- The collection is closed under passing to a smaller open. -/
theorem mem_opensLEPair_of_le {U V W T : Opens X.carrier} (hW : W ∈ opensLEPair U V) (hTW : T ≤ W) :
    T ∈ opensLEPair U V :=
  hW.imp hTW.trans hTW.trans

/-- **The covering condition on intersections, for the opens below one of two given opens.** The
intersection of two members is contained in the first, hence is itself a member, and so covers
itself. -/
theorem inf_eq_sSup_opensLEPair (U V : Opens X.carrier) :
    ∀ U' ∈ opensLEPair U V, ∀ V' ∈ opensLEPair U V,
      U' ⊓ V' = sSup {W | W ∈ opensLEPair U V ∧ W ≤ U' ⊓ V'} := by
  intro U' hU' V' _
  exact le_antisymm (le_sSup ⟨mem_opensLEPair_of_le hU' inf_le_left, le_rfl⟩)
    (sSup_le fun _ hW => hW.2)

/-- **The collection misses `⊤` when both opens are proper.** `⊤ ≤ U` says `U = ⊤`. -/
theorem top_notMem_opensLEPair {U V : Opens X.carrier} (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    (⊤ : Opens X.carrier) ∉ opensLEPair U V := by
  rintro (h | h)
  · exact hU (top_le_iff.mp h)
  · exact hV (top_le_iff.mp h)

/-- The two-element cover `{U, V}` has supremum `U ⊔ V`. -/
theorem finsetSup_pair_id (U V : Opens X.carrier) :
    letI := Classical.decEq (Opens X.carrier)
    ({U, V} : Finset (Opens X.carrier)).sup id = U ⊔ V := by
  classical
  rw [Finset.sup_insert, Finset.sup_singleton, id, id]

/-! ### The instance of the existence half of Tag 0D6A -/

/-- **[Stacks, Tag 0D6A], existence, with every binder discharged at a collection that misses
`⊤`.** Let `U` and `V` be two opens covering the ringed space `X`, let `ℬ` be the collection of
all opens contained in `U` or in `V`, and prescribe on each member of `ℬ` the restriction of a
sheaf of `𝒪_X`-modules `F` placed in degree zero.  Then the system has a solution, by
`Stacks.DerivedGlueing.exists_solution_of_finite_cover` applied to the two-element cover
`{U, V}`.

Every hypothesis of that theorem is discharged from closed terms: the granted two-open case by
`Stacks.DerivedGlueing.gluesAlongTwoOpens_locallyGivenOfGlobal`, which assumes nothing about the
collection; the cover by `Stacks.DerivedGlueing.finsetSup_pair_id` and `hUV`; the covering
condition on intersections by `Stacks.DerivedGlueing.inf_eq_sSup_opensLEPair`; and the vanishing of
negative self-`Ext` by
`Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`.

Nothing is assumed of `U`, `V` or `F` beyond the cover, and in particular `U` and `V` may both be
**proper**, in which case `⊤ ∉ ℬ` by `Stacks.DerivedGlueing.top_notMem_opensLEPair` and
`Stacks.DerivedGlueing.exists_solution_of_top_mem` — the case `n = 1`, which needs nothing granted
— does not apply.  The induction of
`Stacks.DerivedGlueing.exists_solutionOver_finsetSup` then runs one genuine two-open glueing step.
This is the non-degeneracy certificate that
`Stacks.DerivedGlueing.top_mem_opensLE_of_finsetSup_eq_top` shows the previous witness cannot
give. -/
theorem nonempty_solution_opensLEPair (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) :
    Nonempty (Solution (locallyGivenOfGlobal X (opensLEPair U V)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F))) := by
  classical
  refine exists_solution_of_finite_cover _
    (gluesAlongTwoOpens_locallyGivenOfGlobal X (opensLEPair U V) _)
    {U, V} ⟨U, Finset.mem_insert_self U {V}⟩ (fun W hW => ?_)
    ((finsetSup_pair_id U V).trans hUV) (inf_eq_sSup_opensLEPair U V)
    (fun W hW i hi =>
      subsingleton_shiftedHom_locallyGivenOfGlobal_single X (opensLEPair U V) F W hW i hi)
  rcases Finset.mem_insert.mp hW with h | h
  · exact h ▸ mem_opensLEPair_left U V
  · exact (Finset.mem_singleton.mp h) ▸ mem_opensLEPair_right U V

end Stacks.DerivedGlueing

end
