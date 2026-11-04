module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.NonDegenerateCoveringCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionFromTheSite

/-!
# A system for which the uniqueness clause of Tag 0D68 is not a restatement of a known case

Clause (a) of [Stacks, Tag 0D68] —
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence` — says that in
Situation 0D67 a solution is unique up to unique isomorphism, given that the collection covers
the space, that the intersection of two members is the union of the members contained in it, and
that the prescribed objects have no negative self-Ext.

That conclusion is already available **unconditionally** when `⊤` is itself a member of the
collection: `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` proves it with no
granted hypothesis at all, because restriction from `⊤` to `⊤` is a bijection on morphism groups
and compatibility over `⊤` forces compatibility over every member.  So a system whose collection
contains `⊤` — `Stacks.DerivedGlueing.locallyGivenOfTop`, the witness used for the vanishing
clause in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenNonVacuity` — cannot show
that clause (a) says anything new.

This file builds a system at which it does.  The carrier is `Spec (ℤ × ℤ)`
(`Stacks.DerivedGlueing.specULiftProdRingedSpace`), the collection is the one
`Stacks.DerivedGlueing.exists_covering_collection_top_notMem` produces there — it covers the
space, its intersections are unions of members, and it does **not** contain `⊤` — and the
prescribed objects are the restrictions of a sheaf of modules placed in degree zero, for which
the negative self-Ext hypothesis holds outright.  Both covering hypotheses and the self-Ext
hypothesis are therefore discharged, the system has a solution
(`Stacks.DerivedGlueing.nonDegenerateSolution`), and the coherence `hcoh` is the only hypothesis
left standing in `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate`.

Nothing here is tagged: these are witnesses about the reach of a statement, not clauses of any
tag.

## Main definitions

* `Stacks.DerivedGlueing.nonDegenerateCollection` — the covering collection on `Spec (ℤ × ℤ)`
  that does not contain `⊤`, named once so that nothing downstream unfolds the existential it
  comes from.
* `Stacks.DerivedGlueing.nonDegenerateSystem` — the system of Situation 0D67 carried by that
  collection, prescribing on each member the restriction of a sheaf of modules placed in degree
  zero.
* `Stacks.DerivedGlueing.nonDegenerateSolution` — a solution of it.

## Main results

* `Stacks.DerivedGlueing.top_notMem_nonDegenerateSystem_opens` — `⊤` is not a member, so
  `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` does not apply.
* `Stacks.DerivedGlueing.sSup_nonDegenerateSystem_opens` — the collection still covers the
  space, so it is not the trivial collection either.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate` — clause (a) of
  [Stacks, Tag 0D68] at this system, with every binder but the coherence discharged.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The collection -/

/-- **A covering collection of opens of `Spec (ℤ × ℤ)` that does not contain `⊤`.**  This is the
collection produced by `Stacks.DerivedGlueing.exists_covering_collection_top_notMem`, named so
that its three properties can be quoted one at a time and so that nothing that mentions it has
to unfold the existential statement it is chosen from. -/
def nonDegenerateCollection : Set (Opens (specULiftProdRingedSpace.{u}).carrier) :=
  (exists_covering_collection_top_notMem.{u}).choose

/-- The collection covers `Spec (ℤ × ℤ)`: the first half of hypothesis (1) of
[Stacks, Tag 0D68]. -/
theorem sSup_nonDegenerateCollection : sSup nonDegenerateCollection.{u} = ⊤ :=
  (exists_covering_collection_top_notMem.{u}).choose_spec.1

/-- The intersection of two members of the collection is the union of the members contained in
it: the second half of hypothesis (1) of [Stacks, Tag 0D68]. -/
theorem inter_eq_sSup_covered_nonDegenerateCollection :
    ∀ A ∈ nonDegenerateCollection.{u}, ∀ B ∈ nonDegenerateCollection.{u},
      A ⊓ B = sSup {W | W ∈ nonDegenerateCollection.{u} ∧ W ≤ A ⊓ B} :=
  (exists_covering_collection_top_notMem.{u}).choose_spec.2.1

/-- The whole space is not a member of the collection. -/
theorem top_notMem_nonDegenerateCollection :
    (⊤ : Opens (specULiftProdRingedSpace.{u}).carrier) ∉ nonDegenerateCollection.{u} :=
  (exists_covering_collection_top_notMem.{u}).choose_spec.2.2

/-! ### The system and its solution -/

/-- **Situation 0D67 on `Spec (ℤ × ℤ)`, over a covering collection that does not contain `⊤`.**
The collection is `Stacks.DerivedGlueing.nonDegenerateCollection` and the object prescribed on a
member is the restriction to it of the sheaf of modules `F` placed in degree zero; the
transition isomorphisms are the comparisons of restriction in two steps with direct restriction,
by `Stacks.DerivedGlueing.locallyGivenOfGlobal`.

Placing `F` in degree zero is what makes the negative self-Ext hypothesis of
[Stacks, Tag 0D68] hold for every member at once,
`Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`. -/
def nonDegenerateSystem
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    LocallyGiven specULiftProdRingedSpace.{u} :=
  locallyGivenOfGlobal specULiftProdRingedSpace.{u} nonDegenerateCollection.{u}
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) 0).obj F)

/-- The collection of opens of `Stacks.DerivedGlueing.nonDegenerateSystem F` is
`Stacks.DerivedGlueing.nonDegenerateCollection`. -/
@[simp]
theorem nonDegenerateSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    (nonDegenerateSystem.{u} F).opens = nonDegenerateCollection.{u} :=
  rfl

/-- **The collection of the system covers the space**: hypothesis (1) of [Stacks, Tag 0D68],
first half, so the collection is not a trivial one. -/
theorem sSup_nonDegenerateSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    sSup (nonDegenerateSystem.{u} F).opens = ⊤ :=
  sSup_nonDegenerateCollection.{u}

/-- **The intersection of two members of the system's collection is the union of the members
contained in it**: hypothesis (1) of [Stacks, Tag 0D68], second half. -/
theorem inter_eq_sSup_covered_nonDegenerateSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    ∀ A ∈ (nonDegenerateSystem.{u} F).opens, ∀ B ∈ (nonDegenerateSystem.{u} F).opens,
      A ⊓ B = sSup {W | W ∈ (nonDegenerateSystem.{u} F).opens ∧ W ≤ A ⊓ B} :=
  inter_eq_sSup_covered_nonDegenerateCollection.{u}

/-- **The whole space is not a member of the system's collection.**  This is what makes the
system a genuine witness for clause (a) of [Stacks, Tag 0D68]:
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` proves the same conclusion with
nothing granted whenever `⊤` is a member, and it therefore does not apply here. -/
theorem top_notMem_nonDegenerateSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    (⊤ : Opens (specULiftProdRingedSpace.{u}).carrier) ∉ (nonDegenerateSystem.{u} F).opens :=
  top_notMem_nonDegenerateCollection.{u}

/-- **The negative self-Ext hypothesis of [Stacks, Tag 0D68] for the system**: the prescribed
object on a member has no self-extensions in negative degree, because restriction of modules to
an open is exact and carries an object placed in degree zero to one placed in degree zero. -/
theorem subsingleton_shiftedHom_nonDegenerateSystem
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤))
    (U : Opens (specULiftProdRingedSpace.{u}).carrier)
    (hU : U ∈ (nonDegenerateSystem.{u} F).opens) (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom ((nonDegenerateSystem.{u} F).obj U hU)
      ((nonDegenerateSystem.{u} F).obj U hU) i) :=
  subsingleton_shiftedHom_locallyGivenOfGlobal_single specULiftProdRingedSpace.{u}
    nonDegenerateCollection.{u} F U hU i hi

/-- **The system has a solution.**  Its object is the sheaf of modules placed in degree zero
itself, read over `⊤`, and its identifications are the comparisons of restriction in two steps,
by `Stacks.DerivedGlueing.solutionOverOfGlobal` at the open `⊤`.

So `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate` is not a statement about an
empty type. -/
def nonDegenerateSolution
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    Solution (nonDegenerateSystem.{u} F) :=
  (solutionOverOfGlobal specULiftProdRingedSpace.{u} nonDegenerateCollection.{u}
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) 0).obj F)
    ⊤).toSolution

/-- **The system has a solution**, as an inhabitation statement. -/
theorem nonempty_solution_nonDegenerateSystem
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    Nonempty (Solution (nonDegenerateSystem.{u} F)) :=
  ⟨nonDegenerateSolution.{u} F⟩

/-! ### Clause (a) of Tag 0D68 at this system -/

/-- **Clause (a) of [Stacks, Tag 0D68] at a system whose collection does not contain `⊤`,
granted only the coherence `hcoh`.**  Every other binder of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence` is discharged: the
system is `Stacks.DerivedGlueing.nonDegenerateSystem`, the two covering hypotheses are
`Stacks.DerivedGlueing.sSup_nonDegenerateSystem_opens` and
`Stacks.DerivedGlueing.inter_eq_sSup_covered_nonDegenerateSystem_opens`, and the negative
self-Ext hypothesis is `Stacks.DerivedGlueing.subsingleton_shiftedHom_nonDegenerateSystem`.

The witness is not a restatement of an already unconditional case: `⊤` is not a member of the
collection (`Stacks.DerivedGlueing.top_notMem_nonDegenerateSystem_opens`), so
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` does not apply; the collection
nevertheless covers the space; and the type of solutions is inhabited
(`Stacks.DerivedGlueing.nonempty_solution_nonDegenerateSystem`), so the conclusion is not
vacuous. -/
theorem exists_unique_solutionIso_nonDegenerate
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤))
    (A B : Solution (nonDegenerateSystem.{u} F))
    (hcoh : ∀ {O : Opens (specULiftProdRingedSpace.{u}).carrier}
      (K L : OpenDerivedCategory specULiftProdRingedSpace.{u} O)
      {T W : Opens (specULiftProdRingedSpace.{u}).carrier}
      (hTW : T ≤ W) (hWO : W ≤ O)
      (φ : ((nonDegenerateSystem.{u} F).restriction W O hWO).obj K ⟶
        ((nonDegenerateSystem.{u} F).restriction W O hWO).obj L),
      homEquivSlice (nonDegenerateSystem.{u} F) K L (hTW.trans hWO)
          (restrictHomBelow (nonDegenerateSystem.{u} F) hTW hWO φ) =
        RingedSite.restrictDerivedHom
          (Stacks.SheafOfModules.ringedSite (specULiftProdRingedSpace.{u}).sheaf) hTW.hom
          ((jShriek O
            (underlyingRingSheaf specULiftProdRingedSpace.{u})).mapDerivedCategory.obj K)
          ((jShriek O
            (underlyingRingSheaf specULiftProdRingedSpace.{u})).mapDerivedCategory.obj L)
          (homEquivSlice (nonDegenerateSystem.{u} F) K L hWO φ)) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_of_covers_of_coherence (nonDegenerateSystem.{u} F) hcoh
    (sSup_nonDegenerateSystem_opens.{u} F)
    (inter_eq_sSup_covered_nonDegenerateSystem_opens.{u} F)
    (subsingleton_shiftedHom_nonDegenerateSystem.{u} F) A B

end Stacks.DerivedGlueing

end
