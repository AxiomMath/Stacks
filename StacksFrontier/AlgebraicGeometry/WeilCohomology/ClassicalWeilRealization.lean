module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealizationExtension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRestrictionRealization
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationLiebermanBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationUntwistedIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotiveTate

/-!
# Classical Weil cohomology theories are realizations of Chow motives

Stacks 0FH3: for `k` algebraically closed and `F` of characteristic zero, a classical Weil
cohomology theory is the same thing as a `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of
symmetric monoidal categories with an isomorphism `F[2] ≅ G(𝟏(1))` such that `G(h(X))` lives in
nonnegative degrees and `dim_F G⁰(h(X)) = 1` for every smooth projective variety `X`
(`Stacks.WeilCohomology.ClassicalMotiveRealization`), the two being related by `H^*(X) = G(h(X))`
with all its structure (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds`).

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_isoClassEquiv` (in
  `StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.IsoClassEquiv`):
  **Stacks 0FH3**. Isomorphism classes of classical Weil cohomology theories
  (`ClassicalWeilCohomologyTheory.isoSetoid`) and of realizations `(G, F[2] ≅ G(𝟏(1)))`
  (`ClassicalMotiveRealization.isoSetoid`) are in bijection, a theory corresponding to a
  realization exactly when `H^*(X) = G(h(X))` with all its structure, and the inverse bijection
  sends `(G, F[2] ≅ G(𝟏(1)))` to the theory `H^*(X) = G(h(X))` of the first paragraph of the
  proof (`ClassicalMotiveRealization.toClassicalWeilCohomologyTheory`).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_classicalMotiveRealization`: the
  functor of Stacks 0FH2 with some isomorphism `F[2] ≅ G(𝟏(1))` satisfies conditions (1) and (2),
  with `H^*(X) = G(h(X))` as graded vector spaces naturally in `X`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory`:
  conversely, the functor of such a realization is that of some classical Weil cohomology theory,
  with `H^*(X) = G(h(X))` as graded vector spaces naturally in `X` (through Stacks 0FHK).

The last two record the two constructions of the proof on their own; the isomorphisms
`F[2] ≅ G(𝟏(1))` and the cycle class and trace maps enter only in the first.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

/-- **The functor of Stacks 0FH2 is a realization as in Stacks 0FH3.** For a classical Weil
cohomology theory `H^*` (Stacks 0FGV, over the Chow groups of Chapter 42), the functor
`G : M_k ⥤ graded F-vector spaces` of Stacks 0FH2 (`ClassicalWeilCohomologyTheory.motiveFunctor`),
with some isomorphism `F[2] ≅ G(𝟏(1))`, is a `ℚ`-linear functor of symmetric monoidal categories
with `G(h(X))` in nonnegative degrees and `dim_F G⁰(h(X)) = 1` for every smooth projective variety
`X`, and `H^*(X) = G(h(X))` as graded vector spaces, naturally in `X`. The isomorphism
`F[2] ≅ G(𝟏(1))` here is an arbitrary one (`G(𝟏(1))` is a line in degree `-2`); the one matching
the trace maps of `H^*`, and the correspondence of Stacks 0FH3 itself, are
`ClassicalWeilCohomologyTheory.exists_isoClassEquiv`. -/
theorem ClassicalWeilCohomologyTheory.exists_classicalMotiveRealization
    (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k)) :
    ∃ R : ClassicalMotiveRealization k F,
      Nonempty (T.toPre.toPoincarePairingSetup.MotiveComparison R.G) := by
  let E := T.motiveComparison
  let : BraidedCategory (GradedObject ℤ (ModuleCat.{v} F)) := GradedObject.koszulBraidedCategory
  let hbr : T.motiveFunctor.Braided := WeilData.motiveFunctorBraided _ _ _
  exact ⟨{ G := T.motiveFunctor
           braided := hbr
           additive := inferInstance
           linear := inferInstance
           tateIso := (nonempty_tateIso (WeilData.motiveFunctor_tate_degree _ _ _)).some
           nonneg := fun X i hi ↦ E.isZero_of_eq_zero fun a ↦ T.eq_zero_of_neg X hi a
           finrank_zero := fun X ↦ (E.finrank_eq X 0).symm.trans (T.finrank_piece_zero X) },
    ⟨E⟩⟩

/-- **The first paragraph of the proof of Stacks 0FH3**, given the data of a realization: if data
`W` (D0)–(D3) satisfying (A), (B), (C) have the realization `R.G` (Stacks 0FHL: a natural
isomorphism between `R.G` and the functor `W.motiveFunctor`), then the restriction of `W` to
varieties is a classical Weil cohomology theory with `H^*(X) = G(h(X))`: conditions (1) and (2)
of `R` give axioms (A)(c) and (A)(d). -/
theorem ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory_of_iso
    (R : ClassicalMotiveRealization k F) (W : WeilDataAxioms k F) (θ : W.motiveFunctor ≅ R.G) :
    ∃ T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k),
      Nonempty (T.toPre.toPoincarePairingSetup.MotiveComparison R.G) := by
  let E := W.motiveComparison.mapIso θ
  exact ⟨W.toPreClassical.toClassicalOfNonneg
      (fun X i hi a ↦ E.eq_zero_of_isZero (R.nonneg X i hi) a)
      (fun X ↦ (E.finrank_eq X 0).trans (R.finrank_zero X)), ⟨E⟩⟩

/-- The converse direction of Stacks 0FH3 for a realization whose data (D0)–(D3) (Stacks 0FHK,
`WeilRealization.toWeilData`) are known to satisfy (A), (B), (C): by Lieberman's lemma the
realization is that of Stacks 0FHL for these data, so their restriction to varieties is a
classical Weil cohomology theory with `H^*(X) = G(h(X))`. -/
theorem ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory_of_axioms
    (R : ClassicalMotiveRealization k F) (hA : R.toWeilRealization.toWeilData.PoincareDuality)
    (hB : R.toWeilRealization.toWeilData.Kunneth)
    (hC : R.toWeilRealization.toWeilData.CycleClassAxiom hA.perfectPairing) :
    ∃ T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k),
      Nonempty (T.toPre.toPoincarePairingSetup.MotiveComparison R.G) := by
  obtain ⟨e⟩ := R.toWeilRealization.rel_toWeilRealization_of_nat hA hB hC
    (R.toWeilRealization.corrMapG_eq_corrHomMap hA hB hC)
  exact R.exists_classicalWeilCohomologyTheory_of_iso ⟨R.toWeilRealization.toWeilData, hA, hB, hC⟩
    e.iso.symm

/-- **The functor of a realization as in Stacks 0FH3 comes from a classical Weil cohomology
theory.** A `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories
with an isomorphism `F[2] ≅ G(𝟏(1))` such that `G(h(X))` lives in nonnegative degrees and
`dim_F G⁰(h(X)) = 1` for every smooth projective variety `X` gives a classical Weil cohomology
theory (Stacks 0FGV, over the Chow groups of Chapter 42) with `H^*(X) = G(h(X))` as graded vector
spaces, naturally in `X`. By Stacks 0FHK, `H^*(X) = G(h(X))` gives data (D0)–(D3) satisfying (A),
(B), (C) (`WeilRealization.toWeilDataAxioms`); conditions (1) and (2) give axioms (A)(c) and (A)(d)
on their restriction to varieties. The theory whose cycle classes and traces are those given by
`F[2] ≅ G(𝟏(1))`, and the correspondence of Stacks 0FH3 itself, are
`ClassicalMotiveRealization.toClassicalWeilCohomologyTheory` and
`ClassicalWeilCohomologyTheory.exists_isoClassEquiv`. -/
theorem ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory
    (R : ClassicalMotiveRealization k F) :
    ∃ T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k),
      Nonempty (T.toPre.toPoincarePairingSetup.MotiveComparison R.G) :=
  R.exists_classicalWeilCohomologyTheory_of_axioms R.toWeilRealization.poincareDuality
    R.toWeilRealization.kunneth R.toWeilRealization.cycleClassAxiom

end Stacks.WeilCohomology

end
