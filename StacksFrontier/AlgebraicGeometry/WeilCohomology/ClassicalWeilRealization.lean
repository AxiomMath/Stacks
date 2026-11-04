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
(`Stacks.WeilCohomology.PoincarePairingSetup.MotiveComparison`).

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_classicalMotiveRealization`: a
  classical Weil cohomology theory comes from such a realization (the second paragraph of the
  proof of Stacks 0FH3, through Stacks 0FH2).
* `Stacks.WeilCohomology.ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory`:
  conversely, such a realization comes from a classical Weil cohomology theory (the first
  paragraph of the proof, through Stacks 0FHK).

Together these are Stacks 0FH3; the comparison `H^*(X) = G(h(X))` is natural in `X`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

/-- **Stacks Project, Tag 0FH3, from cohomology to a realization.** A classical Weil cohomology
theory `H^*` (Stacks 0FGV, over the Chow groups of Chapter 42) comes from a realization of Chow
motives: there is a `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal
categories with an isomorphism `F[2] ≅ G(𝟏(1))`, `G(h(X))` in nonnegative degrees and
`dim_F G⁰(h(X)) = 1` for every smooth projective variety `X`, and `H^*(X) = G(h(X))` naturally in
`X`. The functor is that of Stacks 0FH2 (`ClassicalWeilCohomologyTheory.motiveFunctor`);
`G(𝟏(1))` is a line in degree `-2`, and conditions (1), (2) are axioms (A)(c), (A)(d) and
Poincaré duality transported along `H^*(X) = G(h(X))`. -/
@[stacks 0FH3 "a classical Weil cohomology theory comes from a Q-linear symmetric monoidal \
G : M_k → graded F-vector spaces with F[2] ≅ G(1(1)), G(h(X)) in nonnegative degrees and \
dim G⁰(h(X)) = 1, with H^*(X) = G(h(X)) naturally in X"]
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

/-- **Stacks Project, Tag 0FH3, from a realization to cohomology.** Conversely, a `ℚ`-linear
functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories with an isomorphism
`F[2] ≅ G(𝟏(1))` such that `G(h(X))` lives in nonnegative degrees and `dim_F G⁰(h(X)) = 1` for
every smooth projective variety `X` comes from a classical Weil cohomology theory (Stacks 0FGV,
over the Chow groups of Chapter 42): there is one with `H^*(X) = G(h(X))` naturally in `X`. By
Stacks 0FHK, `H^*(X) = G(h(X))` gives data (D0)–(D3) satisfying (A), (B), (C)
(`WeilRealization.toWeilDataAxioms`); conditions (1) and (2) give axioms (A)(c) and (A)(d) on
their restriction to varieties. -/
@[stacks 0FH3 "a Q-linear symmetric monoidal G : M_k → graded F-vector spaces with \
F[2] ≅ G(1(1)), G(h(X)) in nonnegative degrees and dim G⁰(h(X)) = 1 comes from a classical Weil \
cohomology theory, with H^*(X) = G(h(X)) naturally in X"]
theorem ClassicalMotiveRealization.exists_classicalWeilCohomologyTheory
    (R : ClassicalMotiveRealization k F) :
    ∃ T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k),
      Nonempty (T.toPre.toPoincarePairingSetup.MotiveComparison R.G) :=
  R.exists_classicalWeilCohomologyTheory_of_axioms R.toWeilRealization.poincareDuality
    R.toWeilRealization.kunneth R.toWeilRealization.cycleClassAxiom

end Stacks.WeilCohomology

end
