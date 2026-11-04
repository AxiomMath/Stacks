module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationBijection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationLiebermanBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationUntwistedIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData

/-!
# Weil data and realizations of Chow motives

Let `k` be a field and `F` a field of characteristic `0`. This file proves Stacks 0FHM: data
(D0)–(D3) satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilDataAxioms`) and `ℚ`-linear
symmetric monoidal functors `G : M_k ⥤ graded F-vector spaces` with `G(𝟏(1))` nonzero only in
degree `-2` (`Stacks.WeilCohomology.WeilRealization`) correspond bijectively, up to isomorphism,
through `G ↦ (H^*(X) = G(h(X)))` (Stacks 0FHK) and the construction of Stacks 0FHL.

By Lieberman's lemma (`Stacks.WeilCohomology.WeilRealization.corrMapG_eq_corrHomMap`) a realization
`G` acts on correspondences of degree zero as the realization of Stacks 0FHL attached to its data,
so `G` realizes its data (`Stacks.WeilCohomology.WeilRealization.realizes`), and
`Stacks.WeilCohomology.WeilDataAxioms.exists_quotientEquiv` gives the bijection
(`Stacks.WeilCohomology.WeilRealization.exists_isoClassEquiv`).

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology.WeilRealization

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)

/-- **A realization realizes its data**: the restriction of `G` to correspondences of degree zero
is monoidally isomorphic to the realization of Stacks 0FHL attached to `H^*(X) = G(h(X))`. -/
theorem realizes (hA : G.toWeilData.PoincareDuality) (hB : G.toWeilData.Kunneth)
    (hC : G.toWeilData.CycleClassAxiom hA.perfectPairing) :
    (⟨G.toWeilData, hA, hB, hC⟩ : WeilDataAxioms k F).Realizes G :=
  ⟨G.untwistedIso hA hB hC (G.corrMapG_eq_corrHomMap hA hB hC), inferInstance⟩

variable (k F) in
/-- **Stacks Project, Tag 0FHM.** Let `k` be a field and `F` a field of characteristic `0`.
Data (D0), (D1), (D2), (D3) satisfying (A), (B), (C) and `ℚ`-linear symmetric monoidal functors
`G : M_k ⥤ graded F-vector spaces` such that `G(𝟏(1))` is nonzero only in degree `-2` correspond
`1`-to-`1`, up to isomorphism: the bijection of isomorphism classes sends data `T` to the functor
of Stacks 0FHL (`Stacks.WeilCohomology.WeilDataAxioms.toWeilRealization`), and its inverse sends
`G` to the data `H^*(X) = G(h(X))` of Stacks 0FHK
(`Stacks.WeilCohomology.WeilRealization.toWeilDataAxioms`). -/
@[stacks 0FHM "for a field k and a field F of characteristic 0, data (D0)-(D3) satisfying
(A), (B), (C) correspond 1-to-1 (up to isomorphism) to Q-linear symmetric monoidal functors
G : M_k -> graded F-vector spaces with G(1(1)) nonzero only in degree -2"]
theorem exists_isoClassEquiv :
    ∃ e : Quotient (WeilDataAxioms.isoSetoid k F) ≃ Quotient (isoSetoid k F),
      (∀ T, e ⟦T⟧ = ⟦T.toWeilRealization⟧) ∧ ∀ G, e.symm ⟦G⟧ = ⟦G.toWeilDataAxioms⟧ :=
  WeilDataAxioms.exists_quotientEquiv toWeilDataAxioms fun G ↦
    G.realizes G.poincareDuality G.kunneth G.cycleClassAxiom

end Stacks.WeilCohomology.WeilRealization

end
