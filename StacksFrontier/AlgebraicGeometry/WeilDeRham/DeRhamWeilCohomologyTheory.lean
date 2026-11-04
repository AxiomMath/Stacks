module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheoryOfWeilChern
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamTraceAxioms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamKunnethAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamGlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamProjectiveBundleAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBlowupAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilCoproductAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilPullbackAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilDivisorAxiom

/-!
# De Rham cohomology is a Weil cohomology theory (Proposition 0FWD)

Let `k` be a field of characteristic zero. Proposition 0FWD of the Stacks project says that the
functor `X ↦ H^*_{dR}(X/k)` on smooth projective schemes over `k` is a Weil cohomology theory in
the sense of Definition 0FI2, with coefficients `F = k`.

The proof is the source's. The de Rham data (D0), (D1), (D2') of Section 0FWC are
`Stacks.DeRhamWeil.deRhamFirstChernClassData k`: the Tate line `F(1) = k`, the functor
`X ↦ H^*_{dR}(X/k)` with its cup product and pullbacks, and the de Rham first Chern class
`c₁^{dR}`. They satisfy the axioms (A1) – (A8) of Section 0FID:

* (A1) `Stacks.DeRhamWeil.coproductAxiom`, (A2) `Stacks.DeRhamWeil.pullbackAxiom`,
  (A4) `Stacks.DeRhamWeil.divisorAxiom` (Tag 0FMX);
* (A3) `Stacks.WeilDeRham.deRham_projectiveBundleAxiom` (Tag 0FMT);
* (A5) `Stacks.WeilDeRham.deRham_kunnethAxiom` (Tag 0FMB);
* (A6) `Stacks.WeilDeRham.deRham_traceAxiom`, over an algebraic closure and then over `k` by
  Lemma 0FVT;
* (A7) `Stacks.WeilDeRham.deRham_blowupAxiom` (Tag 0FUW);
* (A8) `Stacks.WeilDeRham.deRham_globalSectionsAxiom`.

By (A1) – (A4) the de Rham data have a cohomological Chern character `ch` (Tag 0FIE, unique),
whose cycle class map `γ` is that of Lemma 0FIF; the data of Section 0FHA they define are
`h.toWeilData …` (`F(1)`, `H^*`, the cup product and the pullbacks of the de Rham data, `γ`, and
the trace maps `λ` of (A6)), the data `𝔚.toWeilData` of the bundle `𝔚 : WeilChernData k k` of
(A1) – (A7). Proposition 0FIU (`Stacks.WeilCohomology.WeilChernData.exists_weilCohomologyTheory`,
under (A1) – (A8)) makes them a Weil cohomology theory.

## Main results

* `Stacks.WeilDeRham.exists_weilCohomologyTheory_deRham`: **Proposition 0FWD**.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Tag 0FIU](https://stacks.math.columbia.edu/tag/0FIU)
* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.WeilCohomology Stacks.DeRhamWeil

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-- **Stacks Project, Proposition 0FWD**: for a field `k` of characteristic zero, the functor
`X ↦ H^*_{dR}(X/k)` on smooth projective schemes over `k` is a Weil cohomology theory over `k`
with coefficients in `k` (Definition 0FI2).

Formulation: there is a Weil cohomology theory `W : WeilCohomologyTheory k k` (Definition 0FI2:
data (D0) – (D3) satisfying (A), (B), (C) and condition (2) of Lemma 0FI0) whose data (D0) – (D3)
are those of de Rham cohomology. These are `h.toWeilData …` for `h` a cohomological Chern
character (Tag 0FIE) of the de Rham data `deRhamFirstChernClassData k` of Section 0FWC, so that
* (D0) `F(1)` is `k`;
* (D1) `H^*(X)` is `H^*_{dR}(X/k)`, with its grading, cup product and pullbacks
  (`W.H`, `W.grade`, the ring structure and `W.pull` are those of `deRhamFirstChernClassData k`);
* (D2) the cycle class map `γ` is the one of Lemma 0FIF built from the de Rham first Chern class
  `c₁^{dR}` (the Chern character `ch` is determined by `c₁^{dR}`,
  `FirstChernClassData.existsUnique_isCohomologicalChernCharacter`);
* (D3) `∫_X` is the trace map `λ_X` of axiom (A6), normalised by `(1 ⊗ λ_X)γ([Δ]) = 1`.

The proof assembles axioms (A1) – (A8) for de Rham cohomology and applies Proposition 0FIU. -/
@[stacks 0FWD "de Rham cohomology over a field of characteristic zero is a Weil cohomology \
theory (Definition 0FI2, coefficients k), with data (D0)-(D3) those of de Rham cohomology: \
F(1) = k, H^* = H^*_dR(-/k) with cup product and pullbacks, gamma from c_1^dR (0FIF), trace \
lambda of (A6)"]
theorem exists_weilCohomologyTheory_deRham [CharZero k] :
    ∃ W : WeilCohomologyTheory k k, ∃ ch,
      ∃ h : (deRhamFirstChernClassData k).IsCohomologicalChernCharacter ch,
        W.toWeilData = h.toWeilData coproductAxiom deRham_projectiveBundleAxiom
          (deRham_kunnethAxiom k) (deRham_traceAxiom h) := by
  have h := (deRhamFirstChernClassData k).isCohomologicalChernCharacter_chernCharacterOf
    coproductAxiom pullbackAxiom deRham_projectiveBundleAxiom divisorAxiom
  obtain ⟨W, hW⟩ := WeilChernData.exists_weilCohomologyTheory
    { toFirstChernClassData := deRhamFirstChernClassData k
      coproduct := coproductAxiom
      pullback := pullbackAxiom
      projectiveBundle := deRham_projectiveBundleAxiom
      divisor := divisorAxiom
      kunneth := deRham_kunnethAxiom k
      trace := deRham_traceAxiom h
      blowup := deRham_blowupAxiom } (deRham_globalSectionsAxiom k)
  exact ⟨W, _, h, hW⟩

end Stacks.WeilDeRham

end
