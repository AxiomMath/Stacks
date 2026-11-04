module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRestriction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Classical Weil cohomology data from a realization of Chow motives

Lemma 0FH1 of the Stacks Project: let `k` be an algebraically closed field and `F` a field of
characteristic `0`, and let `G : M_k ⥤ graded F-vector spaces` be a `ℚ`-linear functor of
symmetric monoidal categories with `G(𝟏(1))` nonzero only in degree `-2`
(`Stacks.WeilCohomology.WeilRealization`). Then `G` gives data (D1), (D2), (D3) satisfying all of
(A), (B), (C) except possibly (A)(c) and (A)(d), that is a
`Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory` over the Chow groups of Chapter 42.

The data are those of the proof:

* (D1) `H^*(X) = G(h(X))`, with pullbacks `G(h(f))` and cup product `G` of the multiplication
  `[Γ_Δ] : h(X) ⊗ h(X) ⟶ h(X)` (`Stacks.WeilCohomology.WeilRealization.cohAlg`);
* (D2) `γ(α) = G(a_α)(e_{-r}) ∈ G(h(X))^{2r}` for the correspondence `a_α : 𝟏(-r) ⟶ h(X)` of
  `α ∈ CH^r(X)` (Stacks 0FG0) and generators `e_n` of `G(𝟏(n)) = F[2n]`
  (`Stacks.WeilCohomology.ChowMotiveCat.cycleClassMotive`);
* (D3) `∫_X x = G([X])(x ⊗ e_d)` for the fundamental class `[X] : h(X)(d) ⟶ 𝟏`
  (`Stacks.WeilCohomology.ChowMotiveCat.fundamentalClassMot`).

The construction goes through the general one of Lemma 0FHK over all smooth projective schemes
(`Stacks.WeilCohomology.WeilRealization.toWeilDataAxioms`, whose axioms are proved in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData` from
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClass`,
`...MotiveCycleClassAxioms` and `...MotiveCycleClassMul`), restricted to smooth projective
varieties and read in the coordinate of `F(1) = G^{-2}(𝟏(1))`
(`Stacks.WeilCohomology.WeilDataAxioms.toPreClassical`).

## Main definitions

* `Stacks.WeilCohomology.WeilRealization.toPreClassical`: **Lemma 0FH1**.
* `Stacks.WeilCohomology.WeilRealization.toPreClassicalPieceEquiv`: `H^n(X) = G(h(X))^n`.

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilRealization

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
  CorrespondenceCategory _)

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type w} [Field F] [CharZero F]
  (G : WeilRealization k F)

/-- **Stacks Project, Lemma 0FH1.** Let `k` be algebraically closed and `F` of characteristic
`0`. A `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories
with `G(𝟏(1))` nonzero only in degree `-2` gives data (D1), (D2), (D3) satisfying all of (A),
(B), (C) except possibly (A)(c) and (A)(d): on a smooth projective variety `X`,
`H^*(X) = G(h(X))`, the cycle class map is `α ↦ G(a_α)(e_{-r})` and the trace is
`x ↦ G([X])(x ⊗ e_d)`, for generators `e_n` of `G(𝟏(n))` with `e_1` a basis of `G^{-2}(𝟏(1))`. -/
@[stacks 0FH1 "a Q-linear functor G : M_k → graded F-vector spaces of symmetric monoidal \
categories with G(1(1)) nonzero only in degree -2 gives data (D1), (D2), (D3) satisfying (A), \
(B), (C) except possibly (A)(c) and (A)(d)"]
def toPreClassical : PreClassicalWeilCohomologyTheory.{u, w, w, u} k F (chowCycleData k) :=
  G.toWeilDataAxioms.toPreClassical

/-- **`H^n(X) = G(h(X))^n`** for the data of Lemma 0FH1. -/
def toPreClassicalPieceEquiv (X : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    (G.toPreClassical.H X).piece n ≃ₗ[F]
      (G.functor.obj (CategoryTheory.GradedCategory.TwistedKaroubi.ofObj (R := ℚ)
        (𝐎 ((SmoothProjective.toSchemeCat k).obj X)))) n :=
  (G.cohAlg ((SmoothProjective.toSchemeCat k).obj X)).gradeEquiv n

/-- **The cycle class map of Lemma 0FH1 is `α ↦ G(a_α)(e_{-r})`** in `G(h(X))^{2r}`. -/
theorem toPreClassicalPieceEquiv_cycleClass (X : (SmoothProjective k).FullSubcategory) (r : ℤ)
    (α : (chowCycleData k).group X r) :
    G.toPreClassicalPieceEquiv X (2 * r) (G.toPreClassical.cycleClass X r α) =
      ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen
        ((SmoothProjective.toSchemeCat k).obj X) r α := by
  have h := G.toWeilData_cycleClassCoord ((SmoothProjective.toSchemeCat k).obj X) r α
  exact (congrArg (G.toPreClassicalPieceEquiv X (2 * r)) h).trans
    (((G.cohAlg _).gradeEquiv (2 * r)).apply_symm_apply _)

end Stacks.WeilCohomology.WeilRealization

end
