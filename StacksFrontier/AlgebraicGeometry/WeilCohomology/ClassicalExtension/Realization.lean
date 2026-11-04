module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealizationExtension

/-!
# Stacks 0FH2: the realization of Chow motives attached to a classical Weil cohomology theory

Let `k` be algebraically closed, `F` a field of characteristic zero and `H^*` a classical Weil
cohomology theory (Stacks 0FGV). Stacks 0FH2 constructs a `ℚ`-linear functor of symmetric
monoidal categories `G : M_k ⥤ graded F-vector spaces` with `H^*(X) = G(h(X))`.

The source builds `G` on smooth projective varieties and correspondences of degree zero, using
that "every smooth projective scheme is canonically a disjoint union of smooth projective
varieties (some details omitted)". Here those details are the extension of `H^*` to all smooth
projective schemes, `H^*(X) = ∏_c H^*(X_c)` over the connected components, which satisfies
axioms (A), (B), (C) of Section 0FHA
(`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilDataAxioms`) and agrees with `H^*` on
varieties (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyGradeEquiv`). The
construction of `G` from such data is the one of Stacks 0FHL, whose proof the source says is the
same as that of 0FH2 (`Stacks.WeilCohomology.WeilDataAxioms.exists_motiveFunctor`).

The functor `G` is `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.motiveFunctor` and the
identification of the extended cohomology of varieties with `H^*` is
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.restrictCohomologyIso`, both in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealizationExtension`.

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.motiveFunctorCohomologyIso`:
  `H^*(X) = G(h(X))`, naturally in the variety `X`.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_motiveFunctor`: **Stacks 0FH2**.

## References

* [Stacks Project, Tag 0FH2](https://stacks.math.columbia.edu/tag/0FH2)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

namespace Stacks.WeilCohomology.ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-- **`H^*(X) = G(h(X))`**, naturally in the smooth projective variety `X`. -/
def motiveFunctorCohomologyIso :
    (SmoothProjective.toSchemeCat k).op ⋙ ChowMotiveCat.h k ⋙ T.motiveFunctor ≅
      T.toPre.toPoincarePairingSetup.cohomologyFunctor :=
  Functor.isoWhiskerLeft _ (WeilData.motiveFunctorCohomologyIso _ _ _) ≪≫ T.restrictCohomologyIso

/-- **Stacks Project, Tag 0FH2.** Let `k` be an algebraically closed field, `F` a field of
characteristic zero and `H^*` a classical Weil cohomology theory. Then there is a `ℚ`-linear
functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories (for the
Koszul-signed symmetry of Stacks, Homology, Example 0FFX) with `H^*(X) = G(h(X))`, naturally in
the smooth projective variety `X` (pullbacks `f^*` corresponding to `G(h(f))`). -/
@[stacks 0FH2 "a classical Weil cohomology theory gives a Q-linear symmetric monoidal functor
G : M_k -> graded F-vector spaces with H^*(X) = G(h(X))"]
theorem exists_motiveFunctor :
    ∃ (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F))
      (_ : @Functor.Braided (ChowMotiveCat k) _ _ _ (GradedObject ℤ (ModuleCat.{v} F)) _ _
        GradedObject.koszulBraidedCategory G) (_ : G.Additive) (_ : Functor.Linear ℚ G),
      Nonempty ((SmoothProjective.toSchemeCat k).op ⋙ ChowMotiveCat.h k ⋙ G ≅
        T.toPre.toPoincarePairingSetup.cohomologyFunctor) :=
  ⟨T.motiveFunctor, WeilData.motiveFunctorBraided _ _ _, inferInstance, inferInstance,
    ⟨T.motiveFunctorCohomologyIso⟩⟩

end Stacks.WeilCohomology.ClassicalWeilCohomologyTheory

end
