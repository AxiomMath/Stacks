module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponent
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence

/-!
# The contraction of an exceptional component exists

In the situation of [Stacks, Tag 0C61] let the component `C_n` of the special fibre be an
exceptional curve of the first kind. The first sentence of the proof of [Stacks, Tag 0C6C]: the
contraction `f : X ⟶ X'` of `C_n` exists. The model is projective over `R` by
[Stacks, Tag 0C5P], so [Stacks, Tag 0C2M] (in the form of [Stacks, Tag 0C2N]) contracts `C_n`.
The remaining assertions of [Stacks, Tag 0C6C] are stated for every contraction in
`ContractExceptionalComponent.lean` and its companions.

## Main results

* `exists_isContractionOfExceptionalCurve_specialFiberComponentIdeal`: an irreducible component
  of the special fibre which is an exceptional curve of the first kind admits a contraction.

## References

* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **Stacks Project, Tag 0C6C, the contraction.** In Situation 0C61, an irreducible component
`C_n` of the special fibre which is an exceptional curve of the first kind can be contracted:
there is a contraction `f : X ⟶ X'` of `C_n`. -/
@[stacks 0C6C "the contraction f : X -> X' of the exceptional component C_n exists"]
theorem exists_isContractionOfExceptionalCurve_specialFiberComponentIdeal
    (N : irreducibleComponents S.specialFiber) {κ : Type u} [Field κ]
    {e : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal N).subscheme}
    (hN : (S.specialFiberComponentIdeal N).IsExceptionalCurveOfFirstKind κ e) :
    ∃ (X' : Scheme.{u}) (f : S.X ⟶ X'),
      IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f := by
  have hmod : IsModel S.C_to_K S.X_to_R S.genericFiberIso :=
    ⟨S.flat, S.locallyOfFiniteType, S.quasiCompact, S.genericFiberIso_over_K⟩
  obtain ⟨X', b, -, -, hb, -⟩ := exists_isContractionOfExceptionalCurve_isModel S.C_to_K S.X_to_R
    S.genericFiberIso hmod
    (isProjective_of_isModel_of_isRegular S.C_to_K S.X_to_R S.genericFiberIso hmod S.regular)
    S.regular hN
  exact ⟨X', b, hb⟩

end Stacks.Models.RegularProperModelSituation

end
