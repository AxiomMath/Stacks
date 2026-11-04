module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes: clauses (1), (5) and (9) of Stacks tag 0F9Y, clause (1) unconditionally

`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_and_isPerfect_and_exists_rep`
takes the representability of `M` by a locally bounded complex of finite locally free modules as
a hypothesis for all three clauses. Clause (1) needs no such hypothesis, and the source's own
closing sentence puts the representability as an antecedent of clauses (5) and (9) only. This
file states the three clauses in that shape.

## Main results

* `ComplexAndDivisorSituation.IsGoodBlowup.isIso_and_imp_isPerfect_and_exists_rep`:
  `b` is an isomorphism over `X ∖ D`, and if `M` is represented by a locally bounded complex of
  finite locally free modules, then `Q` is perfect and is represented by such a complex.

## References

* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GU0](https://stacks.math.columbia.edu/tag/0GU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : ComplexAndDivisorSituation.{u, d}}

namespace IsGoodBlowup

variable {X' : Scheme.{u}} {b : X' ⟶ S.X}

/-- Let `b : X' ⟶ X` have properties (1) and (2) of Stacks tag 0GTY for a triple `(X, D, M)`.
Then `b` is an isomorphism over `X ∖ D`, and if `M` is represented by a locally bounded complex
of finite locally free `𝒪_X`-modules, then `Q = Lη_{ℐ'}Lb^*M` is a perfect object of
`D(𝒪_{X'})` and is itself represented by a locally bounded complex of finite locally free
`𝒪_{X'}`-modules. -/
@[stacks 0F9Y "parts (1), (5) and (9) for any `b` with properties (1) and (2) of tag 0GTY: \
part (1) outright, and parts (5) and (9) in the shape of the source's own closing sentence --- \
if `M` is represented by a locally bounded complex of finite locally free modules, then so is \
`Q`, and `Q` is then perfect"]
theorem isIso_and_imp_isPerfect_and_exists_rep (hb : S.IsGoodBlowup b) :
    IsIso (b.resLE S.divisorComplement (b ⁻¹ᵁ S.divisorComplement) le_rfl) ∧
      ((∃ ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
          Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
            Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)) →
        RingedSpace.IsPerfect (X := X'.toRingedSpace)
            (S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined) ∧
          ∃ 𝒬 : CochainComplex X'.Modules ℤ,
            Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
              Nonempty (DerivedCategory.Q.obj 𝒬 ≅
                S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined)) :=
  ⟨hb.isIso_resLE_divisorComplement, fun hrep => (hb.isIso_and_isPerfect_and_exists_rep hrep).2⟩

end IsGoodBlowup

end AlgebraicGeometry.ComplexAndDivisorSituation

end
