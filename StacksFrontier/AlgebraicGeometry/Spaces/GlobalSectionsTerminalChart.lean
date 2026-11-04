module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom

/-!
# The global functions of an algebraic space at a terminal chart

The ring of global regular functions of an algebraic space `X` is a subring of a product indexed
by the objects of the small étale site of `X`, which lie one universe above the sections
themselves: for schemes in `Scheme.{u}` the sections lie in `Type u` but
`RingCat.sectionsSubring (structureRingSheaf X).obj` lies in `Type (u + 1)`.  When `X` has a
*terminal* étale chart `V` — as an affine algebraic space does — evaluation at `V` identifies that
ring with the ring `Γ(chartScheme V, ⊤)` of regular functions on a single scheme, which lies in
`Type u`.

This file records that identification as a ring equivalence, and records that an affine algebraic
space has a terminal chart whose scheme is affine.

## Main results

* `AlgebraicGeometry.Space.globalSectionsChartRingEquiv`: **evaluation at a terminal chart is a
  ring equivalence** `Γ(X, 𝒪_X) ≃+* Γ(chartScheme V, ⊤)`.
* `AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`: **an affine algebraic space has a
  terminal étale chart, and the scheme of that chart is affine.**

## Implementation notes

Terminality is wrapped in `Nonempty` in the existence statement because `IsTerminal` is data.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Evaluation of global regular functions at a terminal étale chart is a ring equivalence.**

The underlying map is `AlgebraicGeometry.Space.globalSectionsChartEval`. Its target is the ring
of regular functions on a single scheme, so it lies in the universe of the schemes. -/
def globalSectionsChartRingEquiv (X : AlgebraicSpaces B S hS) {V : SmallEtale B S hS X.1}
    (hV : IsTerminal V) :
    RingCat.sectionsSubring (structureRingSheaf B S hS X).obj ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V), ⊤) :=
  RingEquiv.ofBijective (globalSectionsChartEval B S hS X V)
    (bijective_globalSectionsChartEval_of_isTerminal B S hS X hV)

/-- `AlgebraicGeometry.Space.globalSectionsChartRingEquiv` sends a global function to its value
`AlgebraicGeometry.Space.globalSectionsChartEval` at the terminal chart. -/
@[simp]
theorem globalSectionsChartRingEquiv_apply (X : AlgebraicSpaces B S hS)
    {V : SmallEtale B S hS X.1} (hV : IsTerminal V)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    globalSectionsChartRingEquiv B S hS X hV a = globalSectionsChartEval B S hS X V a :=
  rfl

/-- **An affine algebraic space has a terminal étale chart whose scheme is affine.** -/
theorem exists_isTerminal_isAffine_chart (X : AlgebraicSpaces B S hS)
    (hX : IsAffineSpace B S hS X.1) :
    ∃ V : SmallEtale B S hS X.1, Nonempty (IsTerminal V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hX
  exact ⟨etaleChartOfIso B S hS e, ⟨isTerminalEtaleChartOfIso B S hS e⟩, hT⟩

end AlgebraicGeometry.Space

end

end
