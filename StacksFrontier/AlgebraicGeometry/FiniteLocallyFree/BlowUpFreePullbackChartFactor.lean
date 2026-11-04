module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChart
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChartTarget

/-!
# The chart comparison as a trivialisation of `b^*N` against the trivialisation of `𝒢`

`AlgebraicGeometry.pullbackFreeChartCompIso` compares the restriction of `b^*N` to the preimage of
an open `W` on which `N` is trivialised with the restriction of `𝒢` there.  It is written as four
comparisons followed by the restriction of `α`, and its last two factors --
`Stacks.Modules.restrictFreeIso` undone, then `α` -- are exactly the inverse of
`AlgebraicGeometry.freeChartTargetIso`, the trivialisation of `𝒢` over the preimage given by `α`.

This file records that factorisation.  It matters because the two halves shrink for completely
different reasons, and only one of them is still open:  the trivialisation of `𝒢` shrinks by
`AlgebraicGeometry.restrictChartIso_freeChartTargetIso`, which is proved, so a shrink of the chart
comparison has to supply nothing beyond a shrink of the **trivialisation of `b^*N`** -- the three
remaining factors, which never mention `𝒢` or `α`.

## Main results

* `AlgebraicGeometry.pullbackFreeChartCompIso_eq`: **the chart comparison is the trivialisation of
  `b^*N` over the preimage of `W` followed by the inverse of the trivialisation of `𝒢` there.**

## Implementation notes

The statement is an equation between isomorphisms whose two sides are the same five factors
bracketed differently, so `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` occur on both sides and nothing is unfolded:
`CategoryTheory.Iso.ext` and the associativity of composition finish it.  This is deliberate --
the transparency obstruction recorded in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/RestrictFreeIsoComp.lean` makes any statement
about a free module on a scheme unrewritable, so the reassociation is applied by hand in term
mode.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {I : Type u} {G : X'.Modules}
  (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- **The trivialisation of the restriction of `b^*N` to the preimage of an open `W` of `X` on
which `N` is trivialised by `τ`.**  The restriction of `b^*N` to `b ⁻¹ᵁ W` is the inverse image
along `b ∣_ W` of the restriction of `N` to `W`, that is free by `τ`, and the inverse image of a
free module is free.

This is `AlgebraicGeometry.pullbackFreeChartIso` with its last factor -- the comparison of the
free module on `b ⁻¹ᵁ W` with the restriction of the free module on `X'` -- left off, so that it
is a trivialisation by the free module on the open subscheme and not by a restriction. -/
def pullbackFreeTrivIso (W : X.Opens) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N) (b ⁻¹ᵁ W).ι ≅
      _root_.SheafOfModules.free (R := (b ⁻¹ᵁ W).toScheme.ringCatSheaf) I :=
  restrictPullbackPreimageIso b W N ≪≫
    (Scheme.Modules.pullback (b ∣_ W)).mapIso τ ≪≫
    Scheme.Modules.pullbackFreeIso (b ∣_ W) I

/-- **The chart comparison is the trivialisation of `b^*N` over the preimage of `W` followed by
the inverse of the trivialisation of `𝒢` there.**

Both sides are the same five comparisons in the same order; the two sides differ only in where the
trivialisation of `b^*N` is cut off from the trivialisation of `𝒢`, which is the inverse of
`Stacks.Modules.restrictFreeIso` followed by the restriction of `α`. -/
theorem pullbackFreeChartCompIso_eq (W : X.Opens) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W).ι).map α)) :
    pullbackFreeChartCompIso b α W N τ hα =
      pullbackFreeTrivIso b W N τ ≪≫ (freeChartTargetIso α (b ⁻¹ᵁ W) hα).symm :=
  Iso.ext
    ((Category.assoc _ _ _).trans
      (congrArg ((restrictPullbackPreimageIso b W N).hom ≫ ·)
        ((Category.assoc _ _ _).trans
          (congrArg ((Scheme.Modules.pullback (b ∣_ W)).map τ.hom ≫ ·)
            (Category.assoc _ _ _)))))

end AlgebraicGeometry

end
