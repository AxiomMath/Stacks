module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits

/-!
# Bounded base changes of a descent situation

In the situation of Stacks 084R the limits of the affine charts `X_j ×_{X_i} U` of the stages
along an affine point `U ⟶ X_i` remain in the big fppf site exactly when those charts are
bounded below the site's cutoff, `AlgebraicGeometry.Space.HasBoundedBaseChanges`. This file
records the two ways a descent situation meets that condition.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.hasBoundedBaseChanges_of_lt_cof`: an index set small
  compared to the cofinality of the cutoff.
* `AlgebraicGeometry.Space.DescentSituation.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE`: an
  index set below the cutoff together with transition morphisms enlarging affine schemes by a
  bounded amount only, as closed immersions and finite morphisms do. This one needs no condition
  on the cofinality of the cutoff, which may be singular.

## Implementation notes

The index of a descent situation is a preorder, so its morphism sets have at most one element and
the stages beyond a given one are at most as many as the index set.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

omit [IsDirected I (· ≤ ·)] in
/-- The stages of a preorder beyond a given one are at most as many as the preorder: the slice of
the opposite category over `op i` injects into the index, its morphism sets having at most one
element. -/
theorem mk_over_op_le (i : I) : Cardinal.mk (Over (op i)) ≤ Cardinal.mk I :=
  ((mk_over_le (op i)).trans (Cardinal.mk_le_of_injective Sigma.fst_injective)).trans_eq
    (Cardinal.mk_congr equivToOpposite.symm)

/-- **A descent situation indexed below the cofinality of the cutoff has bounded base
changes** at every stage (`AlgebraicGeometry.Space.hasBoundedBaseChanges_of_lt_cof`): the index
is a preorder, so its morphism sets have at most one element. -/
theorem DescentSituation.hasBoundedBaseChanges_of_lt_cof (D : DescentSituation B S hS hZ I)
    (hI : Cardinal.mk I < B.cutoff.ord.cof) (i : I) :
    HasBoundedBaseChanges B S hS (op i) D.system :=
  Space.hasBoundedBaseChanges_of_lt_cof B S hS _ _ (fun f => D.transition_affine f)
    (by rwa [Cardinal.mk_congr equivToOpposite.symm])
    (fun _ _ => (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof))

/-- **A descent situation indexed below the cutoff whose transition morphisms have base changes of
bounded growth has bounded base changes** at every stage
(`AlgebraicGeometry.Space.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE`): the stages above a
given one are at most as many as the index set, the index being a preorder. No condition on the
cofinality of the cutoff is needed, so this covers an index set of any size below a singular
cutoff. -/
theorem DescentSituation.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE
    (D : DescentSituation B S hS hZ I) (hI : Cardinal.mk I < B.cutoff) {ν : Cardinal.{u}}
    (hν : ν < B.cutoff)
    (htr : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), HasBaseChangesOfSizeLE B S hS ν (D.system.map f))
    (i : I) : HasBoundedBaseChanges B S hS (op i) D.system :=
  Space.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE B S hS _ _
    ((mk_over_op_le i).trans_lt hI) hν htr

end AlgebraicGeometry.Space

end
