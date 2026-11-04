module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# Descending an operation on cycles through rational equivalence

In the situation of Stacks 0EDT let `X/B` be good and let `k ∈ ℤ`.  The Chow group `CH_k(X)` of
Stacks 0EQ6, part (4), is by construction the quotient of `Z_k(X)` by the subgroup
`AlgebraicGeometry.Space.rationalEquivalences` of cycles rationally equivalent to zero, so an
additive operation `F : Z_k(X) ⟶ A` which kills every cycle rationally equivalent to zero
descends to `CH_k(X) ⟶ A`.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupLift`: the descended operation `CH_k(X) ⟶ A`.

## Main results

* `AlgebraicGeometry.Space.chowGroupLift_chowClass` and
  `AlgebraicGeometry.Space.chowGroupLift_comp_chowClass`: the descended operation agrees with the
  original one on classes of cycles.
* `AlgebraicGeometry.Space.eq_zero_of_isRationallyEquivalentToZero`: the hypothesis of the
  descent reduced to the family of Stacks 0EQ6, part (1): it is enough to kill the cycles
  `∑ (i_j)_* div(f_j)` themselves.
* `AlgebraicGeometry.Space.map_eq_of_rationallyEquivalent`: an operation which kills the cycles
  rationally equivalent to zero takes equal values on rationally equivalent cycles.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {A : Type w} [AddCommGroup A]

/-- **It is enough to kill the cycles `∑ (i_j)_* div(f_j)` of Stacks 0EQ6, part (1).**  An
additive operation on `Z_k(X)` which vanishes on every locally finite sum of principal divisors
on integral closed subspaces of δ-dimension `k + 1` vanishes on every cycle rationally
equivalent to zero, because by Stacks 0EQ6, part (2), those sums are exactly the cycles
rationally equivalent to zero. -/
theorem eq_zero_of_isRationallyEquivalentToZero (F : CycleGroup D sX k →+ A)
    (hF : ∀ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hWfin : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem X (W j).subspace)
      (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
      (∀ j, deltaDimension D sX (W j) = k + 1) →
      (∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j)) →
      F (cycleFamilySum D sX hX W hWfin k c) = 0)
    (α : CycleGroup D sX k) (hα : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    F α = 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := hα
  rw [hWsum]
  exact hF J W hWfin c hWdim hWprin

/-- **An operation on cycles which kills rational equivalence descends to the Chow group.**  In
the situation of Stacks 0EDT let `X/B` be good, let `F : Z_k(X) ⟶ A` be additive and suppose
`F α = 0` for every `k`-cycle `α` rationally equivalent to zero.  Then `F` factors through the
quotient `CH_k(X) = Z_k(X)/∼_rat` of Stacks 0EQ6, part (4), giving an operation
`CH_k(X) ⟶ A`.

This is the universal property of the quotient at the subgroup
`AlgebraicGeometry.Space.rationalEquivalences`, whose membership is being rationally equivalent
to zero. -/
def chowGroupLift (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k, IsRationallyEquivalentToZero.{v} D sX hX k α → F α = 0) :
    chowGroup.{v} D sX hX k →+ A :=
  QuotientAddGroup.lift (rationalEquivalences.{v} D sX hX k) F hF

/-- The descended operation `AlgebraicGeometry.Space.chowGroupLift` agrees with the original one
on the class of a cycle. -/
@[simp]
theorem chowGroupLift_chowClass (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k, IsRationallyEquivalentToZero.{v} D sX hX k α → F α = 0)
    (α : CycleGroup D sX k) :
    chowGroupLift.{u, v} D sX hX k F hF (chowClass.{v} D sX hX k α) = F α :=
  rfl

/-- The descended operation composed with the class map `Z_k(X) ⟶ CH_k(X)` is the original
operation. -/
theorem chowGroupLift_comp_chowClass (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k, IsRationallyEquivalentToZero.{v} D sX hX k α → F α = 0) :
    (chowGroupLift.{u, v} D sX hX k F hF).comp (chowClass.{v} D sX hX k) = F :=
  AddMonoidHom.ext fun α => chowGroupLift_chowClass.{u, v} D sX hX k F hF α

/-- An additive operation on `Z_k(X)` which kills the cycles rationally equivalent to zero takes
the same value on two rationally equivalent cycles, their difference being rationally equivalent
to zero. -/
theorem map_eq_of_rationallyEquivalent (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k, IsRationallyEquivalentToZero.{v} D sX hX k α → F α = 0)
    {α β : CycleGroup D sX k} (h : RationallyEquivalent.{v} D sX hX k α β) :
    F α = F β :=
  sub_eq_zero.1 ((map_sub F α β).symm.trans (hF _ h))

end AlgebraicGeometry.Space

end
