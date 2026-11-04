module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Flat pullback of the cycle of an integral closed subscheme

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project and let `f : X' ⟶ X` be flat of relative dimension `r`. Stacks 02RB has two
halves: the construction of the flat pullback homomorphism `Z_k(X) ⟶ Z_{k+r}(X')`, and the
assertion that it agrees with the componentwise description, namely that the pullback of the
cycle `[Z]_k` of an integral closed subscheme `i : Z ⟶ X` of delta-dimension `k` is the cycle
`[X' ×_X Z]_{k+r}` of its scheme-theoretic inverse image. This file proves the second half for
the flat pullback `Stacks.Chow.flatPullback`, with the scheme-theoretic inverse image taken as the
pullback `pullback.fst f i`.

## Main results

* `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme`: the flat pullback of the cycle of
  an integral closed subscheme is the cycle of its scheme-theoretic inverse image.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The flat pullback of the cycle of an integral closed subscheme
`i : Z ⟶ X` of delta-dimension `k` is the cycle of delta-dimension `k + r` of its
scheme-theoretic inverse image `X' ×_X Z`. -/
@[stacks 02RB "pullback of an integral closed subscheme"]
theorem flatPullback_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {X' X Z : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : schemeDeltaDimension C (i ≫ sX) = (k : EInt)) :
    flatPullback C sX' sX f hbase r hf k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sX' (pullback.fst f i) (k + (r : ℤ)) := by
  have hdim : relativeDimension C.dimensionFunction sX (i (genericPoint Z)) = k :=
    (relativeDimension_comp_closedImmersion C.dimensionFunction i sX (genericPoint Z)).symm.trans
      (WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C (i ≫ sX)).symm.trans hZ))
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun x => ?_
  rw [flatPullback_apply]
  by_cases hx : f x = i (genericPoint Z)
  · rw [hx, cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint C sX i k hdim,
      one_mul, flatPullbackWeight,
      closedSubschemeCycleCoeff_comap_eq_pullbackFst C sX' f i (k + (r : ℤ)) x hx]
    rfl
  · rw [cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne C sX i k hx, zero_mul]
    exact (closedSubschemeCycleCoeff_pullbackFst_eq_zero C sX' sX f i (k + (r : ℤ)) x hx).symm

end Stacks.Chow

end
