module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension

/-!
# The dimension bound of Stacks 0FVI (1) at the other projection

`Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_le` of
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension` is **Stacks 0FVI, part (1),
dimension bound**: in the flat base-change situation of Stacks 0FVG, the base change of a closed
subscheme `i : Z ⟶ X` with `dim_δ(Z) ≤ k` has `dim_{δ'} ≤ k + c`. It presents that base change
as `pullback.snd i (pullback.fst f B.g)`, the second projection of the pullback of `i` along the
projection `X' ⟶ X`.

A cycle-level argument for [Stacks, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ) reaches
the same closed subscheme written the other way round, as `pullback.fst (pullback.fst f B.g) i`:
the two orders of the factors are what the two sides of the coefficient formula for base change
of cycles produce. This file crosses that spelling, so that the bound is available at both.

The crossing is `CategoryTheory.Limits.pullbackSymmetry`: the two projections differ by
precomposition with an isomorphism, hence agree pointwise, and the bound is pointwise by
`Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le` and
`Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le`. Nothing of Stacks 0FVI is
reproved here and no `@[stacks 0FVI]` attribute is placed; the single declaration below is the
existing bound read at the other projection.

## Main results

* `Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_fst_le` — the bound of
  Stacks 0FVI (1) for the base change written as a first projection.

## References

* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 0FVI, part (1), dimension bound, at the other projection.** In the flat base-change
situation of Stacks 0FVG, the base change `Z ×_X X'` of a closed subscheme `Z ⊆ X` of
delta-dimension at most `k`, presented as the *first* projection
`pullback.fst (pullback.fst f B.g) i`, is a closed subscheme of `X' = X ×_S S'` of
delta-dimension at most `k + c`.

This is `Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_le` composed with
`CategoryTheory.Limits.pullbackSymmetry`; see the module documentation. -/
theorem schemeDeltaDimension_baseChange_closedSubscheme_fst_le (B : FlatBaseChangeSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] {k : ℤ}
    (hZ : schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange
        (pullback.fst (pullback.fst f B.g) i ≫ pullback.snd f B.g) ≤
      ((k + B.c : ℤ) : EInt) := by
  have hbase := schemeDeltaDimension_baseChange_closedSubscheme_le B f i hZ
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le B.baseChange
    (pullback.snd f B.g) (pullback.fst (pullback.fst f B.g) i) fun w => ?_
  have hpt : (pullback.fst (pullback.fst f B.g) i) w =
      (pullback.snd i (pullback.fst f B.g))
        ((pullbackSymmetry (pullback.fst f B.g) i).hom w) := by
    rw [← Scheme.Hom.comp_apply (pullbackSymmetry (pullback.fst f B.g) i).hom
      (pullback.snd i (pullback.fst f B.g)) w, pullbackSymmetry_hom_comp_snd]
  rw [hpt]
  exact relativeDimension_le_of_schemeDeltaDimension_le B.baseChange (pullback.snd f B.g)
    (pullback.snd i (pullback.fst f B.g)) hbase _

end Stacks.Chow

end
