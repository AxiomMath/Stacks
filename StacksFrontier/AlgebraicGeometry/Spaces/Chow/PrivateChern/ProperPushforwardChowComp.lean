module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare

/-!
# Functoriality of proper pushforward on Chow homology

In Situation 0EDT, proper pushforward on the Chow homology `CH_*(X) = ⨁_k CH_k(X)` of good
algebraic spaces is functorial: for proper morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` over the base,

  `g_* ∘ f_* = (f ≫ g)_*`   on `CH_*(X)`.

This is Stacks 0EP2, which holds already for cycles
(`AlgebraicGeometry.Space.properCyclePushforward_comp`).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.properPushforwardChow_comp`.

## References

* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y Z : D.Ambient} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)

/-- **Stacks 0EP2 on Chow homology**: `g_* ∘ f_* = (f ≫ g)_*`. -/
theorem properPushforwardChow_comp {f : X ⟶ Y} {g : Y ⟶ Z} (hfB : f ≫ sY = sX)
    (hgB : g ≫ sZ = sY) (hf : IsProper D.site D.base D.base_mem f)
    (hg : IsProper D.site D.base D.base_mem g) (β : chowHomology.{u, u + 1} D sX hX) :
    properPushforwardChow.{u, u + 1} D sY hY sZ hZ g hgB hg
        (properPushforwardChow.{u, u + 1} D sX hX sY hY f hfB hf β) =
      properPushforwardChow.{u, u + 1} D sX hX sZ hZ (f ≫ g) (by rw [Category.assoc, hgB, hfB])
        (isProper_comp D.site D.base D.base_mem hX.1 hY.1 hZ.1 f g hf hg) β := by
  show ((properPushforwardChow.{u, u + 1} D sY hY sZ hZ g hgB hg).comp
      (properPushforwardChow.{u, u + 1} D sX hX sY hY f hfB hf)) β = _
  congr 1
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  rw [AddMonoidHom.comp_apply, properPushforwardChow_of, properPushforwardChow_of,
    properPushforwardChow_of, chowGroupProperPushforward_chowClass,
    chowGroupProperPushforward_chowClass, chowGroupProperPushforward_chowClass,
    properCyclePushforward_comp D sX sY sZ hX hY hZ hfB hgB hf hg k b]

end AlgebraicGeometry.Space.PrivateChern

end
