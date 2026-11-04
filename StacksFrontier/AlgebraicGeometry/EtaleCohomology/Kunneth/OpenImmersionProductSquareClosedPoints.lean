module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ClosedPointsOfProductOverField

/-!
# The base change map of the product square of an open immersion, at closed points

In the proof of [Stacks, Tag 0F1H] the stalk of the base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` at a geometric point `z̄` of `X ×_K Y` is treated in two cases,
according to whether the image of `z` in `X` or the image of `z` in `Y` is not closed, and then:
*"Thus any counter example with `dim(X) + dim(Y)` minimal would only have nonisomorphisms
`q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` on stalks at closed points of `X ×_K Y` (because a point `z` of `X ×_K Y`
is a closed point if and only if both the image of `z` in `X` and in `Y` are closed)."* This file
proves that sentence, for `X` and `Y` locally of finite type over `K`.

## Main results

* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_not_isClosed`
  — the stalks at the geometric points over non-closed points of `Y ×_K X` are invertible once
  they are at those whose image in `X` or in `Y` is not closed.
* `Stacks.EtaleCohomology.OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_closedPoints`
  — the base change map is invertible once its stalks are invertible at the geometric points
  whose image in `X` or in `Y` is not closed, and at the geometric points over closed points.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- **Reduction to the points with a non-closed image.** Let `X` and `Y` be locally of finite type
over `K`. If the stalk of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible at every geometric point
of `Y ×_K X` whose image in `X` is not closed, and at every geometric point whose image in `Y` is
not closed, then it is invertible at every geometric point lying over a non-closed point: a point
of `Y ×_K X` is closed if and only if its images in `X` and in `Y` are. -/
theorem isIso_stalk_higherBaseChangeMapAb_of_not_isClosed (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hX : ∀ z : GeometricPoint (pullback sY sX),
      ¬ IsClosed ({pullback.snd sY sX (z.hom default)} : Set X) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (hY : ∀ z : GeometricPoint (pullback sY sX),
      ¬ IsClosed ({pullback.fst sY sX (z.hom default)} : Set Y) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (z : GeometricPoint (pullback sY sX)) (hz : ¬ IsClosed ({z.hom default} : Set _)) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) := by
  rw [isClosed_singleton_pullback_iff, not_and_or] at hz
  rcases hz with hz | hz
  · exact hY z hz
  · exact hX z hz

/-- **The base change map is invertible once it is at the closed points and at the points with a
non-closed image.** Let `X` and `Y` be locally of finite type over `K`. If the stalk of
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible at every geometric point of `Y ×_K X` whose image
in `X` or in `Y` is not closed, and at every geometric point lying over a closed point, then the
base change map is invertible. -/
theorem isIso_higherBaseChangeMapAb_of_closedPoints (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hX : ∀ z : GeometricPoint (pullback sY sX),
      ¬ IsClosed ({pullback.snd sY sX (z.hom default)} : Set X) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (hY : ∀ z : GeometricPoint (pullback sY sX),
      ¬ IsClosed ({pullback.fst sY sX (z.hom default)} : Set Y) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (hc : ∀ z : GeometricPoint (pullback sY sX), IsClosed ({z.hom default} : Set _) →
      IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
        (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕))) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun z => ?_
  by_cases hz : IsClosed ({z.hom default} : Set _)
  · exact hc z hz
  · exact isIso_stalk_higherBaseChangeMapAb_of_not_isClosed sX sU sY j hj i 𝓕 hX hY z hz

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
