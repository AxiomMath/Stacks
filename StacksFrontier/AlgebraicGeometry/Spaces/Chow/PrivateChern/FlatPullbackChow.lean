module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow

/-!
# Flat pullback on the Chow homology of a good algebraic space

In Situation 0EDT let `f : X ⟶ Y` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B`. Flat pullback of cycles `f^* : Z_k(Y) → Z_{k+r}(X)` (Stacks 0EP8) carries
cycles rationally equivalent to zero to cycles rationally equivalent to zero (Stacks 0EQB), so
the flat pullback `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow` on Chow homology is
the induced map: `f^*[α] = [f^*α]`.

The presenting families of rational equivalences are indexed in a universe `w`; flat pullback
raises it to `max w (u + 1)`, so the statements are made at the universe `max v (u + 1)`, which
flat pullback preserves.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.respectsRationalEquivalence_flatPullbackMap`: Stacks
  0EQB for the Chow groups of `AlgebraicGeometry.Space.chowGroup`.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_of_chowClass`: `f^*[α] = [f^*α]`.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y : D.Ambient} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
  (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
  (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **Stacks 0EQB**: flat pullback of cycles respects rational equivalence. -/
theorem respectsRationalEquivalence_flatPullbackMap (k : ℤ) :
    RespectsRationalEquivalence.{u, max v (u + 1)} D sY hY sX hX
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + r) rfl) := by
  intro α hα
  exact (isRationallyEquivalentToZeroCanonical_iff.{max v (u + 1)} D sX hX (k + r) _).1
    (isRationallyEquivalentToZeroCanonical_flatPullbackMap D sX hX sY hY f hbase r hflat hr k
      (k + r) rfl ((isRationallyEquivalentToZeroCanonical_iff.{max v (u + 1)} D sY hY k α).2 hα))

/-- **The flat pullback on Chow homology is induced by flat pullback of cycles**:
`f^*[α] = [f^*α]`. -/
theorem flatPullbackChow_of_chowClass (k : ℤ) (α : CycleGroup D sY k) :
    flatPullbackChow.{u, max v (u + 1)} D sX hX sY hY f hbase r hflat hr
        (DirectSum.of _ k (chowClass.{max v (u + 1)} D sY hY k α)) =
      DirectSum.of (fun k => chowGroup.{max v (u + 1)} D sX hX k) (k + r)
        (chowClass.{max v (u + 1)} D sX hX (k + r)
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + r) rfl α)) := by
  rw [flatPullbackChow, gradedChowMap_of, chowDescend_chowClass _ _ _ _ _ _
    (respectsRationalEquivalence_flatPullbackMap.{u, v} D sX hX sY hY f hbase r hflat hr k)]

end AlgebraicGeometry.Space.PrivateChern

end
