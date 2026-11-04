module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula

/-!
# `f_*1 = 1` from the compatibility of the trace maps

Let `(D0)`–`(D3)` be data satisfying axiom (A)(b) (`Stacks.WeilCohomology.WeilData`), and let
`f : X ⟶ Y` be a morphism of nonempty smooth projective schemes over `k`, both equidimensional of
dimension `d`. The pushforward `f_* : H^0(X) ⟶ H^0(Y)` is characterized by
`∫_X f^*a ∪ c = ∫_Y a ∪ f_*c`. Taking `c = 1`, this says that `f_*1 = 1` exactly when
`∫_X ∘ f^* = ∫_Y` on `H^{2d}(Y)(d)`: the pairing on `Y` is perfect. This is the last step of the
proof of Stacks 0FIS.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_unitTw_iff`: `f_*1 = 1` if and only if
  `∫_X f^*a = ∫_Y a` for all `a ∈ H^{2d}(Y)(d)`.

## References

* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- **`f_*1 = 1` exactly when the trace of `X` is the trace of `Y` composed with pullback.** For
`f : X ⟶ Y` between nonempty smooth projective schemes equidimensional of the same dimension
`d`, and the pushforward of (A)(b), `f_*1 = 1 ∈ H^0(Y)` if and only if `∫_X f^*a = ∫_Y a` for every
`a ∈ H^{2d}(Y)(d)`. -/
theorem pushforward_unitTw_eq_unitTw_iff (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y d) :
    W.pushforward hA f hX hY 0 0 0 0 rfl rfl (W.unitTw X 0 0 rfl) = W.unitTw Y 0 0 rfl ↔
      ∀ a : W.Tw Y (2 * d) d, W.trace X d hX (W.pullTw f (2 * d) d a) = W.trace Y d hY a := by
  have key : ∀ a : W.Tw Y (2 * d) d,
      W.trace X d hX (W.pullTw f (2 * d) d a) =
        W.pairingTw Y d hY (2 * d) 0 (by ring) d 0 (by ring) a
          (W.pushforward hA f hX hY 0 0 0 0 rfl rfl (W.unitTw X 0 0 rfl)) := by
    intro a
    have h := W.pushforward_trace' hA f hX hY 0 0 0 0 rfl rfl (2 * d) d (by ring) (by ring)
      (by ring) (by ring) a (W.unitTw X 0 0 rfl)
    rw [pairingTw_apply, W.cupTw_eq_self_of_coe_twCoord_eq_one_right X _ _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw X _ _ rfl)] at h
    exact h
  have hY1 : ∀ a : W.Tw Y (2 * d) d,
      W.pairingTw Y d hY (2 * d) 0 (by ring) d 0 (by ring) a (W.unitTw Y 0 0 rfl) =
        W.trace Y d hY a := by
    intro a
    rw [pairingTw_apply, W.cupTw_eq_self_of_coe_twCoord_eq_one_right Y _ _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw Y _ _ rfl)]
  constructor
  · intro h a
    rw [key, h, hY1]
  · intro h
    refine W.eq_of_pairingTw_eq hA hY (2 * d) 0 (by ring) d 0 (by ring) fun a => ?_
    rw [← key, hY1, h]

end WeilData

end Stacks.WeilCohomology

end
