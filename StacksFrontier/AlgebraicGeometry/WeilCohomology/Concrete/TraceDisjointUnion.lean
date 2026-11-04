module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula

/-!
# The unit class, the trace of a pushforward, and the dimension of a disjoint union

Three facts used for Stacks 0FHJ and 0FHP, for data (D0)–(D3) of Section 45.9 (Tag 0FHA):

* the unit class `1 ∈ H^0(X)(0)`, written in a degree and twist that are only propositionally
  zero, as the class with coordinate `1` for the coordinates `WeilData.twCoord` of the Tate
  twists, together with its behaviour under cup product and pullback;
* a pushforward between nonempty equidimensional schemes of the same dimension preserves the
  trace, `∫_Z f_*b = ∫_X b`: this is the trace equation `∫_X f^*c ∪ b = ∫_Z c ∪ f_*b` defining
  `f_*`, taken at `c = 1`;
* a coproduct `X ⨿ Y` of nonempty schemes equidimensional of dimension `d` is nonempty and
  equidimensional of dimension `d`, so that `∫_{X ⨿ Y}` is defined.

The registered Stacks 0FHP is in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionTrace`.

## Main results

* `Stacks.WeilCohomology.WeilData.unitTw`: the unit class.
* `Stacks.WeilCohomology.WeilData.trace_pushforward`: `∫_Z f_*b = ∫_X b`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isNonemptyEquidimensional_pt`,
  `Stacks.WeilCohomology.SmoothProjectiveScheme.isNonemptyEquidimensional_coprodObj`: `X ⨿ Y` is
  nonempty and equidimensional of dimension `d` when `X` and `Y` are.

## References

* [Stacks Project, Tag 0FHP](https://stacks.math.columbia.edu/tag/0FHP)
* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- The unit class `1 ∈ H^n(X)(m)`, for a degree `n` equal to zero, as the class with
coordinate `1`. -/
def unitTw (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) (hn : n = 0) : W.Tw X n m :=
  (W.twCoord X n m).symm ⟨1, hn ▸ SetLike.GradedOne.one_mem⟩

/-- The unit class read back in coordinates is `1`. -/
theorem coe_twCoord_unitTw (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) (hn : n = 0) :
    (W.twCoord X n m (W.unitTw X n m hn) : W.H X) = 1 := by
  simp [unitTw]

/-- Cup product on the left with a class whose coordinate is `1` is the identity. -/
theorem cupTw_eq_self_of_coe_twCoord_eq_one (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i j : ℤ)
    (h : i + j = j) (s t : ℤ) (h' : s + t = t) (x : W.Tw X i s)
    (hx : (W.twCoord X i s x : W.H X) = 1) (y : W.Tw X j t) :
    W.cupTw X i j j h s t t h' x y = y :=
  (W.twCoord X j t).injective <| Subtype.ext <| by rw [twCoord_cupTw, coe_cup, hx, one_mul]

/-- The pullback of the unit class has coordinate `1`. -/
theorem coe_twCoord_pullTw_unitTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (n m : ℤ)
    (hn : n = 0) : (W.twCoord X n m (W.pullTw f n m (W.unitTw Y n m hn)) : W.H X) = 1 := by
  rw [twCoord_pullTw, coe_pullDeg, coe_twCoord_unitTw, map_one]

/-- **Pushforward between schemes of the same dimension preserves the trace**: for
`f : X ⟶ Z` with `X` and `Z` nonempty and equidimensional of the same dimension `d`, and
`b ∈ H^{2d}(X)(d)`, `∫_Z f_*b = ∫_X b`. This is the trace equation `∫_X f^*c ∪ b = ∫_Z c ∪ f_*b`
defining `f_*`, at `c = 1`. -/
theorem trace_pushforward (hA : W.PerfectPairing) {X Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Z)
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) (hZ : IsNonemptyEquidimensional Z d)
    (b : W.Tw X (2 * d) d) :
    W.trace Z d hZ (W.pushforward hA f hX hZ (2 * d) d (2 * d) d rfl rfl b) =
      W.trace X d hX b := by
  have key := W.pushforward_trace hA f hX hZ (2 * d) d (2 * d) d rfl rfl
    (W.unitTw Z _ _ (sub_self _)) b
  simp only [pairingTw, LinearMap.compr₂_apply] at key
  rw [W.cupTw_eq_self_of_coe_twCoord_eq_one X _ _ _ _ _ _ _
      (W.coe_twCoord_pullTw_unitTw f _ _ (sub_self _)),
    W.cupTw_eq_self_of_coe_twCoord_eq_one Z _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw Z _ _ (sub_self _))] at key
  exact key.symm

end WeilData

namespace SmoothProjectiveScheme

/-- **A coproduct `X ⨿ Y` is nonempty and equidimensional of dimension `d`** when `X` and `Y`
are, for any colimit cofan. -/
theorem isNonemptyEquidimensional_pt {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan X Y}
    (hc : IsColimit c) {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y d) : IsNonemptyEquidimensional c.pt d where
  nonempty := have := hX.nonempty; nonempty_pt_of_left
  relativeDimension := relativeDimension_pt hc hX.relativeDimension hY.relativeDimension

/-- **`X ⨿ Y` is nonempty and equidimensional of dimension `d`** when `X` and `Y` are. -/
theorem isNonemptyEquidimensional_coprodObj {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d) :
    IsNonemptyEquidimensional (coprodObj X Y) d :=
  isNonemptyEquidimensional_pt (isColimitCoprodCofan X Y) hX hY

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
