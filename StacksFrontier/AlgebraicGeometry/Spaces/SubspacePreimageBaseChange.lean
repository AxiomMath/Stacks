module

public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Inverse images of subfunctors along the two legs of a cartesian square

Let a cartesian square of type-valued functors be given, with `f : Y ⟶ X`, `g : X' ⟶ X`,
`f' : Y' ⟶ X'` and `gY : Y' ⟶ Y`, and let `Z` be a subfunctor of `X`.  Pulling `Z` back to `X'`
and then to `Y'` is pulling it back to `Y` and then to `Y'`, both being the inverse image along
the common composite `Y' ⟶ X`; and the projection `(f')⁻¹(g⁻¹Z) ⟶ g⁻¹Z` commutes with the
projection `f⁻¹(Z) ⟶ Z` and the two maps between them.

A subfunctor which is only *known to be equal* to an inverse image, rather than given as one,
comes with the same projection and the same cartesian square.

## Main definitions

* `CategoryTheory.Subfunctor.mapOfEqPreimage`: for `T = k⁻¹(W)`, the projection `T ⟶ W`.

## Main results

* `CategoryTheory.Subfunctor.preimage_preimage_of_isPullback`: the two inverse images of `Z` in
  `Y'` agree.
* `CategoryTheory.Subfunctor.isPullback_mapOfEqPreimage`: that projection, which lies over `k`
  by `CategoryTheory.Subfunctor.lift_ι`, makes a cartesian square with the two inclusions.
* `CategoryTheory.Subfunctor.mapOfEqPreimage_comm`: the two projections commute with the square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {X Y X' Y' : C ⥤ Type w}

/-! ### A subfunctor known to be an inverse image -/

/-- **The projection of a subfunctor `T` of `X` onto a subfunctor `W` of `Y` which it is the
inverse image of along `k : X ⟶ Y`.** It is the inclusion of `T` followed by `k`, which lands in
`W` exactly because `T ≤ k⁻¹(W)`.

For `T` presented as `k⁻¹(W)` this is `CategoryTheory.Subfunctor.fromPreimage` on the nose. -/
def mapOfEqPreimage (W : Subfunctor Y) (k : X ⟶ Y) {T : Subfunctor X} (h : T = W.preimage k) :
    T.toFunctor ⟶ W.toFunctor :=
  Subfunctor.lift (T.ι ≫ k) (by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
    exact (Subfunctor.image_le_iff _ _ _).2 h.le)

/-- **Stacks 083Q for a subfunctor known to be an inverse image.** The square of the projection
of `CategoryTheory.Subfunctor.mapOfEqPreimage` against the two inclusions is cartesian. -/
theorem isPullback_mapOfEqPreimage (W : Subfunctor Y) (k : X ⟶ Y) {T : Subfunctor X}
    (h : T = W.preimage k) : IsPullback (W.mapOfEqPreimage k h) T.ι W.ι k := by
  subst h
  exact Subfunctor.isPullback_preimage k W

/-! ### The two legs of a cartesian square -/

/-- **The inverse image of a subfunctor in the apex of a cartesian square is read along either
leg.** For a subfunctor `Z` of `X` and a cartesian square with `f : Y ⟶ X`, `g : X' ⟶ X`,
`f' : Y' ⟶ X'` and `gY : Y' ⟶ Y`, the inverse image in `Y'` of `g⁻¹(Z)` is the inverse image of
`f⁻¹(Z)`: both are the inverse image of `Z` along the common composite `Y' ⟶ X`. -/
theorem preimage_preimage_of_isPullback (Z : Subfunctor X) {gY : Y' ⟶ Y} {f' : Y' ⟶ X'}
    {f : Y ⟶ X} {g : X' ⟶ X} (sq : IsPullback gY f' f g) :
    (Z.preimage g).preimage f' = (Z.preimage f).preimage gY := by
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, sq.w]

/-- **The two projections of the inverse images of a subfunctor commute with the square.** Let
`W` be a subfunctor of `X`, let `W'` be a subfunctor of `X'` equal to `g⁻¹(W)`, and let the
square be cartesian.  Then restricting `f'` to the inverse images of `W'` and projecting to `W`
is projecting to `f⁻¹(W)` and then restricting `f`. -/
theorem mapOfEqPreimage_comm (W : Subfunctor X) {gY : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X}
    {g : X' ⟶ X} (sq : IsPullback gY f' f g) {W' : Subfunctor X'} (hW' : W' = W.preimage g)
    (hT : W'.preimage f' = (W.preimage f).preimage gY) :
    W'.fromPreimage f' ≫ W.mapOfEqPreimage g hW' =
      (W.preimage f).mapOfEqPreimage gY hT ≫ W.fromPreimage f := by
  apply (cancel_mono W.ι).mp
  simp only [Category.assoc, Subfunctor.mapOfEqPreimage, Subfunctor.lift_ι,
    Subfunctor.lift_ι_assoc, Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι_assoc, sq.w]

end CategoryTheory.Subfunctor

end
