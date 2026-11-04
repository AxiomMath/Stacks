module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# Chart base change is cartesian over a morphism of charts

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`. Base change
along `f` of étale scheme charts of `Y` is the functor
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4). For a single chart
`W ⟶ Y` the defining square is cartesian over `f`, which is
`AlgebraicGeometry.Space.smallBaseChange_isPullback`. This file records the *relative* form: for
a morphism `k : V ⟶ W` of étale charts of `Y`, the square
```
V ×_Y X --> W ×_Y X
   |           |
   v           v
   V -- k -->  W
```
is cartesian as well — the base change of `V` along `f` is the fibre product of `k` with the
base change of `W`.

## Main results

* `AlgebraicGeometry.Space.representablePullbackMap_isPullback`: the relative square is
  cartesian in presheaves.
* `AlgebraicGeometry.Space.representablePullbackMap_isPullback_site`: the same square is
  cartesian in the big fppf site.
* `AlgebraicGeometry.Space.representablePullbackMap_isPullback_scheme`: and therefore cartesian
  on the underlying schemes.
* `AlgebraicGeometry.Space.representablePullbackMap_property`: a property of scheme morphisms
  stable under base change passes to the base change of a morphism of charts.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)

/-- The base change along `f` of a morphism of étale charts of `Y`, written as the morphism into
the chosen representable pullback induced by the universal property. -/
abbrev representablePullbackMap {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    hf.pullback V.1.hom ⟶ hf.pullback W.1.hom :=
  hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left)
    (representablePullback_lift_cond B S hS f hf k)

/-- **Stacks 03G2, part (4)**, relative form. For a morphism `k : V ⟶ W` of étale scheme charts
of `Y` the square formed by the two cartesian projections of base change along `f` and by `k` is
cartesian in presheaves. -/
theorem representablePullbackMap_isPullback {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    IsPullback (yoneda.map (representablePullbackMap B S hS f hf k))
      (yoneda.map (hf.snd V.1.hom)) (yoneda.map (hf.snd W.1.hom))
      (yoneda.map k.hom.left) := by
  have hw : yoneda.map k.hom.left ≫ W.1.hom = V.1.hom := CostructuredArrow.w k.hom
  have hfstV : yoneda.map (representablePullbackMap B S hS f hf k) ≫
      hf.fst W.1.hom = hf.fst V.1.hom :=
    hf.lift_fst _ _ (representablePullback_lift_cond B S hS f hf k)
  have hsndV : representablePullbackMap B S hS f hf k ≫ hf.snd W.1.hom =
      hf.snd V.1.hom ≫ k.hom.left :=
    hf.lift_snd _ _ (representablePullback_lift_cond B S hS f hf k)
  have hsnd : yoneda.map (representablePullbackMap B S hS f hf k) ≫
      yoneda.map (hf.snd W.1.hom) =
      yoneda.map (hf.snd V.1.hom) ≫ yoneda.map k.hom.left := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hsndV]
  refine IsPullback.of_right (h₁₂ := hf.fst W.1.hom) ?_ hsnd (hf.isPullback W.1.hom)
  rw [hfstV, hw]
  exact hf.isPullback V.1.hom

/-- **Stacks 03G2, part (4)**, relative form, in the site. The relative base-change square of
`AlgebraicGeometry.Space.representablePullbackMap_isPullback` is cartesian already in the big
fppf site of `S`. -/
theorem representablePullbackMap_isPullback_site {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    IsPullback (representablePullbackMap B S hS f hf k) (hf.snd V.1.hom)
      (hf.snd W.1.hom) k.hom.left :=
  IsPullback.of_map_of_faithful yoneda (representablePullbackMap_isPullback B S hS f hf k)

/-- **Stacks 03G2, part (4)**, relative form, on underlying schemes. The base change along `f` of
an étale chart of `Y` given over another chart `W` is the fibre product of schemes of that chart
with the base change of `W`. -/
theorem representablePullbackMap_isPullback_scheme {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (representablePullbackMap B S hS f hf k))
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))
      ((BigFppfOver.toScheme B S hS).map (hf.snd W.1.hom))
      ((BigFppfOver.toScheme B S hS).map k.hom.left) :=
  (representablePullbackMap_isPullback_site B S hS f hf k).map (BigFppfOver.toScheme B S hS)

/-- The base-change functor on étale scheme charts acts on morphisms by
`AlgebraicGeometry.Space.representablePullbackMap`. -/
theorem smallBaseChange_map_hom_left {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    ((smallBaseChange B S hS f hf).map k).hom.left =
      representablePullbackMap B S hS f hf k := rfl

/-- Any property of scheme morphisms stable under base change passes from a morphism of étale
scheme charts of `Y` to its base change along `f`. -/
theorem representablePullbackMap_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {V W : SmallEtale B S hS Y.1} (k : V ⟶ W)
    (hk : P ((BigFppfOver.toScheme B S hS).map k.hom.left)) :
    P ((BigFppfOver.toScheme B S hS).map (representablePullbackMap B S hS f hf k)) :=
  MorphismProperty.of_isPullback
    (representablePullbackMap_isPullback_scheme B S hS f hf k).flip hk

end AlgebraicGeometry.Space

end
