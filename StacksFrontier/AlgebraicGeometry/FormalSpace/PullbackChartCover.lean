module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty

/-!
# The chart cover of a fibre product of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a local property of morphisms
of countably indexed weakly admissible topological rings which is stable under completed
tensor-product base change (Stacks 0GBC), and let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of
fppf sheaves on the big fppf site of `S`. **Stacks 0GBD** says that the equivalent conditions
of Stacks 0ANG pass from `f` to the second projection `pr₂ : X ×_Y Z ⟶ Z`; this file builds the
family of charts of `X ×_Y Z` on which the source's proof runs, and proves what that proof needs
of it.

The charts of `X ×_Y Z` used by the source are the fibre products `U ×_V W` of a chart `U` of
`V ×_Y X` with a chart `W` of `V ×_Y Z` over a chart `V` of `Y`. The second projection of such
a fibre product is a base change of the chart map `U ⟶ V`, and its map to `X ×_Y Z` factors as
`U ×_V W ⟶ U ×_X (X ×_Y Z) ⟶ X ×_Y Z`, both stages being base changes of representable étale
morphisms. Stacks 0GBD itself is
`AlgebraicGeometry.FormalSpace.hasProperty_pullback_snd_of_isLocallyCountablyIndexed` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedPullbackLocalProperty`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.chartPullbackMap`: the map `U ×_V W ⟶ X ×_Y Z`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_isPullback`: representable étale
  morphisms of fppf sheaves are stable under base change along an arbitrary cartesian square.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_chartPullbackMap`: the chart `U ×_V W` is
  representable étale over `X ×_Y Z`.

## Implementation notes

That `U ×_V W` is the fibre product of `W` with `U ×_X (X ×_Y Z)` over `V ×_Y Z` comes from two
applications of `CategoryTheory.IsPullback.of_bot`: first identifying `U ×_X (X ×_Y Z)` with
`U ×_V (V ×_Y Z)`, then exhibiting `U ×_V W` as its fibre product with `W` over `V ×_Y Z`.

What the source needs of the family of chart fibre products, beyond the assertion of Definition
0AIM that it jointly covers `X ×_Y Z`, is that each member is representable étale over
`X ×_Y Z` and maps to `Z` through the chart `W` of `V ×_Y Z`; that is what is proved here.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Representable étale morphisms of fppf sheaves are stable under base change, in the form of
an arbitrary cartesian square: if the right-hand map of a cartesian square is representable
étale, then so is the left-hand map parallel to it. -/
theorem isRepresentableEtale_of_isPullback {T X Y Z : FppfSheaf B S hS} {p : T ⟶ X} {q : T ⟶ Y}
    {h : X ⟶ Z} {k : Y ⟶ Z} (hsq : IsPullback p q h k)
    (hh : IsRepresentableEtale B S hS h) : IsRepresentableEtale B S hS q := by
  have hsq' : IsPullback p.hom q.hom h.hom k.hom :=
    hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
      p.hom q.hom h.hom k.hom hsq' hh.1,
    isEtaleULift_pullback_fst_of_isPullback B S hS hsq' hh.2⟩

section Charts

variable {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) {V U W : FppfSheaf B S hS}
  (v : V ⟶ Y) (a : U ⟶ pullback v f) (b : W ⟶ pullback v g)

/-- The chart of `X ×_Y Z` cut out by a chart `v : V ⟶ Y` of the base, a chart `a` of `V ×_Y X`
and a chart `b` of `V ×_Y Z`: the fibre product `U ×_V W`, mapped to `X ×_Y Z` by the
projections of its two factors to `X` and to `Z`. -/
def chartPullbackMap :
    pullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ⟶ pullback f g :=
  pullback.lift
    (pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ a ≫ pullback.snd v f)
    (pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ b ≫ pullback.snd v g)
    (by
      have h1 : pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ a ≫
            pullback.fst v f ≫ v =
          pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ b ≫
            pullback.fst v g ≫ v := by
        simpa only [Category.assoc] using
          (pullback.condition (f := a ≫ pullback.fst v f) (g := b ≫ pullback.fst v g)) =≫ v
      simp only [Category.assoc]
      rw [← pullback.condition (f := v) (g := f), ← pullback.condition (f := v) (g := g)]
      exact h1)

/-- The map `U ×_V W ⟶ X ×_Y Z` composed with the projection to `X`. -/
theorem chartPullbackMap_comp_fst :
    chartPullbackMap B S hS f g v a b ≫ pullback.fst f g =
      pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ a ≫ pullback.snd v f :=
  pullback.lift_fst _ _ _

/-- The map `U ×_V W ⟶ X ×_Y Z` composed with the projection to `Z` factors through the chart
`W` of `V ×_Y Z`. -/
theorem chartPullbackMap_comp_snd :
    chartPullbackMap B S hS f g v a b ≫ pullback.snd f g =
      pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ b ≫ pullback.snd v g :=
  pullback.lift_snd _ _ _

/-- The comparison map `U ×_X (X ×_Y Z) ⟶ V ×_Y Z` induced by the chart map `U ⟶ V` and by the
projection of `X ×_Y Z` to `Z`. -/
private def chartCompare :
    pullback (a ≫ pullback.snd v f) (pullback.fst f g) ⟶ pullback v g :=
  pullback.lift
    (pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) ≫ a ≫ pullback.fst v f)
    (pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) ≫ pullback.snd f g)
    (by
      simp only [Category.assoc]
      rw [pullback.condition (f := v) (g := f), ← pullback.condition (f := f) (g := g)]
      simpa only [Category.assoc] using
        pullback.condition_assoc (f := a ≫ pullback.snd v f) (g := pullback.fst f g) f)

private theorem chartCompare_comp_fst :
    chartCompare B S hS f g v a ≫ pullback.fst v g =
      pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) ≫ a ≫ pullback.fst v f :=
  pullback.lift_fst _ _ _

private theorem chartCompare_comp_snd :
    chartCompare B S hS f g v a ≫ pullback.snd v g =
      pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) ≫ pullback.snd f g :=
  pullback.lift_snd _ _ _

/-- The comparison map `U ×_V W ⟶ U ×_X (X ×_Y Z)`. -/
private def chartLift :
    pullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ⟶
      pullback (a ≫ pullback.snd v f) (pullback.fst f g) :=
  pullback.lift (pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g))
    (chartPullbackMap B S hS f g v a b)
    (chartPullbackMap_comp_fst B S hS f g v a b).symm

private theorem chartLift_comp_fst :
    chartLift B S hS f g v a b ≫ pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) =
      pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) :=
  pullback.lift_fst _ _ _

private theorem chartLift_comp_snd :
    chartLift B S hS f g v a b ≫ pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) =
      chartPullbackMap B S hS f g v a b :=
  pullback.lift_snd _ _ _

private theorem chartLift_comp_chartCompare_comp_fst :
    chartLift B S hS f g v a b ≫ chartCompare B S hS f g v a ≫ pullback.fst v g =
      pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ a ≫ pullback.fst v f := by
  rw [chartCompare_comp_fst, ← Category.assoc, chartLift_comp_fst]

private theorem chartLift_comp_chartCompare_comp_snd :
    chartLift B S hS f g v a b ≫ chartCompare B S hS f g v a ≫ pullback.snd v g =
      chartPullbackMap B S hS f g v a b ≫ pullback.snd f g := by
  rw [chartCompare_comp_snd, ← Category.assoc, chartLift_comp_snd]

/-- `U ×_X (X ×_Y Z)` is the fibre product of `U` with `V ×_Y Z` over `V`. -/
private theorem isPullback_chartCompare :
    IsPullback (pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g))
      (chartCompare B S hS f g v a) (a ≫ pullback.fst v f) (pullback.fst v g) := by
  have hs := (IsPullback.of_hasPullback (a ≫ pullback.snd v f) (pullback.fst f g)).paste_vert
    (IsPullback.of_hasPullback f g)
  have e : (a ≫ pullback.fst v f) ≫ v = (a ≫ pullback.snd v f) ≫ f := by
    simp only [Category.assoc, pullback.condition]
  refine IsPullback.of_bot ?_ (chartCompare_comp_fst B S hS f g v a).symm
    (IsPullback.of_hasPullback v g)
  rw [chartCompare_comp_snd, e]
  exact hs

/-- `U ×_V W` is the fibre product of `U ×_X (X ×_Y Z)` with `W` over `V ×_Y Z`. -/
private theorem isPullback_chartLift :
    IsPullback (pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g))
      (chartLift B S hS f g v a b) b (chartCompare B S hS f g v a) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_chartCompare B S hS f g v a).flip
  · rw [chartLift_comp_fst B S hS f g v a b]
    exact (IsPullback.of_hasPullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g)).flip
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, chartLift_comp_chartCompare_comp_fst]
      exact pullback.condition.symm
    · rw [Category.assoc, Category.assoc, chartLift_comp_chartCompare_comp_snd,
        chartPullbackMap_comp_snd]

/-- The chart `U ×_V W` is representable étale over `X ×_Y Z`: its map to `X ×_Y Z` is a base
change of the chart map `b` of `V ×_Y Z` followed by a base change of the composite
`U ⟶ V ×_Y X ⟶ X`. -/
theorem isRepresentableEtale_chartPullbackMap (hv : IsRepresentableEtale B S hS v)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    IsRepresentableEtale B S hS (chartPullbackMap B S hS f g v a b) := by
  rw [← chartLift_comp_snd B S hS f g v a b]
  refine IsRepresentableEtale.comp B S hS
    (isRepresentableEtale_of_isPullback B S hS (isPullback_chartLift B S hS f g v a b) hb)
    (isRepresentableEtale_of_isPullback B S hS
      (IsPullback.of_hasPullback (a ≫ pullback.snd v f) (pullback.fst f g)) ?_)
  exact IsRepresentableEtale.comp B S hS ha (isRepresentableEtale_pullback_snd B S hS v f hv)

end Charts

end AlgebraicGeometry.FormalSpace

end
