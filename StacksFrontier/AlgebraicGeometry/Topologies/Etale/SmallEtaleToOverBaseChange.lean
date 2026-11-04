module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Base change on the small étale site is pullback of schemes over the base

Let `B` be a big étale site, let `X` and `Y` be objects of `B` and let `f : Y ⟶ X`. Base change
along `f` carries an object of the small étale site of `X` to its fibre product with `Y`, formed
inside `B`. Read in the category of all schemes over `Y`, that fibre product is the pullback of
the original scheme over `X` along `f`, because the inclusion of `B` into schemes preserves
pullbacks.

## Main definitions

* `AlgebraicGeometry.smallEtaleToOverBaseChangeProj`: the projection of the base change of an
  étale scheme over `X` onto that scheme.
* `AlgebraicGeometry.smallEtaleToOverBaseChangeIso`: the comparison of base change on the small
  étale site with pullback in schemes over `Y`.

## Main results

* `AlgebraicGeometry.smallEtaleToOverBaseChangeIsPullback`: the base change of an étale scheme
  over `X` sits in a pullback square over `f`.

## References

* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)

/-- The projection of the base change along `f` of an étale scheme over `X` onto that scheme,
as a natural transformation of the two underlying-scheme functors. -/
def smallEtaleToOverBaseChangeProj :
    (smallEtaleBaseChange B f ⋙ smallEtaleToOver B Y) ⋙ Over.forget Y.1 ⟶
      smallEtaleToOver B X ⋙ Over.forget X.1 where
  app U := B.inclusion.map (pullback.fst U.obj.hom f)
  naturality U V g := by
    change B.inclusion.map ((Over.pullback f).map g.hom).left ≫
        B.inclusion.map (pullback.fst V.obj.hom f) =
      B.inclusion.map (pullback.fst U.obj.hom f) ≫ B.inclusion.map g.hom.left
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (pullback.lift_fst _ _ _)

/-- The base change along `f` of an étale scheme over `X` sits in a pullback square over `f`. -/
theorem smallEtaleToOverBaseChangeIsPullback (U : SmallEtale B X.1 X.2) :
    IsPullback ((smallEtaleToOverBaseChangeProj B f).app U)
      ((smallEtaleBaseChange B f ⋙ smallEtaleToOver B Y).obj U).hom
      ((smallEtaleToOver B X).obj U).hom f.hom :=
  (IsPullback.of_hasPullback U.obj.hom f).map B.inclusion

/-- Base change on the small étale site is pullback in schemes over the base. -/
def smallEtaleToOverBaseChangeIso :
    smallEtaleBaseChange B f ⋙ smallEtaleToOver B Y ≅
      smallEtaleToOver B X ⋙ Over.pullback f.hom := by
  refine NatIso.ofComponents (fun U ↦ Over.isoMk
    (smallEtaleToOverBaseChangeIsPullback B f U).isoPullback
    (smallEtaleToOverBaseChangeIsPullback B f U).isoPullback_hom_snd) ?_
  intro U V g
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, CategoryTheory.Functor.comp_map, Over.isoMk_hom_left,
      Over.pullback_map_left, Category.assoc, IsPullback.isoPullback_hom_fst,
      pullback.lift_fst]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact (smallEtaleToOverBaseChangeProj B f).naturality g
  · simp only [Over.comp_left, CategoryTheory.Functor.comp_map, Over.isoMk_hom_left,
      Over.pullback_map_left, Category.assoc, IsPullback.isoPullback_hom_snd,
      pullback.lift_snd]
    exact Over.w ((smallEtaleBaseChange B f ⋙ smallEtaleToOver B Y).map g)

end AlgebraicGeometry

end
