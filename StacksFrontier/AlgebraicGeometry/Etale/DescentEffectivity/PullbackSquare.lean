module

public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumPullbackSquare
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.Equivalence
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale effectivity is inherited by pullbacks of descent data

`AlgebraicGeometry.DescentData.isEffective_pullback` says that a descent datum which is the
canonical datum of a scheme over the base stays canonical after pulling back along a
commutative square. This file records the étale refinement: the scheme realising the pullback
is the restriction of the realising scheme to the new base, so if the first is étale over its
base then so is the second.

That refinement is what the limit reduction of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) needs. There the datum is
descended to a finite stage of an inverse system, effectivity is proved at that stage, and the
conclusion is transported back along the square relating the stage to the limit; the transport
has to carry the étaleness of the descended scheme with it, which bare effectivity does not.

## Main results

* `AlgebraicGeometry.DescentDatum.isEtaleEffective_pullbackSquare`: **étale effectivity is
  inherited by pullbacks of descent data along a commutative square.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_pullbackSquare`: **over a
  fixed base, étale effectivity is also reflected by pullback along a morphism admitting a
  reverse**, which is what identifies the restrictions of a datum to an open of the base computed
  in two different ways.

The base-change stability of the underlying scheme, which this needs in order to know that the
pullback of an étale datum is étale, is
`AlgebraicGeometry.DescentDatum.property_pullbackSquare_over_hom` of
`StacksFrontier/AlgebraicGeometry/Etale/DescentEffectivity/Defs.lean`.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S} {p : X' ⟶ X}
  {comm : p ≫ a = a' ≫ h} (P : DescentData.PullbackFunctor a a' h p comm)

/-- **Étale effectivity is inherited by pullbacks of descent data.** If a descent datum
relative to `X / S` is the canonical datum of a scheme étale over `S`, its pullback along the
square is the canonical datum of the restriction of that scheme to `S'`, which is étale over
`S'` because étaleness is stable under base change. -/
@[sga "1 IX 4.2" "partial"]
theorem isEtaleEffective_pullbackSquare {D : DescentDatum a} [Etale D.over.hom]
    [Etale (pullbackSquareDatum P D).over.hom] (hD : D.IsEtaleEffective) :
    (pullbackSquareDatum P D).IsEtaleEffective := by
  obtain ⟨U, ⟨e⟩⟩ := hD
  have : Etale ((Scheme.Etale.forget S).obj U).hom := U.prop
  have : Etale (pullback.snd ((Scheme.Etale.forget S).obj U).hom h) := inferInstance
  refine ⟨Scheme.Etale.mk (pullback.snd ((Scheme.Etale.forget S).obj U).hom h),
    ⟨ObjectProperty.isoMk _ ?_⟩⟩
  exact (DescentData.canonicalDatumPullbackIso P ((Scheme.Etale.forget S).obj U)).symm ≪≫
    P.functor.mapIso ((IsEtaleDescentData a).ι.mapIso e)

/-- **Over a fixed base, étale effectivity is reflected by pullback along a morphism admitting a
reverse morphism over that base.** If `q : X ⟶ X'` and `p : X' ⟶ X` are morphisms over `S`, then
pullback along `q` is an equivalence on descent data (Tag 0243), and its quasi-inverse is pullback
along `p`; so a datum relative to `X' / S` whose pullback along `q` is étale effective is itself
étale effective.

This is what compares two computations of the restriction of a datum to an open of the base: the
restriction along a composite and the iterated restriction are data relative to two morphisms over
the same base which are canonically isomorphic, hence admit morphisms in both directions. -/
theorem isEtaleEffective_of_isEtaleEffective_pullbackSquare {S X X' : Scheme.{u}} (a : X ⟶ S)
    (a' : X' ⟶ S) (p : X' ⟶ X) (q : X ⟶ X') (hp : p ≫ a = a' ≫ 𝟙 S) (hq : q ≫ a' = a ≫ 𝟙 S)
    (E : DescentDatum a') [Etale E.over.hom]
    [Etale (pullbackSquareDatum (DescentData.pullbackFunctor a' a (𝟙 S) q hq) E).over.hom]
    (h : (pullbackSquareDatum (DescentData.pullbackFunctor a' a (𝟙 S) q hq) E).IsEtaleEffective) :
    E.IsEtaleEffective := by
  have hP : Etale (pullbackSquareDatum (DescentData.pullbackFunctor a a' (𝟙 S) p hp)
      (pullbackSquareDatum (DescentData.pullbackFunctor a' a (𝟙 S) q hq) E)).over.hom :=
    property_pullbackSquare_over_hom _ @Etale _ ‹_›
  have h2 := isEtaleEffective_pullbackSquare
    (DescentData.pullbackFunctor a a' (𝟙 S) p hp) h
  have hcomp : (p ≫ q) ≫ a' = a' ≫ 𝟙 S := by
    rw [Category.assoc, hq, Category.comp_id, hp, Category.comp_id]
  have hself : (p ≫ q) ≫ a' = a' := by rw [hcomp, Category.comp_id]
  have hε : (DescentData.pullbackFunctor a' a (𝟙 S) q hq).functor ⋙
      (DescentData.pullbackFunctor a a' (𝟙 S) p hp).functor ≅ 𝟭 _ :=
    (DescentData.pullbackFactorizationIso
      (DescentData.pullbackFunctor a' a' (𝟙 S) (p ≫ q) hcomp)
      (DescentData.pullbackFunctor a' a (𝟙 S) q hq)
      (DescentData.pullbackFunctor a a' (𝟙 S) p hp)).symm ≪≫
    DescentData.selfPullbackFunctorIso a' (p ≫ q) hself
  exact Functor.essImage.ofIso (ObjectProperty.isoMk _ (hε.app E)) h2

end DescentDatum

end AlgebraicGeometry

end
