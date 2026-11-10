module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.EtaleChartFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection

/-!
# Flat base change of a local complete intersection morphism of algebraic spaces

A local complete intersection morphism of algebraic spaces over `S` stays a local complete
intersection morphism after base change along a flat morphism of algebraic spaces. This is the
algebraic-spaces form of flat base change for the Koszul property; the schemes form is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_pullback_snd`, Stacks 069I.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_pullback_snd`: flat base change of a local
  complete intersection morphism of algebraic spaces.
* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism`: the
  Koszul property of morphisms of schemes is étale local on the source and target, granted that
  it is local on the source for the étale topology.

## Implementation notes

The base-changed morphism is the second projection out of the fibre product of the underlying
presheaves of points, which is again an algebraic space by Stacks 02X2; the fibre product and
its cartesian square are `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` and
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`.

## References

* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 069I](https://stacks.math.columbia.edu/tag/069I)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Étale locality of the Koszul property on the source and target -/

/-- Postcomposition with an étale morphism preserves the Koszul property. -/
private theorem isLocalCompleteIntersectionMorphism_respectsRight_etale :
    MorphismProperty.RespectsRight
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    let : Etale i := hi
    let : LocallyOfFiniteType f :=
      locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism hf
    let : LocallyOfFiniteType (f ≫ i) := inferInstance
    intro x
    obtain ⟨-, U, hxU, P, j, π, hj, hkoszul, hπ, hfactor⟩ := hf x
    let : IsImmersion j := hj
    let : Smooth π := hπ
    refine ⟨finiteTypeAt_of_locallyOfFiniteType (f ≫ i) x, U, hxU, P, j, π ≫ i, hj, hkoszul,
      inferInstance, ?_⟩
    simp only [← Category.assoc, hfactor]

/-- Granted that the Koszul property of morphisms of schemes is local on the source for the étale
topology, it is étale local on the source and target in the sense of Stacks 04QZ. -/
public theorem isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
    (hsrc : MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage) :
    IsEtaleLocalOnSourceAndTarget
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}) := by
  let := hsrc
  let := isLocalCompleteIntersectionMorphism_respectsRight_etale.{u}
  refine
    { precomp := respectsLeft_etale_of_isLocalAtSource _
      pullbackSnd_of_etale := fun f hf g hg => ?_
      iff_forall_exists_etale_neighborhood := fun f => ?_ }
  · let : Etale g := hg
    exact isLocalCompleteIntersectionMorphism_pullback_snd f g hf
  · classical
    refine ⟨fun hf x => ⟨_, _, 𝟙 _, 𝟙 _, f, x, inferInstance, inferInstance, by simp, by simp,
      hf⟩, fun hx => ?_⟩
    choose U V a b k u ha hb hu hcomm hP using hx
    refine MorphismProperty.IsLocalAtSource.of_forall_comp
      (ofArrows_mem_etalePrecoverage_iff.mpr ⟨fun x => ⟨x, u x, hu x⟩, ha⟩) ?_
    rintro W g ⟨x⟩
    rw [← hcomm x]
    exact MorphismProperty.RespectsRight.postcomp (Q := @Etale) (b x) (hb x) (k x) (hP x)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flat base change of the Koszul property -/

set_option synthInstance.maxHeartbeats 80000 in
-- instance search for pullbacks of algebraic spaces over the big fppf site
/-- A flat base change of a local complete intersection morphism of algebraic spaces is a local
complete intersection morphism: if `f : X ⟶ Y` is Koszul and `g : Y' ⟶ Y` is flat, then the
projection `X ×_Y Y' ⟶ Y'` is Koszul. -/
@[stacks 06C7]
public theorem isLocalCompleteIntersection_pullback_snd
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom)
    (hf : IsLocalCompleteIntersection B S hS f.hom) :
    IsLocalCompleteIntersection B S hS (Limits.pullback.snd f.hom g.hom) := by
  have hmain := holdsOnEveryEtaleChart_of_isPullback_of_isFlat B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u})
    (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
      _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale)
    (fun a c hc ha => by
      let : Flat c := hc
      exact _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_pullback_snd a c ha)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hg hf
  exact hmain

end Space

end AlgebraicGeometry

end
