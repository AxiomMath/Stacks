module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The map on relative self-products induced by a morphism of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a base algebraic space `B` induces a map
`X ×_B X ⟶ Y ×_B Y` on relative self-products. It factors as
`X ×_B X ⟶ X ×_B Y ⟶ Y ×_B Y`, and each of the two factors is a base change of `f` itself;
hence the map on self-products is universally closed whenever `f` is. The square formed by
this map and the two relative diagonals commutes, which is how the map enters the study of
separation properties: the diagonal of `Y` pulls back along it to the diagonal of `X`.

## Main definitions

* `AlgebraicGeometry.Space.selfProductMap` is the canonical map on relative self-products.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_of_isIso`: an isomorphism of presheaves on the
  big fppf site is universally closed.
* `AlgebraicGeometry.Space.universallyClosed_of_isPullback`: universal closedness transfers
  along an arbitrary cartesian square, not only along the canonical fibre product.
* `AlgebraicGeometry.Space.universallyClosed_selfProductMap`: the map on relative
  self-products of a universally closed morphism is universally closed.

## Implementation notes

The structure morphism of the source is written as the composite `X ⟶ Y ⟶ B`, which is the
over-`B` condition on `f`. The fibre products are those of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, so the map on self-products is a morphism of
algebraic spaces and not merely of presheaves; its underlying morphism of presheaves is
`CategoryTheory.Limits.pullback.map`.

The two cartesian squares exhibiting the factors `X ×_B X ⟶ X ×_B Y` and `X ×_B Y ⟶ Y ×_B Y`
as base changes of `f` are built by hand from the universal property, rather than by composing
the pasting isomorphisms, because the morphisms whose cartesianity is wanted are the
`CategoryTheory.Limits.pullback.map` morphisms appearing in the definition and not the
projections of an iterated fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is universally closed: each of
its base changes is again an isomorphism, and the map on points of an isomorphism is a closed
map. -/
theorem universallyClosed_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : UniversallyClosed B S hS e := fun Z _ g ↦
  have : IsIso (pullback.fst g e) :=
    (IsPullback.of_isLimit (pullback.isLimit g e)).isIso_fst_of_isIso
  isClosedMap_pointsMap_of_isIso B S hS (pullback.fst g e)

/-- Universal closedness transfers along an arbitrary cartesian square: if
`IsPullback a b g f` and `f` is universally closed, then so is `a`.

This is `AlgebraicGeometry.Space.universallyClosed_pullback` composed with the identification
of the given square with the canonical fibre product. -/
theorem universallyClosed_of_isPullback
    {A C Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T)
    (f : C ⟶ T) (g : Z ⟶ T) (hf : UniversallyClosed B S hS f)
    {a : A ⟶ Z} {b : A ⟶ C} (hpb : IsPullback a b g f) :
    UniversallyClosed B S hS a := by
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hC hT
  have hc := universallyClosed_comp B S hS hP hZ hpb.isoPullback.hom (pullback.fst g f)
    (universallyClosed_of_isIso B S hS hpb.isoPullback.hom)
    (universallyClosed_pullback B S hS f g hf)
  rwa [hpb.isoPullback_hom_fst] at hc

variable {B S hS}
variable {Bs X Y : AlgebraicSpaces B S hS}

/-- The canonical map `X ×_B X ⟶ Y ×_B Y` on relative self-products induced by a morphism
`f : X ⟶ Y` of algebraic spaces over `B`. -/
noncomputable def selfProductMap (g : Y ⟶ Bs) (f : X ⟶ Y) :
    AlgebraicSpaces.fiberProduct B S hS (f ≫ g) (f ≫ g) ⟶
      AlgebraicSpaces.fiberProduct B S hS g g :=
  ObjectProperty.homMk
    (pullback.map (f ≫ g).hom (f ≫ g).hom g.hom g.hom
      f.hom f.hom (𝟙 Bs.1) (by simp) (by simp))

/-- The map on relative self-products of a universally closed morphism of algebraic spaces is
universally closed: it is the composition of two base changes of the morphism. -/
theorem universallyClosed_selfProductMap (g : Y ⟶ Bs) (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f.hom) :
    UniversallyClosed B S hS (selfProductMap g f).hom := by
  let fg := f.hom ≫ g.hom
  let pxx := pullback fg fg
  let pxy := pullback fg g.hom
  let pyy := pullback g.hom g.hom
  let a : pxx ⟶ pxy :=
    pullback.map fg fg fg g.hom (𝟙 X.1) f.hom (𝟙 Bs.1) (by simp [fg]) (by simp [fg])
  let b : pxy ⟶ pyy :=
    pullback.map fg g.hom g.hom g.hom f.hom (𝟙 Y.1) (𝟙 Bs.1) (by simp [fg]) (by simp)
  have ha₁ : a ≫ pullback.fst fg g.hom = pullback.fst fg fg := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd fg g.hom = pullback.snd fg fg ≫ f.hom := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.fst g.hom g.hom = pullback.fst fg g.hom ≫ f.hom :=
    pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd g.hom g.hom = pullback.snd fg g.hom := pullback.lift_snd _ _ _
  have hpbA : IsPullback a (pullback.snd fg fg) (pullback.snd fg g.hom) f.hom :=
    IsPullback.of_right (by rw [ha₁]; exact IsPullback.of_hasPullback fg fg) ha₂
      (IsPullback.of_hasPullback fg g.hom)
  have hpbB : IsPullback b (pullback.fst fg g.hom) (pullback.fst g.hom g.hom) f.hom :=
    IsPullback.of_right (by rw [hb₂]; exact (IsPullback.of_hasPullback fg g.hom).flip) hb₁
      (IsPullback.of_hasPullback g.hom g.hom).flip
  have hpXY : IsAlgebraicSpace B S hS pxy :=
    isAlgebraicSpace_pullback B S hS fg g.hom X.property Y.property Bs.property
  have hpYY : IsAlgebraicSpace B S hS pyy :=
    isAlgebraicSpace_pullback B S hS g.hom g.hom Y.property Y.property Bs.property
  have hcomp := universallyClosed_comp B S hS hpXY hpYY a b
    (universallyClosed_of_isPullback B S hS
      (isAlgebraicSpace_pullback B S hS fg fg X.property X.property Bs.property) X.property hpXY
      Y.property f.hom (pullback.snd fg g.hom) hf hpbA)
    (universallyClosed_of_isPullback B S hS hpXY X.property hpYY Y.property
      f.hom (pullback.fst g.hom g.hom) hf hpbB)
  have hab : a ≫ b = pullback.map (f.hom ≫ g.hom) (f.hom ≫ g.hom) g.hom g.hom
      f.hom f.hom (𝟙 Bs.1) (by simp) (by simp) := by
    simpa [a, b, fg] using
      pullback.map_comp (𝟙 X.1) f.hom f.hom (𝟙 Y.1) (𝟙 Bs.1) (𝟙 Bs.1)
        (by simp) (by simp) (by simp) (by simp)
  rwa [hab] at hcomp

end AlgebraicGeometry.Space

end
