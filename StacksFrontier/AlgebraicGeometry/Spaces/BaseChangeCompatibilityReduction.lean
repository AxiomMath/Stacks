module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal

/-!
# The base-change clause of Stacks 081V reduced to three assertions

`AlgebraicGeometry.Space.BaseChangeCompatibility`, the base-change clause (the second sentence) of
Stacks 081V, has twelve fields. Three of them — `algebraPullback`, `algebraPullbackMap` and
`algebraPullback_isPushout` — are constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`. This file constructs six more: the
geometric base change of an algebraic space affine over `X`, its projection, the cartesianness of
the resulting square, the naturality of that projection, the base-change comparison on direct-image
sheaves of rings, and the assertion that that comparison is the adjunct of the square map.
`AlgebraicGeometry.Space.BaseChangeCompatibility.ofBaseChangeIso` builds the whole structure from
the remaining three fields, `algebraPullback_isQuasicoherent`, `baseChangeIso` and
`baseChangeIso_canonical`.

## Main definitions

* `AlgebraicGeometry.Space.affineBaseChangeFunctor` is the `affineBaseChange` field: the fibre
  product `Z ↦ Z ×_X Y` as a functor between the affine over-categories.
* `AlgebraicGeometry.Space.affineBaseChangeProjection` is the `affineBaseChange_projection`
  field, and `AlgebraicGeometry.Space.pushforwardBaseChangeMapOfSquare` the
  `pushforwardBaseChangeMap` field.
* `AlgebraicGeometry.Space.quasicoherentAlgebraPullbackFunctor` is the functor on quasi-coherent
  algebras which the `baseChangeIso` field compares.
* `AlgebraicGeometry.Space.BaseChangeCompatibility.ofBaseChangeIso` builds the structure from the
  three remaining fields.

## Main results

* `AlgebraicGeometry.Space.isPullback_affineBaseChangeProjection` and
  `AlgebraicGeometry.Space.affineBaseChangeProjection_naturality` are the
  `affineBaseChange_isPullback` and `affineBaseChange_projection_naturality` fields.

## Implementation notes

The `pushforwardBaseChangeMap_canonical` field asks that the base-change comparison on
direct-image rings be the adjunct, under the inverse-image/direct-image adjunction for sheaves of
commutative rings, of `AlgebraicGeometry.Space.pushforwardSquareMap` at the cartesian square.
Rather than build a comparison and then verify that equation,
`AlgebraicGeometry.Space.pushforwardBaseChangeMapOfSquare` is *defined* as that adjunct — the
inverse of `CategoryTheory.Adjunction.homEquiv` applied to the square map — so the field is
`Equiv.apply_symm_apply` and no coherence is checked by hand.  The square map's hypothesis
`p ≫ Z.hom = W.hom ≫ g` is supplied by the `CategoryTheory.IsPullback.w` of the same square, so
the two fields are guaranteed to be about one square and not two.

Affineness of the base change is `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`, which
is Stacks 03WI (`AlgebraicGeometry.Space.IsAffineHom.of_isPullback`) transported from presheaves
to algebraic spaces along `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`; fibre products are
`AlgebraicGeometry.AlgebraicSpaces.hasPullbacks`, Stacks 043C.

`affineBaseChangeProjection_naturality` is `CategoryTheory.Limits.pullback.lift_fst` once
`CategoryTheory.Over.pullback`'s action on morphisms is unfolded: the functor sends a morphism to
the lift whose first component is the projection followed by the morphism, which is the equation
the field asks for.

The field `algebraPullback_isQuasicoherent` asks that the pullback of a quasi-coherent algebra
along an arbitrary morphism of algebraic spaces be quasi-coherent; for modules this is Stacks 03GA.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Geometric base change of an affine algebraic space -/

/-- The `affineBaseChange` field of `AlgebraicGeometry.Space.BaseChangeCompatibility`: base
change along `g : Y ⟶ X` as a functor from the algebraic spaces affine over `X` to those affine
over `Y`.

The underlying functor is `CategoryTheory.Over.pullback`, available because the algebraic spaces
over a scheme have fibre products (Stacks 043C); its codomain is restricted to the affine
over-category by Stacks 03WI, affineness being stable under base change. -/
def affineBaseChangeFunctor {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    AffineOver B S hS X ⥤ AffineOver B S hS Y :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun f : Over X => IsAffineHom B S hS f.hom.hom) ⋙ Over.pullback g)
    fun Z => isAffineHom_hom_of_isPullback (IsPullback.of_hasPullback Z.obj.hom g) Z.property

/-- The `affineBaseChange_projection` field: the projection `Z ×_X Y ⟶ Z` from the base change of
an algebraic space affine over `X` to the space itself. -/
def affineBaseChangeProjection {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (Z : AffineOver B S hS X) :
    ((affineBaseChangeFunctor B S hS g).obj Z).obj.left ⟶ Z.obj.left :=
  pullback.fst Z.obj.hom g

/-- The `affineBaseChange_isPullback` field: the square formed by the projection of
`AlgebraicGeometry.Space.affineBaseChangeProjection`, the structure morphism of the base change,
the structure morphism of the original space and `g` is cartesian. -/
theorem isPullback_affineBaseChangeProjection {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (Z : AffineOver B S hS X) :
    IsPullback (affineBaseChangeProjection B S hS g Z)
      ((affineBaseChangeFunctor B S hS g).obj Z).obj.hom Z.obj.hom g :=
  IsPullback.of_hasPullback Z.obj.hom g

/-- The `affineBaseChange_projection_naturality` field: the projections of
`AlgebraicGeometry.Space.affineBaseChangeProjection` are natural in the affine algebraic space
being base-changed. -/
theorem affineBaseChangeProjection_naturality {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    {Z Z' : AffineOver B S hS X} (f : Z ⟶ Z') :
    ((affineBaseChangeFunctor B S hS g).map f).hom.left ≫
        affineBaseChangeProjection B S hS g Z' =
      affineBaseChangeProjection B S hS g Z ≫ f.hom.left := by
  simp only [affineBaseChangeFunctor, affineBaseChangeProjection, ObjectProperty.lift_map,
    Functor.comp_map]
  exact pullback.lift_fst _ _ _

/-! ### The base-change comparison on direct images -/

/-- The `pushforwardBaseChangeMap` field: the comparison
`g⁻¹ (Z.hom_* 𝒪_Z) ⟶ (Z ×_X Y ⟶ Y)_* 𝒪_{Z ×_X Y}` of sheaves of commutative rings on the small
étale site of `Y`.

It is *defined* as the adjunct of `AlgebraicGeometry.Space.pushforwardSquareMap` at the cartesian
square of `AlgebraicGeometry.Space.isPullback_affineBaseChangeProjection`, so that the
`pushforwardBaseChangeMap_canonical` field holds by `Equiv.apply_symm_apply`. -/
def pushforwardBaseChangeMapOfSquare {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (Z : AffineOver B S hS X) :
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (pushforwardAlgebra B S hS Z.obj).right ⟶
      (pushforwardAlgebra B S hS ((affineBaseChangeFunctor B S hS g).obj Z).obj).right :=
  ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
      (pushforwardAlgebra B S hS Z.obj).right
      (pushforwardAlgebra B S hS ((affineBaseChangeFunctor B S hS g).obj Z).obj).right).symm
    (pushforwardSquareMap B S hS g Z.obj ((affineBaseChangeFunctor B S hS g).obj Z).obj
      (affineBaseChangeProjection B S hS g Z)
      (isPullback_affineBaseChangeProjection B S hS g Z).w)

/-! ### The reduction -/

/-- The pullback of quasi-coherent algebras along `g : Y ⟶ X`, given `hqc`: the pullback of every
quasi-coherent algebra on `X` is quasi-coherent.  This is the functor `F` which the `baseChangeIso`
field of `AlgebraicGeometry.Space.BaseChangeCompatibility` compares with base change of affine
algebraic spaces. -/
def quasicoherentAlgebraPullbackFunctor {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hqc : ∀ A : QuasicoherentAlgebra B S hS X,
      AlgebraSheaf.IsQuasicoherent
        ((_root_.AlgebraicGeometry.Space.algebraPullback B S hS g).obj A.obj)) :
    QuasicoherentAlgebra B S hS X ⥤ QuasicoherentAlgebra B S hS Y :=
  ObjectProperty.lift _ (quasicoherentAlgebraInclusion B S hS X ⋙ algebraPullback B S hS g) hqc

/-- **The base-change clause of Stacks 081V reduced to three assertions.**  Given an
affine-algebra anti-equivalence `E`, the twelve fields of
`AlgebraicGeometry.Space.BaseChangeCompatibility` follow from three: that algebra pullback
preserves quasi-coherence, that `E` commutes with base change, and that the commutation is the
canonical comparison.  The other nine are supplied here and in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`. -/
def BaseChangeCompatibility.ofBaseChangeIso (E : AffineAlgebraAntiEquivalence B S hS)
    (hqc : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (A : QuasicoherentAlgebra B S hS X),
      AlgebraSheaf.IsQuasicoherent
        ((_root_.AlgebraicGeometry.Space.algebraPullback B S hS g).obj A.obj))
    (baseChangeIso : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
      (E.equivalence X).functor ⋙ quasicoherentAlgebraPullbackFunctor B S hS g (hqc g) ≅
        (affineBaseChangeFunctor B S hS g).op ⋙ (E.equivalence Y).functor)
    (baseChangeIso_canonical :
      ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (Z : AffineOver B S hS X),
        (_root_.AlgebraicGeometry.Space.algebraPullbackMap B S hS g).app
            ((E.equivalence X).functor.obj (.op Z)).obj ≫
            ((quasicoherentAlgebraInclusion B S hS Y).map ((baseChangeIso g).hom.app (.op Z)) ≫
              (quasicoherentAlgebraInclusion B S hS Y).map
                ((E.pushforwardIso Y).hom.app
                  (.op ((affineBaseChangeFunctor B S hS g).obj Z))) ≫
              (E.pushforward_obj Y ((affineBaseChangeFunctor B S hS g).obj Z)).hom).right =
          (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
                (smallEtaleRingedToposHom B S hS g).toToposHom).map
              ((quasicoherentAlgebraInclusion B S hS X).map
                  ((E.pushforwardIso X).hom.app (.op Z)) ≫
                (E.pushforward_obj X Z).hom).right ≫
            pushforwardBaseChangeMapOfSquare B S hS g Z) :
    BaseChangeCompatibility B S hS E where
  algebraPullback g := _root_.AlgebraicGeometry.Space.algebraPullback B S hS g
  algebraPullbackMap g := _root_.AlgebraicGeometry.Space.algebraPullbackMap B S hS g
  algebraPullback_isPushout g A :=
    _root_.AlgebraicGeometry.Space.algebraPullback_isPushout B S hS g A
  algebraPullback_isQuasicoherent g A := hqc g A
  affineBaseChange g := affineBaseChangeFunctor B S hS g
  affineBaseChange_projection g Z := affineBaseChangeProjection B S hS g Z
  affineBaseChange_isPullback g Z := isPullback_affineBaseChangeProjection B S hS g Z
  affineBaseChange_projection_naturality :=
    fun {_ _} g {_ _} f => affineBaseChangeProjection_naturality B S hS g f
  baseChangeIso g := baseChangeIso g
  pushforwardBaseChangeMap g Z := pushforwardBaseChangeMapOfSquare B S hS g Z
  pushforwardBaseChangeMap_canonical _ _ := Equiv.apply_symm_apply _ _
  baseChangeIso_canonical g Z := baseChangeIso_canonical g Z

end AlgebraicGeometry.Space

end
