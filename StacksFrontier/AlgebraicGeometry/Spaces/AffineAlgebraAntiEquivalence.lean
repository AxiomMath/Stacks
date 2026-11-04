module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Affine algebraic spaces and quasi-coherent algebras

The algebraic spaces affine over an algebraic space `X` are anti-equivalent to the quasi-coherent
sheaves of commutative `𝒪_X`-algebras, by an anti-equivalence that sends `f : Y ⟶ X` to
`f_* 𝒪_Y` and is compatible with arbitrary base change. This file defines the two categories,
the direct-image algebra and its action on morphisms, and the structures recording an
anti-equivalence of this kind and its compatibility with base change.

## Main definitions

* `AlgebraicGeometry.Space.AffineOver` is the category of algebraic spaces affine over an
  algebraic space `X`, and `AlgebraicGeometry.Space.QuasicoherentAlgebra` the category of
  quasi-coherent sheaves of commutative `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.pushforwardAlgebra` is the direct image `f_* 𝒪_Y` of the structure
  sheaf of an algebraic space over `X`, as a sheaf of algebras on the small étale site of `X`,
  and `AlgebraicGeometry.Space.pushforwardRingMap` is its contravariant action on a morphism
  over `X`.
* `AlgebraicGeometry.Space.pushforwardSquareMap` is the comparison `f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_W)`
  attached to a commutative square over `g : Y ⟶ X`, whose adjunct is the base-change comparison
  `g⁻¹ f_* 𝒪_Z ⟶ f'_* 𝒪_W`.
* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` packages the anti-equivalence together
  with its identification with direct image, and
  `AlgebraicGeometry.Space.BaseChangeCompatibility` packages compatibility with arbitrary base
  change.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two categories -/

/-- Algebraic spaces affine over a fixed algebraic space. -/
abbrev AffineOver (X : AlgebraicSpaces B S hS) :=
  ObjectProperty.FullSubcategory (fun f : Over X ↦ IsAffineHom B S hS f.hom.hom)

/-- Quasi-coherent sheaves of commutative `𝒪_X`-algebras. -/
abbrev QuasicoherentAlgebra (X : AlgebraicSpaces B S hS) :=
  ObjectProperty.FullSubcategory
    (AlgebraSheaf.IsQuasicoherent :
      ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2))

/-- The inclusion of the quasi-coherent algebras on `X` into all algebra sheaves on `X`. -/
abbrev quasicoherentAlgebraInclusion (X : AlgebraicSpaces B S hS) :
    QuasicoherentAlgebra B S hS X ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.ι
    (AlgebraSheaf.IsQuasicoherent :
      ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2))

/-! ### The direct-image algebra -/

/-- The sheaf of algebras `f_* 𝒪_Y` for an algebraic space `Y` over `X`, with the algebra
structure given by the structure map `f♯ : 𝒪_X ⟶ f_* 𝒪_Y`. -/
def pushforwardAlgebra {X : AlgebraicSpaces B S hS} (f : Over X) :
    AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  AlgebraSheaf.ofHom (smallEtaleRingedToposHom B S hS f.hom).fSharp

/-- The map on direct-image ring sheaves induced by a morphism over `X`. -/
def pushforwardRingMap {X : AlgebraicSpaces B S hS} {Y Z : Over X} (f : Y ⟶ Z) :
    (pushforwardAlgebra B S hS Z).right ⟶ (pushforwardAlgebra B S hS Y).right :=
  (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom).map
      (smallEtaleRingedToposHom B S hS f.left).fSharp ≫
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f.left).toToposHom
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom
        (smallEtaleRingedTopos B S hS Y.left).O).hom ≫
    (smallEtaleRingedToposHom_compRingIso B S hS f.left Z.hom).hom.app
      (smallEtaleRingedTopos B S hS Y.left).O ≫
    eqToHom (congrArg
      (fun q : Y.left ⟶ X ↦
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y.left).O)
      (Over.w f))

/-- The canonical comparison attached to a commutative square

```
W ⟶ Z
↓     ↓
Y ⟶ X
```

over `g : Y ⟶ X`: the map `f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_W)` of sheaves of commutative rings on the
small étale site of `X` induced by the top projection `p : W ⟶ Z`. Its adjunct is the
base-change comparison `g⁻¹ f_* 𝒪_Z ⟶ f'_* 𝒪_W`. -/
def pushforwardSquareMap {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (pushforwardAlgebra B S hS Z).right ⟶
      (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS g).toToposHom).obj
          (pushforwardAlgebra B S hS W).right :=
  (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom).map
      (smallEtaleRingedToposHom B S hS p).fSharp ≫
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS p).toToposHom
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom
        (smallEtaleRingedTopos B S hS W.left).O).hom ≫
    (smallEtaleRingedToposHom_compRingIso B S hS p Z.hom).hom.app
      (smallEtaleRingedTopos B S hS W.left).O ≫
    eqToHom (congrArg
      (fun q : W.left ⟶ X ↦
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS W.left).O)
      hw) ≫
    (smallEtaleRingedToposHom_compRingIso B S hS W.hom g).inv.app
      (smallEtaleRingedTopos B S hS W.left).O ≫
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS W.hom).toToposHom
      (smallEtaleRingedToposHom B S hS g).toToposHom
      (smallEtaleRingedTopos B S hS W.left).O).inv

/-! ### The anti-equivalence and its compatibility with base change -/

/-- Data of the anti-equivalence between the algebraic spaces affine over `X` and the
quasi-coherent `𝒪_X`-algebras, naturally identified with direct image. -/
structure AffineAlgebraAntiEquivalence where
  /-- The anti-equivalence over each algebraic space. -/
  equivalence : ∀ X : AlgebraicSpaces B S hS,
    (AffineOver B S hS X)ᵒᵖ ≌ QuasicoherentAlgebra B S hS X
  /-- Contravariant direct image of structure sheaves. -/
  pushforward : ∀ X : AlgebraicSpaces B S hS,
    (AffineOver B S hS X)ᵒᵖ ⥤ QuasicoherentAlgebra B S hS X
  /-- Its value on an affine morphism is that morphism's pushed-forward structure sheaf. -/
  pushforward_obj : ∀ (X : AlgebraicSpaces B S hS) (Y : AffineOver B S hS X),
    (quasicoherentAlgebraInclusion B S hS X).obj ((pushforward X).obj (.op Y)) ≅
      pushforwardAlgebra B S hS Y.obj
  /-- The action on morphisms is the canonical map on direct-image rings. -/
  pushforward_map : ∀ (X : AlgebraicSpaces B S hS) {Y Z : AffineOver B S hS X} (f : Y ⟶ Z),
    ((pushforward_obj X Z).inv ≫
      (quasicoherentAlgebraInclusion B S hS X).map ((pushforward X).map f.op) ≫
      (pushforward_obj X Y).hom).right =
      pushforwardRingMap B S hS f.hom
  /-- The anti-equivalence is naturally the direct-image functor. -/
  pushforwardIso : ∀ X : AlgebraicSpaces B S hS,
    (equivalence X).functor ≅ pushforward X

/-- Compatibility of an affine-algebra anti-equivalence with arbitrary base change. -/
structure BaseChangeCompatibility (E : AffineAlgebraAntiEquivalence B S hS) where
  /-- Pullback of algebra sheaves along an arbitrary morphism. -/
  algebraPullback : ∀ {X Y : AlgebraicSpaces B S hS} (_g : Y ⟶ X),
    AlgebraSheaf.{u, u} B S hS X.1 X.2 ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2
  /-- The canonical inverse-image map into the pulled-back algebra. -/
  algebraPullbackMap : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    AlgebraSheaf.forget ⋙
        inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS g).toToposHom ⟶
      algebraPullback g ⋙ AlgebraSheaf.forget
  /-- Algebra pullback is extension of scalars. -/
  algebraPullback_isPushout : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (A : AlgebraSheaf.{u, u} B S hS X.1 X.2),
    IsPushout
      ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS g).toToposHom).map A.hom)
      (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
      ((algebraPullbackMap g).app A)
      ((algebraPullback g).obj A).hom
  /-- Pullback preserves quasi-coherence. -/
  algebraPullback_isQuasicoherent : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (A : QuasicoherentAlgebra B S hS X),
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A.obj)
  /-- Base change of affine algebraic spaces. -/
  affineBaseChange : ∀ {X Y : AlgebraicSpaces B S hS} (_g : Y ⟶ X),
    AffineOver B S hS X ⥤ AffineOver B S hS Y
  /-- The projection from a geometric base change to its original space. -/
  affineBaseChange_projection : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (Z : AffineOver B S hS X),
    ((affineBaseChange g).obj Z).obj.left ⟶ Z.obj.left
  /-- The geometric base change is a cartesian square. -/
  affineBaseChange_isPullback : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (Z : AffineOver B S hS X),
    IsPullback (affineBaseChange_projection g Z)
      ((affineBaseChange g).obj Z).obj.hom Z.obj.hom g
  /-- The projections are natural in the affine space being base-changed. -/
  affineBaseChange_projection_naturality :
    ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) {Z Z' : AffineOver B S hS X} (f : Z ⟶ Z'),
      ((affineBaseChange g).map f).hom.left ≫ affineBaseChange_projection g Z' =
        affineBaseChange_projection g Z ≫ f.hom.left
  /-- The equivalence commutes naturally with arbitrary base change. -/
  baseChangeIso : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    let F : QuasicoherentAlgebra B S hS X ⥤ QuasicoherentAlgebra B S hS Y :=
      ObjectProperty.lift _ (quasicoherentAlgebraInclusion B S hS X ⋙ algebraPullback g)
        (algebraPullback_isQuasicoherent g)
    (E.equivalence X).functor ⋙ F ≅ (affineBaseChange g).op ⋙ (E.equivalence Y).functor
  /-- The comparison from the inverse image of the direct image to the direct image of the
  geometric base change. -/
  pushforwardBaseChangeMap : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (Z : AffineOver B S hS X),
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (pushforwardAlgebra B S hS Z.obj).right ⟶
      (pushforwardAlgebra B S hS ((affineBaseChange g).obj Z).obj).right
  /-- The comparison is adjoint to the map induced by the fibre-product projection on structure
  sheaves. -/
  pushforwardBaseChangeMap_canonical :
    ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (Z : AffineOver B S hS X),
      (commRingImageAdjunction
            (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          (pushforwardAlgebra B S hS Z.obj).right
          (pushforwardAlgebra B S hS ((affineBaseChange g).obj Z).obj).right
          (pushforwardBaseChangeMap g Z) =
        pushforwardSquareMap B S hS g Z.obj ((affineBaseChange g).obj Z).obj
          (affineBaseChange_projection g Z) (affineBaseChange_isPullback g Z).w
  /-- Under the direct-image identifications, the base-change isomorphism is the canonical
  comparison adjoint to the projection. -/
  baseChangeIso_canonical : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
      (Z : AffineOver B S hS X),
    (algebraPullbackMap g).app ((E.equivalence X).functor.obj (.op Z)).obj ≫
        ((quasicoherentAlgebraInclusion B S hS Y).map ((baseChangeIso g).hom.app (.op Z)) ≫
          (quasicoherentAlgebraInclusion B S hS Y).map
            ((E.pushforwardIso Y).hom.app (.op ((affineBaseChange g).obj Z))) ≫
          (E.pushforward_obj Y ((affineBaseChange g).obj Z)).hom).right =
      (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS g).toToposHom).map
          ((quasicoherentAlgebraInclusion B S hS X).map
              ((E.pushforwardIso X).hom.app (.op Z)) ≫
            (E.pushforward_obj X Z).hom).right ≫
        pushforwardBaseChangeMap g Z

end AlgebraicGeometry.Space

end
