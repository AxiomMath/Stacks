module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardBaseChangeComparison

/-!
# Naturality of the base-change comparison of a direct-image algebra

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  For an algebraic space `Z` affine over `X` with base change `Z' = Y ×_X Z`,
`AlgebraicGeometry.Space.affineOverBaseChangeAlgebraHom` is the comparison of `𝒪_Y`-algebras

`g^* (f_* 𝒪_Z) ⟶ f'_* 𝒪_{Z'}`.

This file proves that it is natural in `Z`: for a morphism `h : Z₁ ⟶ Z₂` of algebraic spaces
affine over `X` the square formed by the two comparisons, the pullback of the direct-image map of
`h` and the direct-image map of the base change of `h` commutes.

## Main results

* `AlgebraicGeometry.Space.pushforwardSquareMap_eq`: the comparison
  `AlgebraicGeometry.Space.pushforwardSquareMap` of a commutative square is the direct-image map
  of its top edge, read over `X`, followed by the inverse of the comparison of iterated direct
  images.
* `AlgebraicGeometry.Space.pushforwardRingMap_comp_pushforwardSquareMap` and
  `AlgebraicGeometry.Space.pushforwardSquareMap_comp_map_pushforwardRingMap`: **the two
  composition laws of the square comparison**, precomposition with the direct-image map of a
  morphism over `X` and postcomposition with the direct image along `g` of the direct-image map
  of a morphism over `Y`.
* `AlgebraicGeometry.Space.map_pushforwardAlgMap_comp_pushforwardCompIso_hom`: the comparison
  of iterated direct images of structure sheaves is natural in the middle algebraic space.
* `AlgebraicGeometry.Space.ringSheafPullback_map_comp_pushforwardSquareBaseChangeMap` and
  `AlgebraicGeometry.Space.algebraPullback_map_comp_baseChangeAlgebraHom`: the base-change
  comparison of an arbitrary commutative square, of sheaves of rings and of algebras, is natural
  in the square.
* `AlgebraicGeometry.Space.affineOverBaseChangeAlgebraHom_naturality`: **the base-change
  comparison is natural in the algebraic space affine over `X`.**

## Implementation notes

Both composition laws are reduced to `AlgebraicGeometry.Space.pushforwardRingMap_comp`, the
composition law of the direct-image map over a single base.  The square comparison of a square
over `g` is the direct-image map, over `X`, of the top edge `W ⟶ Z` with `W` viewed over `X`
through `W ⟶ Y ⟶ X`, followed by the inverse of the comparison
`g_* (f'_* 𝒪_W) ≅ (f' ≫ g)_* 𝒪_W` of iterated direct images; so precomposition is the
composition law directly, and postcomposition is that law together with the naturality of the
comparison of iterated direct images in the algebraic space over `Y`, which is the naturality and
the associativity cocycle of the comparison of Stacks 03G2, part (3), read on sheaves of sets.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A rearrangement of composites used below: if `F.map v ≫ w = x ≫ y` and `F.map u ≫ x = z ≫ t`
then `F.map (u ≫ v) ≫ w = z ≫ t ≫ y`.  Stated separately so that the composites it is applied to
are matched once, with every intervening object fixed by the arguments. -/
private theorem map_comp_comp_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {c₁ c₂ c₃ : C} {d₁ d₂ d₃ : D} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (w : F.obj c₃ ⟶ d₁)
    (x : F.obj c₂ ⟶ d₂) (y : d₂ ⟶ d₁) (z : F.obj c₁ ⟶ d₃) (t : d₃ ⟶ d₂)
    (hvw : F.map v ≫ w = x ≫ y) (hux : F.map u ≫ x = z ≫ t) :
    F.map (u ≫ v) ≫ w = z ≫ t ≫ y := by
  rw [F.map_comp, Category.assoc, hvw, ← Category.assoc, hux, Category.assoc]

/-! ### The comparison of iterated direct images -/

section Iterated

variable {A₁ A₂ A₃ X : AlgebraicSpaces B S hS}

/-- **The comparison of iterated direct images of structure sheaves.**  For `a : A₁ ⟶ A₂` and
`y : A₂ ⟶ X`, the direct image along `y` of the direct image along `a` of `𝒪_{A₁}` is the direct
image along `a ≫ y`: the comparison of iterated direct images of sheaves of commutative rings
followed by the comparison of Stacks 03G8.  These are the last two factors of
`AlgebraicGeometry.Space.pushforwardAlgMap`. -/
def pushforwardCompIso (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).obj
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a).toToposHom).obj
          (smallEtaleRingedTopos B S hS A₁).O) ≅
      (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS (a ≫ y)).toToposHom).obj
          (smallEtaleRingedTopos B S hS A₁).O :=
  pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS y).toToposHom (smallEtaleRingedTopos B S hS A₁).O ≪≫
    (smallEtaleRingedToposHom_compRingIso B S hS a y).app (smallEtaleRingedTopos B S hS A₁).O

/-- The direct-image map of `a` over `y` is the direct image along `y` of the structure map of
`a`, followed by the comparison of iterated direct images. -/
theorem pushforwardAlgMap_eq (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    pushforwardAlgMap B S hS a y =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (smallEtaleRingedToposHom B S hS a).fSharp ≫
        (pushforwardCompIso B S hS a y).hom :=
  rfl

/-- The comparison of iterated direct images, unfolded into its two factors. -/
theorem pushforwardCompIso_hom (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (pushforwardCompIso B S hS a y).hom =
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
          (smallEtaleRingedToposHom B S hS y).toToposHom (smallEtaleRingedTopos B S hS A₁).O).hom ≫
        (smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
          (smallEtaleRingedTopos B S hS A₁).O :=
  rfl

/-- On sheaves of sets the comparison of iterated direct images is the comparison of
Stacks 03G2, part (3). -/
theorem forgetRing_map_pushforwardCompIso_hom (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (smallEtaleRingedTopos B S hS X).forgetRing.map (pushforwardCompIso B S hS a y).hom =
      (smallToposMorphismTypeU_comp B S hS a y).hom.app (structureSetSheaf B S hS A₁) := by
  have hcomp : (smallEtaleRingedTopos B S hS X).forgetRing.map
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS y).toToposHom
        (smallEtaleRingedTopos B S hS A₁).O).hom = 𝟙 _ :=
    pushforwardCommRingCompIso_hom_forget
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS y).toToposHom
      (smallEtaleRingedTopos B S hS A₁).O
  have hiso : (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
          (smallEtaleRingedTopos B S hS A₁).O) =
      (smallToposMorphismTypeU_comp B S hS a y).hom.app (structureSetSheaf B S hS A₁) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS X.1) _ (smallToposMorphismTypeU_comp B S hS a y)
  rw [pushforwardCompIso_hom]
  refine ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _).trans ?_
  refine (congrArg₂ (fun p q => p ≫ q) hcomp hiso).trans ?_
  exact Category.id_comp _

/-- **The comparison of Stacks 03G2, part (3) is natural in the algebraic space over the middle
base**, at the direct-image map of sheaves of sets: the naturality of the comparison for `b, y`
at the structure map of `a`, together with its associativity cocycle for `a, b, y`. -/
theorem map_pushforwardSetMap_comp_smallToposMorphismTypeU_comp (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    (y : A₃ ⟶ X) :
    (smallToposMorphismTypeU B S hS y).pushforward.map (pushforwardSetMap B S hS a b) ≫
          (smallToposMorphismTypeU_comp B S hS (a ≫ b) y).hom.app (structureSetSheaf B S hS A₁) =
        (smallToposMorphismTypeU_comp B S hS b y).hom.app (structureSetSheaf B S hS A₂) ≫
          pushforwardSetMap B S hS a (b ≫ y) := by
  have hnat := (smallToposMorphismTypeU_comp B S hS b y).hom.naturality
    (structureSharpSet B S hS a)
  have hcoc := smallToposMorphismTypeU_comp_assoc B S hS a b y (structureSetSheaf B S hS A₁)
  simp only [pushforwardSetMap]
  refine map_comp_comp_of_eq (smallToposMorphismTypeU B S hS y).pushforward
    ((smallToposMorphismTypeU B S hS b).pushforward.map (structureSharpSet B S hS a))
    ((smallToposMorphismTypeU_comp B S hS a b).hom.app (structureSetSheaf B S hS A₁))
    ((smallToposMorphismTypeU_comp B S hS (a ≫ b) y).hom.app (structureSetSheaf B S hS A₁))
    ((smallToposMorphismTypeU_comp B S hS b y).hom.app
      ((smallToposMorphismTypeU B S hS a).pushforward.obj (structureSetSheaf B S hS A₁)))
    ((smallToposMorphismTypeU_comp B S hS a (b ≫ y)).hom.app (structureSetSheaf B S hS A₁))
    ((smallToposMorphismTypeU_comp B S hS b y).hom.app (structureSetSheaf B S hS A₂))
    ((smallToposMorphismTypeU B S hS (b ≫ y)).pushforward.map (structureSharpSet B S hS a))
    ?_ ?_
  · exact hcoc
  · exact hnat

/-- The left-hand side of
`AlgebraicGeometry.Space.map_pushforwardAlgMap_comp_pushforwardCompIso_hom`, read on sheaves of
sets. -/
theorem forgetRing_map_map_pushforwardAlgMap_comp (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (pushforwardAlgMap B S hS a b) ≫ (pushforwardCompIso B S hS (a ≫ b) y).hom) =
      (smallToposMorphismTypeU B S hS y).pushforward.map (pushforwardSetMap B S hS a b) ≫
        (smallToposMorphismTypeU_comp B S hS (a ≫ b) y).hom.app (structureSetSheaf B S hS A₁) := by
  have e1 : (smallEtaleRingedTopos B S hS X).forgetRing.map
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
        (pushforwardAlgMap B S hS a b)) =
        (smallToposMorphismTypeU B S hS y).pushforward.map (pushforwardSetMap B S hS a b) :=
    (underlyingRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
      (Φ := (smallEtaleRingedToposHom B S hS y).toToposHom.pushforward)
      (pushforwardAlgMap B S hS a b)).trans
      (congrArg (smallToposMorphismTypeU B S hS y).pushforward.map
        (forgetRing_pushforwardAlgMap B S hS a b))
  refine ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _).trans ?_
  rw [e1, forgetRing_map_pushforwardCompIso_hom]
  rfl

/-- The right-hand side of
`AlgebraicGeometry.Space.map_pushforwardAlgMap_comp_pushforwardCompIso_hom`, read on sheaves of
sets. -/
theorem forgetRing_map_pushforwardCompIso_hom_comp (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((pushforwardCompIso B S hS b y).hom ≫ pushforwardAlgMap B S hS a (b ≫ y)) =
      (smallToposMorphismTypeU_comp B S hS b y).hom.app (structureSetSheaf B S hS A₂) ≫
        pushforwardSetMap B S hS a (b ≫ y) := by
  refine ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _).trans ?_
  rw [forgetRing_pushforwardAlgMap, forgetRing_map_pushforwardCompIso_hom]
  rfl

/-- **The comparison of iterated direct images is natural in the algebraic space over the
middle base.**  For `a : A₁ ⟶ A₂`, `b : A₂ ⟶ A₃` and `y : A₃ ⟶ X`, pushing the direct-image map
of `a` over `b` forward along `y` and then comparing is comparing first and then taking the
direct-image map of `a` over `b ≫ y`.

On sheaves of sets this is
`AlgebraicGeometry.Space.map_pushforwardSetMap_comp_smallToposMorphismTypeU_comp`. -/
theorem map_pushforwardAlgMap_comp_pushforwardCompIso_hom (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    (y : A₃ ⟶ X) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
        (pushforwardAlgMap B S hS a b) ≫ (pushforwardCompIso B S hS (a ≫ b) y).hom =
      (pushforwardCompIso B S hS b y).hom ≫ pushforwardAlgMap B S hS a (b ≫ y) :=
  (smallEtaleRingedTopos B S hS X).forgetRing.map_injective
    ((forgetRing_map_map_pushforwardAlgMap_comp B S hS a b y).trans
      ((map_pushforwardSetMap_comp_smallToposMorphismTypeU_comp B S hS a b y).trans
        (forgetRing_map_pushforwardCompIso_hom_comp B S hS a b y).symm))

/-- Transporting the source morphism of the comparison of iterated direct images along an
equality. -/
theorem pushforwardCompIso_inv_comp_map_eqToHom {m m' : A₁ ⟶ A₂} (h : m = m') (y : A₂ ⟶ X) :
    (pushforwardCompIso B S hS m y).inv ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (eqToHom (congrArg (fun q : A₁ ⟶ A₂ =>
            (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
              (smallEtaleRingedTopos B S hS A₁).O) h)) =
      eqToHom (congrArg (fun q : A₁ ⟶ X =>
          (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS A₁).O) (congrArg (fun k => k ≫ y) h)) ≫
        (pushforwardCompIso B S hS m' y).inv := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp]

/-- The inverse comparison of iterated direct images, read through the direct-image maps:
`AlgebraicGeometry.Space.map_pushforwardAlgMap_comp_pushforwardCompIso_hom` with the two
comparisons inverted. -/
theorem pushforwardCompIso_inv_comp_map_pushforwardAlgMap (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    (y : A₃ ⟶ X) :
    (pushforwardCompIso B S hS b y).inv ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (pushforwardAlgMap B S hS a b) =
      pushforwardAlgMap B S hS a (b ≫ y) ≫ (pushforwardCompIso B S hS (a ≫ b) y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact map_pushforwardAlgMap_comp_pushforwardCompIso_hom B S hS a b y

end Iterated

/-! ### The square comparison and its two composition laws -/

section Rearrange

variable {C D : Type*} [Category C] [Category D]

/-- Reassociation of a composite of six morphisms. -/
private theorem comp_assoc_six {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : C} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃)
    (d : P₃ ⟶ P₄) (e : P₄ ⟶ P₅) (f : P₅ ⟶ P₆) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = (a ≫ b ≫ c ≫ d) ≫ e ≫ f := by
  simp only [Category.assoc]

/-- `x ≫ y ≫ j = z ≫ j` as soon as `z = x ≫ y`. -/
private theorem comp_comp_eq_of_eq {P Q R T : C} (x : P ⟶ Q) (y : Q ⟶ R) (j : R ⟶ T) (z : P ⟶ R)
    (hz : z = x ≫ y) : x ≫ y ≫ j = z ≫ j := by
  rw [hz, Category.assoc]

/-- `(x ≫ i) ≫ y = z ≫ j` as soon as `i ≫ y = w ≫ j` and `z = x ≫ w`. -/
private theorem comp_comp_eq_of_eq' {P Q R T V : C} (x : P ⟶ Q) (i : Q ⟶ R) (y : R ⟶ V) (w : Q ⟶ T)
    (j : T ⟶ V) (z : P ⟶ T) (h : i ≫ y = w ≫ j) (hz : z = x ≫ w) : (x ≫ i) ≫ y = z ≫ j := by
  rw [Category.assoc, h, hz, Category.assoc]

/-- Moving a morphism past the image of a composite in two steps. -/
private theorem comp_map_comp_of_eq (G : C ⥤ D) {P R R' : D} {Q Q' Q'' : C}
    (i : P ⟶ G.obj Q) (m : Q ⟶ Q') (n : Q' ⟶ Q'') (m' : P ⟶ R) (i' : R ⟶ G.obj Q')
    (n' : R ⟶ R') (j : R' ⟶ G.obj Q'') (h₁ : i ≫ G.map m = m' ≫ i')
    (h₂ : i' ≫ G.map n = n' ≫ j) : i ≫ G.map (m ≫ n) = (m' ≫ n') ≫ j := by
  rw [G.map_comp, ← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Two maps out of a common source agree after `m ≫ c₁` and `c₂ ≫ r` once the first leg is
moved past `m` and both sides are identified. -/
private theorem comp_comp_eq_comp_comp_of_eq {P Q Q' R T V : C} (x : P ⟶ Q) (m : Q ⟶ Q')
    (c₁ : Q' ⟶ V) (c₂ : Q ⟶ T) (r : T ⟶ V) (n : P ⟶ R) (x' : R ⟶ Q') (P₁ : R ⟶ V)
    (P₂ : P ⟶ T) (hnat : x ≫ m = n ≫ x') (h₁ : x' ≫ c₁ = P₁) (h₂ : x ≫ c₂ = P₂)
    (hk : n ≫ P₁ = P₂ ≫ r) : x ≫ m ≫ c₁ = x ≫ c₂ ≫ r := by
  rw [← Category.assoc, hnat, Category.assoc, h₁, hk, ← h₂, Category.assoc]

/-- `s ≫ m ≫ c₁ = s ≫ c₂ ≫ r` from `s ≫ m = s'`, `s' ≫ c₁ = q₁`, `s ≫ c₂ = q₂` and
`q₂ ≫ r = q₁`. -/
private theorem comp_comp_eq_comp_comp_of_eq' {P Q Q' T V : C} (s : P ⟶ Q) (m : Q ⟶ Q')
    (c₁ : Q' ⟶ V) (c₂ : Q ⟶ T) (r : T ⟶ V) (s' : P ⟶ Q') (q₁ : P ⟶ V) (q₂ : P ⟶ T)
    (h₀ : s ≫ m = s') (h₁ : s' ≫ c₁ = q₁) (h₂ : s ≫ c₂ = q₂) (h₃ : q₂ ≫ r = q₁) :
    s ≫ m ≫ c₁ = s ≫ c₂ ≫ r := by
  rw [← Category.assoc, h₀, h₁, ← h₃, ← h₂, Category.assoc]

end Rearrange

section Squares

variable {X Y : AlgebraicSpaces B S hS}

/-- An algebraic space `W` over `Y`, read over `X` through `g : Y ⟶ X`. -/
abbrev overComp (g : Y ⟶ X) (W : Over Y) : Over X :=
  Over.mk (W.hom ≫ g)

/-- A morphism over `Y`, read as a morphism over `X` through `g : Y ⟶ X`. -/
abbrev overCompMap (g : Y ⟶ X) {W₁ W₂ : Over Y} (t : W₁ ⟶ W₂) :
    overComp B S hS g W₁ ⟶ overComp B S hS g W₂ :=
  Over.homMk t.left (show t.left ≫ W₂.hom ≫ g = W₁.hom ≫ g by
    rw [← Category.assoc, Over.w t])

/-- **The square comparison is a direct-image map over `X` followed by the comparison of
iterated direct images.**  For a commutative square over `g` with top edge `p : W ⟶ Z`, the
comparison `f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_W)` is the direct-image map of `p`, as a morphism over `X`
from `W` viewed over `X` to `Z`, followed by the inverse of
`g_* (f'_* 𝒪_W) ≅ (f' ≫ g)_* 𝒪_W`. -/
theorem pushforwardSquareMap_eq (g : Y ⟶ X) (Z : Over X) (W : Over Y) (p : W.left ⟶ Z.left)
    (hw : p ≫ Z.hom = W.hom ≫ g) :
    pushforwardSquareMap B S hS g Z W p hw =
      pushforwardRingMap B S hS (Over.homMk p hw : overComp B S hS g W ⟶ Z) ≫
        (pushforwardCompIso B S hS W.hom g).inv :=
  comp_assoc_six
    ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom).map
      (smallEtaleRingedToposHom B S hS p).fSharp)
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS p).toToposHom
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom
        (smallEtaleRingedTopos B S hS W.left).O).hom
    ((smallEtaleRingedToposHom_compRingIso B S hS p Z.hom).hom.app
      (smallEtaleRingedTopos B S hS W.left).O)
    (eqToHom (congrArg
      (fun q : W.left ⟶ X =>
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS W.left).O)
      hw))
    ((smallEtaleRingedToposHom_compRingIso B S hS W.hom g).inv.app
      (smallEtaleRingedTopos B S hS W.left).O)
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS W.hom).toToposHom
      (smallEtaleRingedToposHom B S hS g).toToposHom
      (smallEtaleRingedTopos B S hS W.left).O).inv

/-- The square comparison depends on its top edge only, not on the proof that the square
commutes. -/
theorem pushforwardSquareMap_congr (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    {p p' : W.left ⟶ Z.left} (h : p = p') (hw : p ≫ Z.hom = W.hom ≫ g)
    (hw' : p' ≫ Z.hom = W.hom ≫ g) :
    pushforwardSquareMap B S hS g Z W p hw = pushforwardSquareMap B S hS g Z W p' hw' := by
  subst h
  rfl

/-- **Precomposition law of the square comparison.**  For a morphism `h : Z₁ ⟶ Z₂` over `X`,
the direct-image map of `h` followed by the comparison of a square with top edge `p : W ⟶ Z₁` is
the comparison of the square with top edge `p ≫ h`. -/
theorem pushforwardRingMap_comp_pushforwardSquareMap (g : Y ⟶ X) {Z₁ Z₂ : Over X}
    (h : Z₁ ⟶ Z₂) (W : Over Y) (p : W.left ⟶ Z₁.left) (hw : p ≫ Z₁.hom = W.hom ≫ g) :
    pushforwardRingMap B S hS h ≫ pushforwardSquareMap B S hS g Z₁ W p hw =
      pushforwardSquareMap B S hS g Z₂ W (p ≫ h.left)
        (by rw [Category.assoc, Over.w h, hw]) := by
  have e : (Over.homMk (p ≫ h.left) (by rw [Category.assoc, Over.w h, hw]; rfl) :
      overComp B S hS g W ⟶ Z₂) = Over.homMk p hw ≫ h := by
    ext
    simp
  rw [pushforwardSquareMap_eq, pushforwardSquareMap_eq]
  exact comp_comp_eq_of_eq _ _ _ _
    ((congrArg (pushforwardRingMap B S hS) e).trans (pushforwardRingMap_comp B S hS _ _))

/-- The inverse comparison of iterated direct images is natural in the algebraic space over
`Y`: for `t : W₁ ⟶ W₂` over `Y`, pushing the direct-image map of `t` forward along `g` after the
inverse comparison is the inverse comparison after the direct-image map of `t` read over `X`. -/
theorem pushforwardCompIso_inv_comp_map_pushforwardRingMap (g : Y ⟶ X) {W₁ W₂ : Over Y}
    (t : W₁ ⟶ W₂) :
    (pushforwardCompIso B S hS W₂.hom g).inv ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
          (pushforwardRingMap B S hS t) =
      pushforwardRingMap B S hS (overCompMap B S hS g t) ≫
        (pushforwardCompIso B S hS W₁.hom g).inv := by
  have h₁ := pushforwardCompIso_inv_comp_map_pushforwardAlgMap B S hS t.left W₂.hom g
  have h₂ := pushforwardCompIso_inv_comp_map_eqToHom B S hS (Over.w t) g
  rw [pushforwardRingMap_eq B S hS t, pushforwardRingMap_eq B S hS (overCompMap B S hS g t)]
  exact comp_map_comp_of_eq _ _ _ _ _ _ _ _ h₁ h₂

/-- **Postcomposition law of the square comparison.**  For a morphism `t : W₁ ⟶ W₂` over `Y`,
the comparison of a square with top edge `p : W₂ ⟶ Z` followed by the direct image along `g` of
the direct-image map of `t` is the comparison of the square with top edge `t ≫ p`. -/
theorem pushforwardSquareMap_comp_map_pushforwardRingMap (g : Y ⟶ X) (Z : Over X)
    {W₁ W₂ : Over Y} (t : W₁ ⟶ W₂) (p : W₂.left ⟶ Z.left) (hw : p ≫ Z.hom = W₂.hom ≫ g) :
    pushforwardSquareMap B S hS g Z W₂ p hw ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
          (pushforwardRingMap B S hS t) =
      pushforwardSquareMap B S hS g Z W₁ (t.left ≫ p)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w t]) := by
  have e : (Over.homMk (t.left ≫ p)
        (show (t.left ≫ p) ≫ Z.hom = W₁.hom ≫ g by
          rw [Category.assoc, hw, ← Category.assoc, Over.w t]) :
      overComp B S hS g W₁ ⟶ Z) =
      overCompMap B S hS g t ≫ (Over.homMk p hw : overComp B S hS g W₂ ⟶ Z) := by
    ext
    simp
  rw [pushforwardSquareMap_eq, pushforwardSquareMap_eq]
  exact comp_comp_eq_of_eq' _ _ _ _ _ _
    (pushforwardCompIso_inv_comp_map_pushforwardRingMap B S hS g t)
    ((congrArg (pushforwardRingMap B S hS) e).trans (pushforwardRingMap_comp B S hS _ _))

end Squares

/-! ### Naturality of the base-change comparison -/

section Naturality

variable {X Y : AlgebraicSpaces B S hS}

/-- **The base-change comparison of a commutative square is natural in the square.**  For a
morphism `h : Z₁ ⟶ Z₂` over `X`, a morphism `t : W₁ ⟶ W₂` over `Y` and squares over `g` with
top edges `p₁ : W₁ ⟶ Z₁` and `p₂ : W₂ ⟶ Z₂` compatible with `h` and `t`, the inverse image of
the direct-image map of `h` followed by the comparison of the first square is the comparison of
the second square followed by the direct-image map of `t`.

Across the adjunction this is the two composition laws of the square comparison,
`AlgebraicGeometry.Space.pushforwardRingMap_comp_pushforwardSquareMap` and
`AlgebraicGeometry.Space.pushforwardSquareMap_comp_map_pushforwardRingMap`. -/
theorem ringSheafPullback_map_comp_pushforwardSquareBaseChangeMap (g : Y ⟶ X)
    {Z₁ Z₂ : Over X} (h : Z₁ ⟶ Z₂) {W₁ W₂ : Over Y} (t : W₁ ⟶ W₂)
    (p₁ : W₁.left ⟶ Z₁.left) (hw₁ : p₁ ≫ Z₁.hom = W₁.hom ≫ g)
    (p₂ : W₂.left ⟶ Z₂.left) (hw₂ : p₂ ≫ Z₂.hom = W₂.hom ≫ g)
    (hsq : p₁ ≫ h.left = t.left ≫ p₂) :
    (ringSheafPullback B S hS g).map (pushforwardRingMap B S hS h) ≫
        pushforwardSquareBaseChangeMap B S hS g Z₁ W₁ p₁ hw₁ =
      pushforwardSquareBaseChangeMap B S hS g Z₂ W₂ p₂ hw₂ ≫ pushforwardRingMap B S hS t := by
  have key :
      ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
                (smallEtaleRingedToposHom B S hS g).toToposHom).map
              (pushforwardRingMap B S hS h) ≫
            pushforwardSquareBaseChangeMap B S hS g Z₁ W₁ p₁ hw₁) =
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          (pushforwardSquareBaseChangeMap B S hS g Z₂ W₂ p₂ hw₂ ≫
            pushforwardRingMap B S hS t) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      pushforwardSquareBaseChangeMap_canonical, pushforwardSquareBaseChangeMap_canonical,
      pushforwardRingMap_comp_pushforwardSquareMap,
      pushforwardSquareMap_comp_map_pushforwardRingMap]
    exact pushforwardSquareMap_congr B S hS g Z₂ W₁ hsq _ _
  exact ((commRingImageAdjunction
    (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _).injective key

/-- **The base-change comparison of `𝒪_Y`-algebras of a commutative square is natural in the
square**, on underlying sheaves of rings.  Both sides are maps out of the pushout
`g^* (f_* 𝒪_{Z₂})`; on the inverse image of `f_* 𝒪_{Z₂}` this is
`AlgebraicGeometry.Space.ringSheafPullback_map_comp_pushforwardSquareBaseChangeMap`, and on
`𝒪_Y` both sides are the structure map of `f'_* 𝒪_{W₁}`. -/
theorem algebraPullback_map_comp_baseChangeAlgebraHom (g : Y ⟶ X)
    {Z₁ Z₂ : Over X} (h : Z₁ ⟶ Z₂) {W₁ W₂ : Over Y} (t : W₁ ⟶ W₂)
    (p₁ : W₁.left ⟶ Z₁.left) (hw₁ : p₁ ≫ Z₁.hom = W₁.hom ≫ g)
    (p₂ : W₂.left ⟶ Z₂.left) (hw₂ : p₂ ≫ Z₂.hom = W₂.hom ≫ g)
    (hsq : p₁ ≫ h.left = t.left ≫ p₂) :
    ((algebraPullback B S hS g).map (pushforwardAlgebraMap B S hS h)).right ≫
        baseChangeAlgebraHom B S hS g Z₁ W₁ p₁ hw₁ =
      baseChangeAlgebraHom B S hS g Z₂ W₂ p₂ hw₂ ≫ pushforwardRingMap B S hS t := by
  refine (algebraPullback_isPushout B S hS g (pushforwardAlgebra B S hS Z₂)).hom_ext ?_ ?_
  · exact comp_comp_eq_comp_comp_of_eq _ _ _ _ _ _ _ _ _
      ((algebraPullbackMap B S hS g).naturality (pushforwardAlgebraMap B S hS h)).symm
      (algebraPullbackMap_comp_baseChangeAlgebraHom B S hS g Z₁ W₁ p₁ hw₁)
      (algebraPullbackMap_comp_baseChangeAlgebraHom B S hS g Z₂ W₂ p₂ hw₂)
      (ringSheafPullback_map_comp_pushforwardSquareBaseChangeMap B S hS g h t p₁ hw₁ p₂ hw₂ hsq)
  · exact comp_comp_eq_comp_comp_of_eq' _ _ _ _ _ _ _ _
      (AlgebraSheaf.hom_comp_right
        ((algebraPullback B S hS g).map (pushforwardAlgebraMap B S hS h)))
      (baseChangeAlgebraHom_structure B S hS g Z₁ W₁ p₁ hw₁)
      (baseChangeAlgebraHom_structure B S hS g Z₂ W₂ p₂ hw₂)
      (fSharp_comp_pushforwardRingMap B S hS t)

/-- **The base-change comparison of `𝒪_Y`-algebras is natural in the algebraic space affine over
`X`.**  For a morphism `φ : Z₁ ⟶ Z₂` of algebraic spaces affine over `X`, the square

```
g^* (f₂_* 𝒪_{Z₂}) ⟶ (f₂')_* 𝒪_{Y ×_X Z₂}
       ↓                       ↓
g^* (f₁_* 𝒪_{Z₁}) ⟶ (f₁')_* 𝒪_{Y ×_X Z₁}
```

of `𝒪_Y`-algebras commutes, the vertical maps being the pullback of the direct-image map of `φ`
and the direct-image map of its base change. -/
@[stacks 081V "naturality in Z of the base-change comparison g^*(f_* 𝒪_Z) ⟶ f'_* 𝒪_{Y ×_X Z}"]
theorem affineOverBaseChangeAlgebraHom_naturality (g : Y ⟶ X) {Z₁ Z₂ : AffineOver B S hS X}
    (φ : Z₁ ⟶ Z₂) :
    (algebraPullback B S hS g).map (pushforwardAlgebraMap B S hS φ.hom) ≫
        affineOverBaseChangeAlgebraHom B S hS g Z₁ =
      affineOverBaseChangeAlgebraHom B S hS g Z₂ ≫
        pushforwardAlgebraMap B S hS (affineOverBaseChangeMap B S hS g φ).hom :=
  AlgebraSheaf.Hom.ext
    (algebraPullback_map_comp_baseChangeAlgebraHom B S hS g φ.hom
      (affineOverBaseChangeMap B S hS g φ).hom _ _ _ _
      (affineOverBaseChangeMap_comp_projection B S hS g φ).symm)

end Naturality

end AlgebraicGeometry.Space

end
