module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The functor of isomorphism classes of infinitesimal lifts (Stacks 0DNS): the data

Let `𝒳` be an algebraic stack over `S` and `(A' → A, x)` a deformation situation, written as an
arrow `i : U ⟶ U'` of affine objects of the big affine fppf site of `S` together with an object
`x` of `𝒳` over `U`. Stacks 0DNS considers the functor
`F : B' ↦ {lifts of x|_{B' ⊗_{A'} A} to B'}/isomorphism` on `(Aff/Spec A')_{fppf}`, the
localization at `U'` of the big affine fppf site. This file sets up the data in terms of which
that functor is described:

* `Deformation.Artin.LiftClassSheaf.Restriction`: an affine object presenting
  `Spec (B' ⊗_{A'} A)` together with the restriction `x|_{B' ⊗_{A'} A}`, a strongly cartesian
  arrow to `x`;
* `Deformation.Artin.LiftClassSheaf.InfinitesimalLift`: an object of the category of lifts
  `Lift(x|_{B' ⊗_{A'} A}, B')`;
* `Deformation.Artin.LiftClassSheaf.InfinitesimalLift.Isomorphic`: isomorphism in that category;
* `Deformation.Artin.LiftClassSheaf.InfinitesimalLift.IsRestrictionAlong`: the base-change
  relation computing the restriction maps of `F`;
* `Deformation.Artin.LiftClassSheaf.LiftClassPresheaf`: the functor `F` on `Over U'` with that
  characterization of its values and restriction maps.

## Implementation notes

The definitions are those of the statement of Stacks 0DNS: isomorphism classes are described by a
surjection from the type of lifts whose fibres are the isomorphism classes, and the restriction
maps by the base-change relation on lifts; together these determine `F` up to canonical
isomorphism. The values live in `Type (u + 1)`, the universe of the objects of a stack over the
site.

## References

* [Stacks Project, Tag 0DNS](https://stacks.math.columbia.edu/tag/0DNS)
* [Stacks Project, Tag 06JE](https://stacks.math.columbia.edu/tag/06JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin.LiftClassSheaf

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on global sections induced by a morphism of affine objects of the site over `S`. -/
abbrev ringMap {V W : BigAffineFppf B S hS} (f : V ⟶ W) :=
  ((BigAffineFppf.toScheme B S hS).map f).appTop

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  {U U' : BigAffineFppf B S hS} (i : U ⟶ U') (x : 𝒳.val.val.obj)
  (hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U)

/-- The restriction `x|_{B' ⊗_{A'} A}` of the object of a deformation situation `i : U ⟶ U'` to an
affine `W = Spec B'` over `U' = Spec A'`: an affine object of the site presenting
`Spec (B' ⊗_{A'} A)`, its two structure maps, and the strongly cartesian arrow exhibiting an
object of the stack over it as the restriction of `x`. -/
structure Restriction
    (_hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U) (W : Over U') where
  /-- The affine object of the site presenting `Spec (B' ⊗_{A'} A)`. -/
  base : BigAffineFppf B S hS
  /-- Its projection to `W = Spec B'`. -/
  toCover : base ⟶ W.left
  /-- Its projection to `U = Spec A`. -/
  toDef : base ⟶ U
  /-- The square of affine objects commutes. -/
  comm : toDef ≫ i = toCover ≫ W.hom
  /-- On global sections the square is a pushout, i.e. `base = Spec (B' ⊗_{A'} A)`. -/
  isPushout : IsPushout (ringMap B S hS i) (ringMap B S hS W.hom)
    (ringMap B S hS toDef) (ringMap B S hS toCover)
  /-- The object of the stack playing the role of `x|_{B' ⊗_{A'} A}`. -/
  obj : 𝒳.val.val.obj
  /-- Its arrow to `x`. -/
  hom : obj ⟶ x
  /-- The arrow to `x` is strongly cartesian over `Spec (B' ⊗_{A'} A) → Spec A`. -/
  isCartesian :
    𝒳.val.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map toDef) hom

/-- An object of the category `Lift(x|_{B' ⊗_{A'} A}, B')` of lifts: an object of the stack
over `W = Spec B'` together with a strongly cartesian arrow from the restriction
`x|_{B' ⊗_{A'} A}` lying over `Spec (B' ⊗_{A'} A) → Spec B'`. -/
structure InfinitesimalLift {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W) where
  /-- The lifted object, over `W = Spec B'`. -/
  obj : 𝒳.val.val.obj
  /-- The arrow from the restriction of `x`. -/
  hom : r.obj ⟶ obj
  /-- The arrow from the restriction is strongly cartesian. -/
  isCartesian :
    𝒳.val.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map r.toCover) hom

/-- Two lifts are isomorphic in the category of lifts: there is an isomorphism of the
underlying objects lying over the identity of `W = Spec B'` and commuting with the two
arrows from the restriction of `x`. -/
def InfinitesimalLift.Isomorphic {W : Over U'} {r : Restriction B S hS 𝒳 i x hx W}
    (l m : InfinitesimalLift B S hS 𝒳 i x hx r) : Prop :=
  ∃ φ : l.obj ⟶ m.obj, IsIso φ ∧
    𝒳.val.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj W.left)) φ ∧
      l.hom ≫ φ = m.hom

/-- The base-change relation on lifts: `m` is a restriction of `l` along `g : W₂ ⟶ W₁`.
The two presentations of the tensor products are compared by a morphism of affine objects
over `g` and `U`, the restrictions of `x` by the arrow it induces, and the lifted objects by
a strongly cartesian arrow over `g` commuting with the arrows from the restrictions. -/
def InfinitesimalLift.IsRestrictionAlong {W₁ W₂ : Over U'}
    {r₁ : Restriction B S hS 𝒳 i x hx W₁} {r₂ : Restriction B S hS 𝒳 i x hx W₂} (g : W₂ ⟶ W₁)
    (l : InfinitesimalLift B S hS 𝒳 i x hx r₁) (m : InfinitesimalLift B S hS 𝒳 i x hx r₂) :
    Prop :=
  ∃ (b : r₂.base ⟶ r₁.base) (ψ : r₂.obj ⟶ r₁.obj) (φ : m.obj ⟶ l.obj),
    b ≫ r₁.toCover = r₂.toCover ≫ g.left ∧ b ≫ r₁.toDef = r₂.toDef ∧
      𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map b) ψ ∧ ψ ≫ r₁.hom = r₂.hom ∧
      𝒳.val.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map g.left) φ ∧
      m.hom ≫ φ = ψ ≫ l.hom

/-- The functor `F : B' ↦ {lifts of x|_{B' ⊗_{A'} A} to B'}/isomorphism` of Stacks 0DNS on the
big affine fppf site of `U' = Spec A'`, together with the characterization of its values and of
its restriction maps: the restriction of `x` exists over every affine `A'`-algebra, the class
map to each value is surjective, two lifts have the same class exactly when they are isomorphic,
and the restriction maps of the presheaf are base change of lifts. -/
structure LiftClassPresheaf where
  /-- The functor `F`. -/
  presheaf : (Over U')ᵒᵖ ⥤ Type (u + 1)
  /-- The restriction `x|_{B' ⊗_{A'} A}` exists for every affine `A'`-algebra `B'`. -/
  nonempty_restriction : ∀ W : Over U', Nonempty (Restriction B S hS 𝒳 i x hx W)
  /-- The isomorphism class of a lift, as an element of `F(B')`. -/
  cls : ∀ {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W),
    InfinitesimalLift B S hS 𝒳 i x hx r → presheaf.obj (op W)
  /-- Every element of `F(B')` is the class of a lift. -/
  cls_surjective : ∀ {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W),
    Function.Surjective (cls r)
  /-- Two lifts have the same class exactly when they are isomorphic. -/
  cls_eq_iff : ∀ {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W)
    (l m : InfinitesimalLift B S hS 𝒳 i x hx r),
    cls r l = cls r m ↔ InfinitesimalLift.Isomorphic B S hS 𝒳 i x hx l m
  /-- The restriction maps of `F` are base change of lifts. -/
  cls_map : ∀ {W₁ W₂ : Over U'} (g : W₂ ⟶ W₁) (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (l : InfinitesimalLift B S hS 𝒳 i x hx r₁)
    (m : InfinitesimalLift B S hS 𝒳 i x hx r₂),
    InfinitesimalLift.IsRestrictionAlong B S hS 𝒳 i x hx g l m →
      presheaf.map g.op (cls r₁ l) = cls r₂ m

end Deformation.Artin.LiftClassSheaf

end
