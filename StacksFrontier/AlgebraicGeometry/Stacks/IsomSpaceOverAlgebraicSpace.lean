module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeIsomorphismDiagram
public import StacksFrontier.CategoryTheory.FiberedCategory.RepresentableFibred

/-!
# The isomorphism sheaf of two algebraic-space-valued points of an algebraic stack

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S` and let
`x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points of `𝒳`. A point `z` of `Z` over an object
`W` of the big fppf site names an object `(W, z)` of the category of elements of `Z`, hence, after
applying `x₁` and `x₂`, two objects of the fibre category of `𝒳` over `W`. The closing paragraph
of **Stacks 06PP** attaches to this datum the sheaf `Isom_𝒳(x₁, x₂)` on the big fppf site of `S`,
the *sheaf of isomorphisms from `x₁` to `x₂`*, whose sections over `W` are the pairs consisting
of a point `z` of `Z` over `W` and an isomorphism between the two objects of the fibre of `𝒳`
over `W` that `z` determines.

This file builds that sheaf as a `Type u`-valued presheaf, together with its structure morphism to
`Z`. The restriction maps are the content: a morphism `g : W' ⟶ W` of the site lifts to a morphism
`(W', z|_{W'}) ⟶ (W, z)` of the category of elements of `Z`, whose images under `x₁` and `x₂` are
strongly cartesian because `𝒳` is fibred in groupoids (Stacks 003V), and the restriction of a
section is the unique vertical morphism making the resulting square commute. Functoriality is
exactly the uniqueness half of that universal property.

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` of the
target, **Stacks 0CPK** part (3) adds the map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(f x₁, f x₂)` given by
applying `f` to an isomorphism, the section `Z ⟶ Isom_𝒴(f x₁, f x₂)` given by the components of
`α`, and the sub-sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` of isomorphisms whose image under `f` is the
prescribed component of `α` — Stacks 06PP part (2) — and asserts that the resulting square is
cartesian. That square is proved to be a pullback of presheaves here.

Nothing about representability is claimed: that these presheaves are algebraic spaces over `Z` is
the other half of Stacks 06PP and is not proved here. The 2-categorical form of the same diagram,
as a cospan of categories fibred in groupoids, is
`AlgebraicGeometry.Stack.exists_relativeIsomorphismDiagram`.

## Main definitions

* `AlgebraicGeometry.Stack.spacePoint` and `AlgebraicGeometry.Stack.pointFiber`: the object of the
  category of elements of `Z` named by a point, and the object of the fibre category of `𝒳` it
  determines through a point of `𝒳`.
* `AlgebraicGeometry.Stack.pointRestrict`: the restriction of an isomorphism of two such objects
  along a morphism of the site.
* `AlgebraicGeometry.Stack.isomSpaceOverSpace`: **Stacks 06PP**, the presheaf
  `Isom_𝒳(x₁, x₂)`, and `AlgebraicGeometry.Stack.isomSpaceOverSpaceProj`, its structure morphism
  to `Z`.
* `AlgebraicGeometry.Stack.isomSpaceOverSpaceMap`: **Stacks 0CPK** part (3), the map on
  isomorphism sheaves induced by a 1-morphism `f : 𝒳 ⟶ 𝒴`.
* `AlgebraicGeometry.Stack.twistedSection`: the section of `Isom_𝒴(f x₁, f x₂)` over `Z` given by
  the components of a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`.
* `AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace`: **Stacks 06PP** part (2), the sub-presheaf
  `Isom^α_{𝒳/𝒴}(x₁, x₂)` of isomorphisms lifting `α`, with its inclusion
  `AlgebraicGeometry.Stack.relativeIsomSpaceOverSpaceι` and projection
  `AlgebraicGeometry.Stack.relativeIsomSpaceOverSpaceProj`.

## Main results

* `AlgebraicGeometry.Stack.pointRestrict_fac` and `AlgebraicGeometry.Stack.pointRestrict_uniq`:
  the universal property that defines the restriction maps.
* `AlgebraicGeometry.Stack.isomSpaceOverSpaceMap_comp_proj` and
  `AlgebraicGeometry.Stack.twistedSection_comp_proj`: both maps are compatible with the structure
  morphisms to `Z`.
* `AlgebraicGeometry.Stack.isPullback_relativeIsomSpaceOverSpace`: **Stacks 0CPK** part (3), the
  square cutting out the isomorphisms lifting `α` is cartesian.

## Implementation notes

The sections of `Isom_𝒳(x₁, x₂)` over `W` are a `Sigma` type: a point `z : Z(W)` together with a
sub-type of the morphisms of the fibre category `𝒳_W`. Because the type of the second component
depends on the first, the restriction map is defined with the target point of `Z` as a separate
argument constrained by an equation (`AlgebraicGeometry.Stack.pointRestrict`), which is what makes
the functoriality proofs go through by `subst` rather than by transport along a heterogeneous
equality: the two sides of `map_id` and `map_comp` are then literally sections over the same
point.

`AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace` is defined as an explicit sub-presheaf rather
than as a limit, so that its sections are the isomorphisms Stacks 06PP part (2) names; that it is
*the* fibre product is then the content of
`AlgebraicGeometry.Stack.isPullback_relativeIsomSpaceOverSpace`.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPK](https://stacks.math.columbia.edu/tag/0CPK)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

-- The fibre categories and their inclusions must unfold for the instance arguments of
-- `IsHomLift` and `IsStronglyCartesian` to be found inside a composite, as for
-- `CategoryTheory.Functor.isomPresheaf`.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Every morphism of a fibre category of an algebraic stack is an isomorphism.** The fibres of
a category fibred in groupoids are groupoids (Stacks 003V). -/
theorem isIso_fiberHom (𝒯 : AlgebraicStacks.{u, w} B S hS) {W : BigFppfOver B S hS}
    {a b : 𝒯.val.val.p.Fiber W} (φ : a ⟶ b) : IsIso φ :=
  let := 𝒯.val.isFiberedInGroupoids.fiber_isGroupoid W
  inferInstance

/-! ### Points of `Z` as objects of the category of elements -/

/-- The object `(W, z)` of the category of elements of `Z`, that is of the algebraic stack
attached to the algebraic space `Z`, named by a point `z` of `Z` over `W`. -/
def spacePoint (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W)) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj :=
  ⟨W, Discrete.mk z⟩

/-- The base of the object named by a point `z` of `Z` over `W` is `W`. -/
@[simp] lemma spacePoint_base (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W)) :
    (spacePoint.{u, w} B S hS Z hZ W z).base = W :=
  rfl

/-- The morphism `(W', z') ⟶ (W, z)` of the category of elements of `Z` lying over a morphism
`g : W' ⟶ W` of the site, for a point `z'` of `Z` over `W'` that restricts `z`. -/
def spacePointHom {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z) :
    spacePoint.{u, w} B S hS Z hZ W₂.unop z' ⟶ spacePoint.{u, w} B S hS Z hZ W₁.unop z where
  base := g.unop
  fiber := Discrete.eqToHom hz

/-- The morphism `(W', z') ⟶ (W, z)` lies over `g`. -/
instance spacePointHom_isHomLift {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁)
    (z' : Z.obj W₂) (hz : z' = Z.map g z) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift g.unop
      (spacePointHom.{u, w} B S hS Z hZ g z z' hz) :=
  IsHomLift.map _ (spacePointHom.{u, w} B S hS Z hZ g z z' hz)

/-- The morphism of the category of elements of `Z` over an identity of the site is the
identity: the fibres of that category are discrete. -/
lemma spacePointHom_id {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W) (hz : z = Z.map (𝟙 W) z) :
    spacePointHom.{u, w} B S hS Z hZ (𝟙 W) z z hz =
      𝟙 (spacePoint.{u, w} B S hS Z hZ W.unop z) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  apply Discrete.hom_eq

/-- The morphisms of the category of elements of `Z` compose. -/
lemma spacePointHom_comp {W₁ W₂ W₃ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃)
    (z : Z.obj W₁) (z' : Z.obj W₂) (hz' : z' = Z.map g z) (z'' : Z.obj W₃)
    (hz'' : z'' = Z.map h z') (hz : z'' = Z.map (g ≫ h) z) :
    spacePointHom.{u, w} B S hS Z hZ h z' z'' hz'' ≫
        spacePointHom.{u, w} B S hS Z hZ g z z' hz' =
      spacePointHom.{u, w} B S hS Z hZ (g ≫ h) z z'' hz := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  apply Discrete.hom_eq

/-! ### The two objects of a fibre category determined by a point -/

/-- The object of the fibre category of `𝒳` over `W` determined by a point `z` of `Z` over `W` and
a point `x : Z ⟶ 𝒳` of `𝒳`: the image of `(W, z)` under `x`, which lies over `W` because `x` is a
1-morphism over the big fppf site. -/
def pointFiber (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (W : BigFppfOver B S hS)
    (z : Z.obj (Opposite.op W)) : 𝒳.val.val.p.Fiber W :=
  ⟨x.hom.hom.toFunctor.obj (spacePoint.{u, w} B S hS Z hZ W z),
    Functor.congr_obj x.hom.hom.w (spacePoint.{u, w} B S hS Z hZ W z)⟩

attribute [local implicit_reducible] pointFiber

/-- The image under `x` of the morphism `(W', z') ⟶ (W, z)` lies over `g`. -/
instance pointFiber_isHomLift (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z) :
    𝒳.val.val.p.IsHomLift g.unop
      (x.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz)) :=
  Functor.isHomLift_map_of_comp_eq x.hom.hom.w g.unop _

/-! ### Restriction of an isomorphism along a morphism of the site -/

/-- The image under `x₂` of the morphism `(W', z') ⟶ (W, z)` is strongly cartesian, because `𝒳` is
fibred in groupoids. -/
private lemma isStronglyCartesian_map_spacePointHom
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ}
    (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z) :
    𝒳.val.val.p.IsStronglyCartesian g.unop
      (x.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz)) :=
  𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

/-- **The restriction of an isomorphism of the two objects determined by a point.** Given
`g : W' ⟶ W` in the site and a point `z'` of `Z` over `W'` restricting `z`, the images of the
morphism `(W', z') ⟶ (W, z)` under `x₁` and `x₂` lie over `g`, and the one under `x₂` is strongly
cartesian because `𝒳` is fibred in groupoids. The restriction of `φ` is the unique vertical
morphism over `W'` whose composite with the image under `x₂` is the image under `x₁` followed
by `φ`. -/
noncomputable def pointRestrict (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    pointFiber B S hS Z hZ x₁ W₂.unop z' ⟶ pointFiber B S hS Z hZ x₂ W₂.unop z' :=
  letI : 𝒳.val.val.p.IsStronglyCartesian g.unop
      (x₂.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz)) :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  ⟨Functor.IsStronglyCartesian.map 𝒳.val.val.p g.unop
      (x₂.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz))
      (Category.id_comp g.unop).symm
      (x₁.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz) ≫
        Functor.Fiber.fiberInclusion.map φ),
    inferInstance⟩

/-- The equation that determines `AlgebraicGeometry.Stack.pointRestrict`. -/
@[reassoc]
lemma pointRestrict_fac (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    Functor.Fiber.fiberInclusion.map (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ) ≫
        x₂.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz) =
      x₁.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz) ≫
        Functor.Fiber.fiberInclusion.map φ :=
  haveI := isStronglyCartesian_map_spacePointHom B S hS Z hZ x₂ g z z' hz
  Functor.IsStronglyCartesian.fac _ _ _ (Category.id_comp g.unop).symm _

/-- `AlgebraicGeometry.Stack.pointRestrict` is the only morphism of the fibre over `W'`
satisfying `AlgebraicGeometry.Stack.pointRestrict_fac`. -/
lemma pointRestrict_uniq (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z)
    (n : pointFiber B S hS Z hZ x₁ W₂.unop z' ⟶ pointFiber B S hS Z hZ x₂ W₂.unop z')
    (hn : Functor.Fiber.fiberInclusion.map n ≫
        x₂.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz) =
      x₁.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g z z' hz) ≫
        Functor.Fiber.fiberInclusion.map φ) :
    n = pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ :=
  haveI := isStronglyCartesian_map_spacePointHom B S hS Z hZ x₂ g z z' hz
  Functor.Fiber.hom_ext
    (Functor.IsStronglyCartesian.map_uniq _ _ _ (Category.id_comp g.unop).symm _ _ hn)

/-- Restricting along an identity of the site leaves an isomorphism unchanged. -/
lemma pointRestrict_id (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W) (hz : z = Z.map (𝟙 W) z)
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointRestrict B S hS Z hZ x₁ x₂ (𝟙 W) z z hz φ = φ :=
  (pointRestrict_uniq B S hS Z hZ x₁ x₂ (𝟙 W) z z hz φ φ (by
    rw [spacePointHom_id]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _)).symm

/-- Restricting along a composite is restricting along the two factors in turn. -/
lemma pointRestrict_comp (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ W₃ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃) (z : Z.obj W₁)
    (z' : Z.obj W₂) (hz' : z' = Z.map g z) (z'' : Z.obj W₃) (hz'' : z'' = Z.map h z')
    (hz : z'' = Z.map (g ≫ h) z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    pointRestrict B S hS Z hZ x₁ x₂ (g ≫ h) z z'' hz φ =
      pointRestrict B S hS Z hZ x₁ x₂ h z' z'' hz''
        (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz' φ) :=
  (pointRestrict_uniq B S hS Z hZ x₁ x₂ (g ≫ h) z z'' hz φ _ (by
    rw [← spacePointHom_comp B S hS Z hZ g h z z' hz' z'' hz'' hz]
    simp only [Functor.map_comp, Category.assoc]
    rw [pointRestrict_fac_assoc B S hS Z hZ x₁ x₂ h z' z'' hz'',
      pointRestrict_fac B S hS Z hZ x₁ x₂ g z z' hz'])).symm

/-! ### The isomorphism presheaf -/

/-- A section of `Isom_𝒳(x₁, x₂)` over `W`: a point of `Z` over `W` together with an isomorphism
between the two objects of the fibre category of `𝒳` over `W` it determines. -/
abbrev isomSection (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (W : (BigFppfOver B S hS)ᵒᵖ) : Type u :=
  Σ z : Z.obj W, {φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶
    pointFiber B S hS Z hZ x₂ W.unop z // IsIso φ}

/-- Two sections of `Isom_𝒳(x₁, x₂)` over the same point of `Z` agree as soon as the underlying
morphisms of the fibre do: being an isomorphism is a proposition. -/
private lemma isomSection_mk_eq (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W)
    {φ ψ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z}
    (hφ : IsIso φ) (hψ : IsIso ψ) (h : φ = ψ) :
    (⟨z, ⟨φ, hφ⟩⟩ : isomSection B S hS Z hZ x₁ x₂ W) = ⟨z, ⟨ψ, hψ⟩⟩ := by
  subst h; rfl

/-- Conversely, an equality of two sections of `Isom_𝒳(x₁, x₂)` over the same point of `Z` gives
an equality of the underlying morphisms of the fibre. -/
private lemma isomSection_val_eq (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W)
    {φ ψ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z}
    {hφ : IsIso φ} {hψ : IsIso ψ}
    (h : (⟨z, ⟨φ, hφ⟩⟩ : isomSection B S hS Z hZ x₁ x₂ W) = ⟨z, ⟨ψ, hψ⟩⟩) : φ = ψ := by
  rw [Sigma.mk.injEq] at h
  exact congrArg Subtype.val (eq_of_heq h.2)

/-- The restriction of a section of `Isom_𝒳(x₁, x₂)` along `g`, with the point of `Z` it lies over
named separately so that the functoriality statements below compare sections over the same
point. -/
noncomputable def isomSectionRestrict (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (s : isomSection B S hS Z hZ x₁ x₂ W₁)
    (z' : Z.obj W₂) (hz : z' = Z.map g s.1) : isomSection B S hS Z hZ x₁ x₂ W₂ :=
  ⟨z', ⟨pointRestrict B S hS Z hZ x₁ x₂ g s.1 z' hz s.2.1, isIso_fiberHom B S hS 𝒳 _⟩⟩

/-- The named point of `AlgebraicGeometry.Stack.isomSectionRestrict` may be taken to be the
restriction of the given one. -/
lemma isomSectionRestrict_self (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (s : isomSection B S hS Z hZ x₁ x₂ W₁)
    (z' : Z.obj W₂) (hz : z' = Z.map g s.1) :
    isomSectionRestrict B S hS Z hZ x₁ x₂ g s z' hz =
      isomSectionRestrict B S hS Z hZ x₁ x₂ g s (Z.map g s.1) rfl := by
  subst hz; rfl

/-- **Stacks 06PP.** The presheaf `Isom_𝒳(x₁, x₂)` of isomorphisms of two
algebraic-space-valued points of an algebraic stack: its sections over `W` are the pairs
consisting of a point `z` of `Z` over `W` and an isomorphism `x₁(z) ≅ x₂(z)` in the fibre category
of `𝒳` over `W`, and its restriction maps are `AlgebraicGeometry.Stack.pointRestrict`.

This is the object the last paragraph of Stacks 06PP calls `Isom_𝒳(x₁, x₂)`, the *sheaf of
isomorphisms from `x₁` to `x₂`*. That it is represented by an algebraic space over `Z` is the
other half of that definition and is not asserted here. Part (1), the group law on the relative
sheaf of automorphisms `Isom_{𝒳/𝒴}(x, x)`, is
`AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace`; for `𝒴` an algebraic space
its underlying presheaf is this one at `x₁ = x₂ = x`, by
`AlgebraicGeometry.Stack.isIso_relativeAutomorphismToIsomSpace`. -/
@[stacks 06PP "the sheaf of isomorphisms from one algebraic-space-valued point to another"]
noncomputable def isomSpaceOverSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj W := isomSection B S hS Z hZ x₁ x₂ W
  map g := ↾fun s => isomSectionRestrict B S hS Z hZ x₁ x₂ g s (Z.map g s.1) rfl
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    rw [types_id_apply]
    refine (isomSectionRestrict_self B S hS Z hZ x₁ x₂ (𝟙 W) s s.1 (by simp)).symm.trans ?_
    obtain ⟨z, φ, hφ⟩ := s
    exact isomSection_mk_eq B S hS Z hZ x₁ x₂ z _ _
      (pointRestrict_id B S hS Z hZ x₁ x₂ z _ φ)
  map_comp {W₁ W₂ W₃} g h := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    rw [ConcreteCategory.comp_apply]
    refine (isomSectionRestrict_self B S hS Z hZ x₁ x₂ (g ≫ h) s
      (Z.map h (Z.map g s.1)) (by simp)).symm.trans ?_
    exact isomSection_mk_eq B S hS Z hZ x₁ x₂ (Z.map h (Z.map g s.1)) _ _
      (pointRestrict_comp B S hS Z hZ x₁ x₂ g h s.1 (Z.map g s.1) rfl _ rfl _ s.2.1)

/-- Restricting a section of `Isom_𝒳(x₁, x₂)` restricts its point of `Z`. -/
@[simp] lemma isomSpaceOverSpace_map_fst (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (s : isomSection B S hS Z hZ x₁ x₂ W₁) :
    ((isomSpaceOverSpace B S hS Z hZ x₁ x₂).map g s).1 = Z.map g s.1 :=
  rfl

/-- The structure morphism of `Isom_𝒳(x₁, x₂)` to `Z`: a section is an isomorphism *over a point
of `Z`*, and this is that point. -/
noncomputable def isomSpaceOverSpaceProj (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    isomSpaceOverSpace B S hS Z hZ x₁ x₂ ⟶ Z where
  app _ := ↾fun s => s.1
  naturality _ _ _ := rfl

/-! ### The map induced by a 1-morphism of algebraic stacks -/

/-- The isomorphism of the two objects of a fibre category of `𝒴` determined by a point, obtained
by applying a 1-morphism `f : 𝒳 ⟶ 𝒴` to an isomorphism in `𝒳`. It is again vertical because `f`
is a 1-morphism over the big fppf site. -/
def pointFiberMap (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W))
    (φ : pointFiber B S hS Z hZ x₁ W z ⟶ pointFiber B S hS Z hZ x₂ W z) :
    pointFiber B S hS Z hZ (x₁ ≫ f) W z ⟶ pointFiber B S hS Z hZ (x₂ ≫ f) W z :=
  ⟨f.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map φ),
    Functor.isHomLift_map_of_comp_eq f.hom.hom.w (𝟙 W) _⟩

/-- Applying `f` commutes with restriction: both sides are determined by the same universal
property, `AlgebraicGeometry.Stack.pointRestrict_uniq` in `𝒴`. -/
lemma pointFiberMap_pointRestrict (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    pointFiberMap B S hS Z hZ f x₁ x₂ W₂.unop z'
        (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ) =
      pointRestrict B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) g z z' hz
        (pointFiberMap B S hS Z hZ f x₁ x₂ W₁.unop z φ) :=
  pointRestrict_uniq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) g z z' hz
    (pointFiberMap B S hS Z hZ f x₁ x₂ W₁.unop z φ)
    (pointFiberMap B S hS Z hZ f x₁ x₂ W₂.unop z'
      (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ)) (by
    change f.hom.hom.toFunctor.map _ ≫ f.hom.hom.toFunctor.map _ =
      f.hom.hom.toFunctor.map _ ≫ f.hom.hom.toFunctor.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      pointRestrict_fac B S hS Z hZ x₁ x₂ g z z' hz])

/-- **Stacks 0CPK, part (3): the map on isomorphism sheaves.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks carries `Isom_𝒳(x₁, x₂)` into `Isom_𝒴(x₁ ≫ f, x₂ ≫ f)`: it keeps the point of `Z`
and applies `f` to the isomorphism of the fibre.

The source calls this a map *of algebraic spaces*; that the source and target are algebraic
spaces over `Z` is asserted by Stacks 06PP and is not proved here, so this is the map of the
underlying sheaves. -/
@[stacks 0CPK "part (3): the map on isomorphism sheaves"]
noncomputable def isomSpaceOverSpaceMap (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    isomSpaceOverSpace B S hS Z hZ x₁ x₂ ⟶
      isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) where
  app W := ↾fun s =>
    ⟨s.1, ⟨pointFiberMap B S hS Z hZ f x₁ x₂ W.unop s.1 s.2.1, isIso_fiberHom B S hS 𝒴 _⟩⟩
  naturality {W₁ W₂} g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact isomSection_mk_eq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) (Z.map g s.1) _ _
      (pointFiberMap_pointRestrict B S hS Z hZ f x₁ x₂ g s.1 _ rfl s.2.1)

/-- The map induced by `f` keeps the point of `Z`. -/
@[simp] lemma isomSpaceOverSpaceMap_app_fst (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {W : (BigFppfOver B S hS)ᵒᵖ}
    (s : isomSection B S hS Z hZ x₁ x₂ W) :
    ((isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂).app W s).1 = s.1 :=
  rfl

/-- The map induced by `f` is a map over `Z`. -/
@[simp] theorem isomSpaceOverSpaceMap_comp_proj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂ ≫
        isomSpaceOverSpaceProj B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) =
      isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ :=
  Functor.presheafHom_ext fun _ _ => rfl

/-! ### The section determined by a 2-morphism of the target -/

/-- The component at `(W, z)` of a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`, read as an isomorphism of the
two objects of the fibre category of `𝒴` over `W` that `z` determines. Every component of a
2-morphism of categories fibred in groupoids is vertical. -/
def twistedComponent (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (α : x₁ ≫ f ⟶ x₂ ≫ f) (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W)) :
    pointFiber B S hS Z hZ (x₁ ≫ f) W z ⟶ pointFiber B S hS Z hZ (x₂ ≫ f) W z :=
  ⟨α.hom.hom.toNatTrans.app (spacePoint.{u, w} B S hS Z hZ W z),
    α.hom.hom.isHomLift' (spacePoint.{u, w} B S hS Z hZ W z)⟩

/-- The components of a 2-morphism are compatible with restriction: that is the naturality square
of `α` at the morphism `(W', z') ⟶ (W, z)` of the category of elements of `Z`. -/
lemma pointRestrict_twistedComponent (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z) :
    pointRestrict B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) g z z' hz
        (twistedComponent B S hS Z hZ f x₁ x₂ α W₁.unop z) =
      twistedComponent B S hS Z hZ f x₁ x₂ α W₂.unop z' :=
  (pointRestrict_uniq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) g z z' hz
    (twistedComponent B S hS Z hZ f x₁ x₂ α W₁.unop z)
    (twistedComponent B S hS Z hZ f x₁ x₂ α W₂.unop z')
    (α.hom.hom.toNatTrans.naturality
      (spacePointHom.{u, w} B S hS Z hZ g z z' hz)).symm).symm

/-- **The section of `Isom_𝒴(x₁ ≫ f, x₂ ≫ f)` determined by a 2-morphism
`α : x₁ ≫ f ⟶ x₂ ≫ f`.** It sends a point `z` of `Z` to the pair of `z` and the component of `α`
at `(W, z)`, so that composing it with the structure morphism to `Z` is the identity. -/
noncomputable def twistedSection (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    Z ⟶ isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) where
  app W := ↾fun z =>
    ⟨z, ⟨twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z, isIso_fiberHom B S hS 𝒴 _⟩⟩
  naturality {W₁ W₂} g := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact isomSection_mk_eq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) (Z.map g z) _ _
      (pointRestrict_twistedComponent B S hS Z hZ f x₁ x₂ α g z _ rfl).symm

/-- The section determined by `α` sends a point `z` of `Z` to a section over `z`. -/
@[simp] lemma twistedSection_app_fst (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W) :
    ((twistedSection B S hS Z hZ f x₁ x₂ α).app W z).1 = z :=
  rfl

/-- The section determined by a 2-morphism is a section of the structure morphism to `Z`. -/
@[simp] theorem twistedSection_comp_proj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    twistedSection B S hS Z hZ f x₁ x₂ α ≫
        isomSpaceOverSpaceProj B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) = 𝟙 Z :=
  Functor.presheafHom_ext fun _ _ => rfl

/-! ### The isomorphisms lifting a 2-morphism -/

/-- A section of `Isom^α_{𝒳/𝒴}(x₁, x₂)` over `W`: an isomorphism of the two objects of the fibre
category of `𝒳` over `W` determined by a point of `Z`, whose image under `f` is the prescribed
component of `α`. -/
abbrev relativeIsomSection (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (α : x₁ ≫ f ⟶ x₂ ≫ f) (W : (BigFppfOver B S hS)ᵒᵖ) : Type u :=
  Σ z : Z.obj W, {φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶
      pointFiber B S hS Z hZ x₂ W.unop z //
    IsIso φ ∧ pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z φ =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z}

/-- Two sections of `Isom^α_{𝒳/𝒴}(x₁, x₂)` over the same point of `Z` agree as soon as the
underlying morphisms of the fibre do. -/
private lemma relativeIsomSection_mk_eq (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W)
    {φ ψ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z}
    (hφ : IsIso φ ∧ pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z φ =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z)
    (hψ : IsIso ψ ∧ pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z ψ =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z)
    (h : φ = ψ) :
    (⟨z, ⟨φ, hφ⟩⟩ : relativeIsomSection B S hS Z hZ f x₁ x₂ α W) = ⟨z, ⟨ψ, hψ⟩⟩ := by
  subst h; rfl

/-- The restriction of a section of `Isom^α_{𝒳/𝒴}(x₁, x₂)`, with the point of `Z` it lies over
named separately. -/
noncomputable def relativeIsomSectionRestrict (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂)
    (s : relativeIsomSection B S hS Z hZ f x₁ x₂ α W₁) (z' : Z.obj W₂) (hz : z' = Z.map g s.1) :
    relativeIsomSection B S hS Z hZ f x₁ x₂ α W₂ :=
  ⟨z', ⟨pointRestrict B S hS Z hZ x₁ x₂ g s.1 z' hz s.2.1, isIso_fiberHom B S hS 𝒳 _, by
    rw [pointFiberMap_pointRestrict B S hS Z hZ f x₁ x₂ g s.1 z' hz, s.2.2.2,
      pointRestrict_twistedComponent B S hS Z hZ f x₁ x₂ α g s.1 z' hz]⟩⟩

/-- The named point of `AlgebraicGeometry.Stack.relativeIsomSectionRestrict` may be taken to be
the restriction of the given one. -/
lemma relativeIsomSectionRestrict_self (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂)
    (s : relativeIsomSection B S hS Z hZ f x₁ x₂ α W₁) (z' : Z.obj W₂) (hz : z' = Z.map g s.1) :
    relativeIsomSectionRestrict B S hS Z hZ f x₁ x₂ α g s z' hz =
      relativeIsomSectionRestrict B S hS Z hZ f x₁ x₂ α g s (Z.map g s.1) rfl := by
  subst hz; rfl

/-- **Stacks 06PP, part (2).** The presheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` of isomorphisms of two
algebraic-space-valued points of `𝒳` lifting a given 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` of the
target: it is the sub-presheaf of `AlgebraicGeometry.Stack.isomSpaceOverSpace` cut out by the
condition that the image of the isomorphism under `f` be the prescribed component of `α`.

That it is represented by an algebraic space over `Z` is the remaining half of Stacks 06PP part
(2) and is not asserted here. -/
@[stacks 06PP "part (2): the sheaf of isomorphisms lifting a 2-morphism"]
noncomputable def relativeIsomSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj W := relativeIsomSection B S hS Z hZ f x₁ x₂ α W
  map g := ↾fun s => relativeIsomSectionRestrict B S hS Z hZ f x₁ x₂ α g s (Z.map g s.1) rfl
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    rw [types_id_apply]
    refine (relativeIsomSectionRestrict_self B S hS Z hZ f x₁ x₂ α (𝟙 W) s s.1
      (by simp)).symm.trans ?_
    obtain ⟨z, φ, hφ⟩ := s
    exact relativeIsomSection_mk_eq B S hS Z hZ f x₁ x₂ α z _ _
      (pointRestrict_id B S hS Z hZ x₁ x₂ z _ φ)
  map_comp {W₁ W₂ W₃} g h := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    rw [ConcreteCategory.comp_apply]
    refine (relativeIsomSectionRestrict_self B S hS Z hZ f x₁ x₂ α (g ≫ h) s
      (Z.map h (Z.map g s.1)) (by simp)).symm.trans ?_
    exact relativeIsomSection_mk_eq B S hS Z hZ f x₁ x₂ α (Z.map h (Z.map g s.1)) _ _
      (pointRestrict_comp B S hS Z hZ x₁ x₂ g h s.1 (Z.map g s.1) rfl _ rfl _ s.2.1)

/-- The inclusion of `Isom^α_{𝒳/𝒴}(x₁, x₂)` into `Isom_𝒳(x₁, x₂)`: it forgets the condition on
the image of the isomorphism under `f`. -/
noncomputable def relativeIsomSpaceOverSpaceι (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂ where
  app _ := ↾fun s => ⟨s.1, ⟨s.2.1, s.2.2.1⟩⟩
  naturality _ _ _ := rfl

/-- The structure morphism of `Isom^α_{𝒳/𝒴}(x₁, x₂)` to `Z`. -/
noncomputable def relativeIsomSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α ⟶ Z where
  app _ := ↾fun s => s.1
  naturality _ _ _ := rfl

/-- A section of `Isom^α_{𝒳/𝒴}(x₁, x₂)` is determined by its image in `Isom_𝒳(x₁, x₂)`. -/
lemma relativeIsomSection_ext (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} (s t : relativeIsomSection B S hS Z hZ f x₁ x₂ α W)
    (h : (relativeIsomSpaceOverSpaceι B S hS Z hZ f x₁ x₂ α).app W s =
      (relativeIsomSpaceOverSpaceι B S hS Z hZ f x₁ x₂ α).app W t) : s = t := by
  obtain ⟨z, φ, hφ⟩ := s
  obtain ⟨z', φ', hφ'⟩ := t
  obtain rfl : z = z' := congrArg Sigma.fst h
  obtain rfl : φ = φ' := isomSection_val_eq B S hS Z hZ x₁ x₂ z h
  rfl

/-- **Stacks 0CPK, part (3): the cartesian square.** The isomorphisms of `x₁` and `x₂` lifting the
2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` are the fibre product of `Isom_𝒳(x₁, x₂)` and `Z` over
`Isom_𝒴(x₁ ≫ f, x₂ ≫ f)`, along the map induced by `f` and the section determined by `α`.

The square is cartesian pointwise and for an elementary reason: a section of `Isom_𝒳(x₁, x₂)` over
`W` together with a point of `Z` over `W` having the same image in `Isom_𝒴(x₁ ≫ f, x₂ ≫ f)` is the
same thing as a section of `Isom_𝒳(x₁, x₂)` whose image under `f` is the component of `α`, because
the two images have the same point of `Z` as their first component.

The square is the one Stacks 0CPK part (3) draws, as a square of sheaves on the big fppf site of
`S`; that its four corners are algebraic spaces is asserted by Stacks 06PP and is not proved
here. Together with `AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace` it also identifies the
explicit sub-presheaf with the fibre product of Stacks 06PP part (2). -/
@[stacks 0CPK "part (3): the cartesian square"]
theorem isPullback_relativeIsomSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsPullback (relativeIsomSpaceOverSpaceι B S hS Z hZ f x₁ x₂ α)
      (relativeIsomSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α)
      (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
      (twistedSection B S hS Z hZ f x₁ x₂ α) := by
  have key : ∀ (c : Limits.PullbackCone (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
      (twistedSection B S hS Z hZ f x₁ x₂ α)) (W : (BigFppfOver B S hS)ᵒᵖ) (t : c.pt.obj W),
      (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂).app W (c.fst.app W t) =
        (twistedSection B S hS Z hZ f x₁ x₂ α).app W (c.snd.app W t) := by
    intro c W t
    have h := congrArg
      (fun (β : c.pt ⟶ isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f)) => β.app W t)
      c.condition
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  have hfst : ∀ (c : Limits.PullbackCone (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
      (twistedSection B S hS Z hZ f x₁ x₂ α)) (W : (BigFppfOver B S hS)ᵒᵖ) (t : c.pt.obj W),
      (c.fst.app W t).1 = c.snd.app W t :=
    fun c W t => congrArg Sigma.fst (key c W t)
  have hcond : ∀ (c : Limits.PullbackCone (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
      (twistedSection B S hS Z hZ f x₁ x₂ α)) (W : (BigFppfOver B S hS)ᵒᵖ) (t : c.pt.obj W),
      pointFiberMap B S hS Z hZ f x₁ x₂ W.unop (c.fst.app W t).1 (c.fst.app W t).2.1 =
        twistedComponent B S hS Z hZ f x₁ x₂ α W.unop (c.fst.app W t).1 := by
    intro c W t
    have h := key c W t
    rw [← hfst c W t] at h
    exact isomSection_val_eq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) (c.fst.app W t).1 h
  refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk ?_ (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c l h₁ _ => ?_))
  · refine Functor.presheafHom_ext fun W s => ?_
    exact isomSection_mk_eq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) s.1 _ _ s.2.2.2
  · exact
      { app := fun W => ↾fun t =>
          ⟨(c.fst.app W t).1, ⟨(c.fst.app W t).2.1, (c.fst.app W t).2.2, hcond c W t⟩⟩
        naturality := fun {W₁ W₂} g => by
          refine ConcreteCategory.hom_ext _ _ fun t => ?_
          rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
          refine relativeIsomSection_ext B S hS Z hZ f x₁ x₂ α _ _ ?_
          exact NatTrans.naturality_apply c.fst g t }
  · exact Functor.presheafHom_ext fun _ _ => rfl
  · exact Functor.presheafHom_ext fun W t => hfst c W t
  · refine Functor.presheafHom_ext fun W t => ?_
    refine relativeIsomSection_ext B S hS Z hZ f x₁ x₂ α _ _ ?_
    exact congrArg
      (fun (β : c.pt ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂) => β.app W t) h₁

end AlgebraicGeometry.Stack

end
