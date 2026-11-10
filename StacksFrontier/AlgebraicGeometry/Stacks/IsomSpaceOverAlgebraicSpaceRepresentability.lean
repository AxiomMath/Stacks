module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom
import all StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpace

/-!
# The sheaves of isomorphisms of Stacks 06PP are algebraic spaces

`StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceOverAlgebraicSpace.lean` constructs, for an
algebraic stack `𝒳`, an algebraic space `Z` and two points `x₁ x₂ : Z ⟶ 𝒳`, the sheaf of
isomorphisms `Isom_𝒳(x₁, x₂)` over `Z` of **Stacks 06PP**, its relative form
`Isom^α_{𝒳/𝒴}(x₁, x₂)` lifting a 2-morphism, and the cartesian square of **Stacks 0CPK** part
(3). This file proves the other half of the definition in Stacks 06PP: both sheaves are algebraic
spaces over `Z`.

## Main results

* `AlgebraicGeometry.Stack.pointHomCongr`: transport of a morphism of the fibre along an equality
  of points of `Z`, with its functoriality and its compatibility with restriction.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace_fibreOfSection`:
  a map of presheaves is representable by algebraic spaces when its fibres over sections are
  algebraic spaces.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpaceOverSpace`: **Stacks 06PP**,
  `Isom_𝒳(x₁, x₂)` is an algebraic space over `Z`.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_relativeIsomSpaceOverSpace`: **Stacks 06PP** part (2),
  `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic space over `Z`.

## Implementation notes

The fibre of `Isom_𝒳(x₁, x₂) ⟶ Z` over a section of `Z` is identified with the sheaf of vertical
morphisms between the two scheme-valued points of `𝒳` that the section determines, which is an
algebraic space by **Stacks 045G**, read through
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff`, because the
diagonal of an algebraic stack is representable by algebraic spaces. A section of that fibre is
an isomorphism over a point of `Z` *equal to* the prescribed one, so the identification runs on
`AlgebraicGeometry.Stack.pointHomCongr`.

Some of the proofs use the extensionality lemmas for sections of the isomorphism presheaves that
are private to the base module; this file reaches them with `import all` rather than restating
them.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPK](https://stacks.math.columbia.edu/tag/0CPK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

-- The fibre categories and their inclusions must unfold for the instance arguments of
-- `IsHomLift` and `IsStronglyCartesian` to be found inside a composite, as in
-- `StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf`.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

attribute [local implicit_reducible] pointFiber

/-! ### The isomorphism presheaf -/

/-- **Two sections of `Isom_𝒳(x₁, x₂)` over the same point of `Z` are equal exactly when the
underlying morphisms of the fibre are.** The two implications are the extensionality lemmas
`isomSection_val_eq` and `isomSection_mk_eq` of the base module; being an isomorphism is a
proposition, so neither witness is seen by the equality. -/
lemma isomSection_mk_eq_iff (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W)
    {φ ψ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z}
    (hφ : IsIso φ) (hψ : IsIso ψ) :
    (⟨z, ⟨φ, hφ⟩⟩ : isomSection B S hS Z hZ x₁ x₂ W) = ⟨z, ⟨ψ, hψ⟩⟩ ↔ φ = ψ :=
  ⟨isomSection_val_eq B S hS Z hZ x₁ x₂ z, isomSection_mk_eq B S hS Z hZ x₁ x₂ z hφ hψ⟩

/-! ### The isomorphisms lifting a 2-morphism -/

/-- **Two sections of `Isom^α_{𝒳/𝒴}(x₁, x₂)` over the same point of `Z` are equal exactly when the
underlying morphisms of the fibre are.** Both the property of being an isomorphism and the
prescription of the image under `f` are propositions, so neither witness is seen by the
equality. -/
lemma relativeIsomSection_mk_eq_iff (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} (z : Z.obj W)
    {φ ψ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z}
    (hφ : IsIso φ ∧ pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z φ =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z)
    (hψ : IsIso ψ ∧ pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z ψ =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z) :
    (⟨z, ⟨φ, hφ⟩⟩ : relativeIsomSection B S hS Z hZ f x₁ x₂ α W) = ⟨z, ⟨ψ, hψ⟩⟩ ↔ φ = ψ := by
  refine ⟨fun h => ?_, relativeIsomSection_mk_eq B S hS Z hZ f x₁ x₂ α z hφ hψ⟩
  rw [Sigma.mk.injEq] at h
  exact congrArg Subtype.val (eq_of_heq h.2)

/-! ### Functoriality of restriction, and transport along an equality of points -/

/-- **The restriction of a composite is the composite of the restrictions.** Both sides satisfy
the universal property `AlgebraicGeometry.Stack.pointRestrict_uniq` of the composite. -/
lemma pointRestrict_comp_hom (x₁ x₂ x₃ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z)
    (ψ : pointFiber B S hS Z hZ x₂ W₁.unop z ⟶ pointFiber B S hS Z hZ x₃ W₁.unop z) :
    pointRestrict B S hS Z hZ x₁ x₃ g z z' hz (φ ≫ ψ) =
      pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ ≫
        pointRestrict B S hS Z hZ x₂ x₃ g z z' hz ψ :=
  (pointRestrict_uniq B S hS Z hZ x₁ x₃ g z z' hz (φ ≫ ψ) _ (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      pointRestrict_fac B S hS Z hZ x₂ x₃ g z z' hz,
      pointRestrict_fac_assoc B S hS Z hZ x₁ x₂ g z z' hz])).symm

/-- **The restriction of an identity is an identity.** -/
lemma pointRestrict_id_hom (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z) :
    pointRestrict B S hS Z hZ x x g z z' hz (𝟙 _) = 𝟙 _ :=
  (pointRestrict_uniq B S hS Z hZ x x g z z' hz (𝟙 _) (𝟙 _) (by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm)).symm

/-- **Applying a 1-morphism to a composite.** -/
lemma pointFiberMap_comp_hom (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ x₃ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W))
    (φ : pointFiber B S hS Z hZ x₁ W z ⟶ pointFiber B S hS Z hZ x₂ W z)
    (ψ : pointFiber B S hS Z hZ x₂ W z ⟶ pointFiber B S hS Z hZ x₃ W z) :
    pointFiberMap B S hS Z hZ f x₁ x₃ W z (φ ≫ ψ) =
      pointFiberMap B S hS Z hZ f x₁ x₂ W z φ ≫ pointFiberMap B S hS Z hZ f x₂ x₃ W z ψ :=
  Functor.Fiber.hom_ext (by
    change f.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map (φ ≫ ψ)) =
      f.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map φ) ≫
        f.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map ψ)
    simp only [CategoryTheory.Functor.map_comp])

/-- **Applying a 1-morphism to an identity.** -/
lemma pointFiberMap_id_hom (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (W : BigFppfOver B S hS) (z : Z.obj (Opposite.op W)) :
    pointFiberMap B S hS Z hZ f x x W z (𝟙 _) = 𝟙 _ :=
  Functor.Fiber.hom_ext (by
    change f.hom.hom.toFunctor.map
      (Functor.Fiber.fiberInclusion.map (𝟙 (pointFiber B S hS Z hZ x W z))) =
        Functor.Fiber.fiberInclusion.map (𝟙 (pointFiber B S hS Z hZ (x ≫ f) W z))
    simp only [CategoryTheory.Functor.map_id]
    rfl)

/-- The component of the identity 2-morphism of `x ≫ f` is the identity: the relative
isomorphisms lifting it are the automorphisms of `x` killed by `f`. -/
@[simp] lemma twistedComponent_id (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (W : BigFppfOver B S hS)
    (z : Z.obj (Opposite.op W)) :
    twistedComponent B S hS Z hZ f x x (𝟙 (x ≫ f)) W z = 𝟙 _ :=
  rfl

/-- **Transport of a morphism of a fibre along an equality of the point of `Z` it lies over.**
The two objects of the fibre category determined by a point depend on that point, so an
isomorphism over one point is read over an equal point through this transport; every lemma about
it below is proved by substituting the equality. -/
def pointHomCongr (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointFiber B S hS Z hZ x₁ W.unop z' ⟶ pointFiber B S hS Z hZ x₂ W.unop z' :=
  h ▸ φ

/-- Transport of a morphism of a fibre along `rfl` is the morphism itself. -/
@[simp] lemma pointHomCongr_rfl (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z : Z.obj W}
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₂ rfl φ = φ :=
  rfl

/-- Transport along a proof of a reflexive equality of points changes nothing. The transport is
`Eq.rec`, which does not reduce on a proof that is not literally `rfl`, so this is recorded. -/
lemma pointHomCongr_eq (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z : Z.obj W} (h : z = z)
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₂ h φ = φ := by
  rw [proof_irrel h rfl]
  rfl

/-- Transport does not depend on the proof of the equality of points. -/
lemma pointHomCongr_congr (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h h' : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₂ h φ = pointHomCongr B S hS Z hZ x₁ x₂ h' φ := by
  rw [proof_irrel h h']

/-- Transporting twice is transporting along the composite equality. -/
lemma pointHomCongr_trans (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' z'' : Z.obj W} (h : z = z') (h' : z' = z'')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₂ h' (pointHomCongr B S hS Z hZ x₁ x₂ h φ) =
      pointHomCongr B S hS Z hZ x₁ x₂ (h.trans h') φ := by
  subst h; subst h'; rfl

/-- Transport carries an identity to an identity. -/
lemma pointHomCongr_id (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z') :
    pointHomCongr B S hS Z hZ x x h (𝟙 _) = 𝟙 _ := by
  subst h; rfl

/-- Transport is compatible with composition. -/
lemma pointHomCongr_comp (x₁ x₂ x₃ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z)
    (ψ : pointFiber B S hS Z hZ x₂ W.unop z ⟶ pointFiber B S hS Z hZ x₃ W.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₃ h (φ ≫ ψ) =
      pointHomCongr B S hS Z hZ x₁ x₂ h φ ≫ pointHomCongr B S hS Z hZ x₂ x₃ h ψ := by
  subst h; rfl

/-- Transport is compatible with applying a 1-morphism of algebraic stacks. -/
lemma pointFiberMap_pointHomCongr (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z' (pointHomCongr B S hS Z hZ x₁ x₂ h φ) =
      pointHomCongr B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) h
        (pointFiberMap B S hS Z hZ f x₁ x₂ W.unop z φ) := by
  subst h; rfl

/-- Transporting and then restricting is restricting. -/
lemma pointRestrict_pointHomCongr (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) {z z' : Z.obj W₁} (h : z = z')
    (z'' : Z.obj W₂) (hz : z'' = Z.map g z') (hz' : z'' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    pointRestrict B S hS Z hZ x₁ x₂ g z' z'' hz (pointHomCongr B S hS Z hZ x₁ x₂ h φ) =
      pointRestrict B S hS Z hZ x₁ x₂ g z z'' hz' φ := by
  subst h; rfl

/-- Transporting the component of a 2-morphism gives its component at the other point. -/
lemma pointHomCongr_twistedComponent (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z') :
    pointHomCongr B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) h
        (twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z) =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop z' := by
  subst h; rfl

/-- Transporting a restriction is restricting to the other point. -/
lemma pointHomCongr_pointRestrict (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) {z' z'' : Z.obj W₂}
    (hz' : z' = Z.map g z) (hz'' : z'' = Z.map g z) (h : z' = z'')
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    pointHomCongr B S hS Z hZ x₁ x₂ h (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz' φ) =
      pointRestrict B S hS Z hZ x₁ x₂ g z z'' hz'' φ := by
  subst h; rfl

/-- **Two sections of `Isom_𝒳(x₁, x₂)` lying over a common point of `Z` are equal as soon as
the isomorphisms they name are, read over that point.** -/
lemma isomSection_eq_of_pointHomCongr (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} (s t : isomSection B S hS Z hZ x₁ x₂ W) (z : Z.obj W)
    (hs : s.1 = z) (ht : t.1 = z)
    (h : pointHomCongr B S hS Z hZ x₁ x₂ hs s.2.1 =
      pointHomCongr B S hS Z hZ x₁ x₂ ht t.2.1) : s = t := by
  obtain ⟨zs, φ, hφ⟩ := s
  obtain ⟨zt, ψ, hψ⟩ := t
  replace hs : zs = z := hs
  replace ht : zt = z := ht
  subst hs
  subst ht
  exact isomSection_mk_eq B S hS Z hZ x₁ x₂ _ hφ hψ h

/-- **The same for the sections of `Isom^α_{𝒳/𝒴}(x₁, x₂)`.** -/
lemma relativeIsomSection_eq_of_pointHomCongr (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W : (BigFppfOver B S hS)ᵒᵖ} (s t : relativeIsomSection B S hS Z hZ f x₁ x₂ α W)
    (z : Z.obj W) (hs : s.1 = z) (ht : t.1 = z)
    (h : pointHomCongr B S hS Z hZ x₁ x₂ hs s.2.1 =
      pointHomCongr B S hS Z hZ x₁ x₂ ht t.2.1) : s = t := by
  obtain ⟨zs, φ, hφ⟩ := s
  obtain ⟨zt, ψ, hψ⟩ := t
  replace hs : zs = z := hs
  replace ht : zt = z := ht
  subst hs
  subst ht
  exact relativeIsomSection_mk_eq B S hS Z hZ f x₁ x₂ α _ hφ hψ h

/-- Every restriction of an isomorphism of a fibre is an isomorphism. -/
instance isIso_pointRestrict (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z) :
    IsIso (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ) :=
  isIso_fiberHom B S hS 𝒳 _

/-- Every image under a 1-morphism of an isomorphism of a fibre is an isomorphism. -/
instance isIso_pointFiberMap (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (W : BigFppfOver B S hS)
    (z : Z.obj (Opposite.op W))
    (φ : pointFiber B S hS Z hZ x₁ W z ⟶ pointFiber B S hS Z hZ x₂ W z) :
    IsIso (pointFiberMap B S hS Z hZ f x₁ x₂ W z φ) :=
  isIso_fiberHom B S hS 𝒴 _

/-- Every transport of an isomorphism of a fibre is an isomorphism. -/
instance isIso_pointHomCongr (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z) :
    IsIso (pointHomCongr B S hS Z hZ x₁ x₂ h φ) :=
  isIso_fiberHom B S hS 𝒳 _

/-- **The restriction of an inverse is the inverse of the restriction.** -/
lemma pointRestrict_inv (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (z : Z.obj W₁) (z' : Z.obj W₂)
    (hz : z' = Z.map g z)
    (φ : pointFiber B S hS Z hZ x₁ W₁.unop z ⟶ pointFiber B S hS Z hZ x₂ W₁.unop z)
    [IsIso φ] :
    pointRestrict B S hS Z hZ x₂ x₁ g z z' hz (CategoryTheory.inv φ) =
      CategoryTheory.inv (pointRestrict B S hS Z hZ x₁ x₂ g z z' hz φ) := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  rw [← pointRestrict_comp_hom B S hS Z hZ x₁ x₂ x₁ g z z' hz φ (CategoryTheory.inv φ),
    IsIso.hom_inv_id, pointRestrict_id_hom]

/-- **Applying a 1-morphism to an inverse gives the inverse.** -/
lemma pointFiberMap_inv (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (W : BigFppfOver B S hS)
    (z : Z.obj (Opposite.op W))
    (φ : pointFiber B S hS Z hZ x₁ W z ⟶ pointFiber B S hS Z hZ x₂ W z) [IsIso φ] :
    pointFiberMap B S hS Z hZ f x₂ x₁ W z (CategoryTheory.inv φ) =
      CategoryTheory.inv (pointFiberMap B S hS Z hZ f x₁ x₂ W z φ) := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  rw [← pointFiberMap_comp_hom B S hS Z hZ f x₁ x₂ x₁ W z φ (CategoryTheory.inv φ),
    IsIso.hom_inv_id, pointFiberMap_id_hom]

/-- Transport is compatible with inverses. -/
lemma pointHomCongr_inv (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W : (BigFppfOver B S hS)ᵒᵖ} {z z' : Z.obj W} (h : z = z')
    (φ : pointFiber B S hS Z hZ x₁ W.unop z ⟶ pointFiber B S hS Z hZ x₂ W.unop z)
    [IsIso φ] :
    pointHomCongr B S hS Z hZ x₂ x₁ h (CategoryTheory.inv φ) =
      CategoryTheory.inv (pointHomCongr B S hS Z hZ x₁ x₂ h φ) := by
  subst h
  rfl

/-- Restricting a section of `Isom_𝒳(x₁, x₂)` and then reading it over a prescribed point is
reading it over a prescribed point and then restricting. -/
lemma pointRestrict_pointHomCongr_section
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂)
    (s : isomSection B S hS Z hZ x₁ x₂ W₁) (s' : isomSection B S hS Z hZ x₁ x₂ W₂)
    (hnat : s' = (isomSpaceOverSpace B S hS Z hZ x₁ x₂).map g s)
    (z₁ : Z.obj W₁) (z₂ : Z.obj W₂) (hs : s.1 = z₁) (hs' : s'.1 = z₂)
    (hz : z₂ = Z.map g z₁) :
    pointRestrict B S hS Z hZ x₁ x₂ g z₁ z₂ hz
        (pointHomCongr B S hS Z hZ x₁ x₂ hs s.2.1) =
      pointHomCongr B S hS Z hZ x₁ x₂ hs' s'.2.1 := by
  subst hnat
  obtain ⟨z, φ, hφ⟩ := s
  replace hs : z = z₁ := hs
  subst hs
  replace hs' : Z.map g z = z₂ := hs'
  subst hs'
  rfl

/-- The same for the sections of `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
lemma pointRestrict_pointHomCongr_relativeIsomSection (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂)
    (s : relativeIsomSection B S hS Z hZ f x₁ x₂ α W₁)
    (s' : relativeIsomSection B S hS Z hZ f x₁ x₂ α W₂)
    (hnat : s' = (relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α).map g s)
    (z₁ : Z.obj W₁) (z₂ : Z.obj W₂) (hs : s.1 = z₁) (hs' : s'.1 = z₂)
    (hz : z₂ = Z.map g z₁) :
    pointRestrict B S hS Z hZ x₁ x₂ g z₁ z₂ hz
        (pointHomCongr B S hS Z hZ x₁ x₂ hs s.2.1) =
      pointHomCongr B S hS Z hZ x₁ x₂ hs' s'.2.1 := by
  subst hnat
  obtain ⟨z, φ, hφ⟩ := s
  replace hs : z = z₁ := hs
  subst hs
  replace hs' : Z.map g z = z₂ := hs'
  subst hs'
  rfl

/-! ### Representability of a map of presheaves, tested on the fibres over sections -/

/-- **A map of presheaves whose fibre over every scheme-valued point of its target is an
algebraic space over that scheme is representable by algebraic spaces.** The base change of the
map along the section is the lower-shriek extension of that fibre
(`CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap`), and the extension of an
algebraic space over `U` is an algebraic space over `S` by Stacks 03I5 (2).

This is the converse of `AlgebraicGeometry.Space.isAlgebraicSpace_fibreOfSection`, and the test
it offers is the one Stacks 02YQ is applied through below: a fibre over a section lives on the
site of `U`, where a representable-diagonal hypothesis on a stack can be used. -/
theorem isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace_fibreOfSection
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (h : ∀ (U : BigFppfOver B S hS) (β : yoneda.obj (Over.mk U.hom) ⟶ G),
      IsAlgebraicSpace B U.left.1 U.left.2 (OverShriek.fibreOfSection U.hom a β)) :
    Space.IsRepresentableByAlgebraicSpaces B S hS a := fun U ξ =>
  Space.isAlgebraicSpace_of_iso B S hS
    (OverShriek.isPullback_relocalizeFibreOfSectionMap U.hom a ξ).flip.isoPullback
    (Space.isAlgebraicSpace_relocalizePresheaf B S hS U _ (h U ξ))

/-! ### The isomorphism sheaves are algebraic spaces over `Z` -/

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

section Representability

variable (U : BigFppfOver B S hS) (β : yoneda.obj (Over.mk U.hom) ⟶ Z)

/-- The point of `Z` over an object `τ` of the big fppf site of `U` named by a section `β` of `Z`
over `U`: the restriction of `β` along the tautological morphism of `τ`. -/
abbrev slicePointElt (τ : BigFppfOver B U.left.1 U.left.2) :
    Z.obj (Opposite.op ((Over.map U.hom).obj τ)) :=
  β.app (Opposite.op ((Over.map U.hom).obj τ)) (OverShriek.overMapTautHom U.hom τ)

/-- **The scheme-valued point of `𝒳` over the big fppf site of `U` determined by a section of
`Z` over `U`**: evaluate the algebraic-space-valued point `x` of `𝒳` on the point of `Z` that
the section names. -/
abbrev slicePointFunctor (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj :=
  pointOfSchemePoint B S hS U β ⋙ x.hom.hom.toFunctor

/-- `AlgebraicGeometry.Stack.slicePointFunctor` is a scheme-valued point: it lies over
`CategoryTheory.Over.map U.hom`. -/
lemma slicePointFunctor_comp_eq (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    slicePointFunctor.{u, w} B S hS Z hZ U β x ⋙ 𝒳.val.val.p = Over.map U.hom :=
  (Functor.assoc (pointOfSchemePoint B S hS U β) x.hom.hom.toFunctor 𝒳.val.val.p).trans
    ((congrArg (fun K => pointOfSchemePoint B S hS U β ⋙ K) x.hom.hom.w).trans
      (pointOfSchemePoint_comp_eq B S hS U β))

/-- The morphism of the category of elements of `Z` that
`AlgebraicGeometry.Stack.pointOfSchemePoint` assigns to a morphism of the site of `U` is the one
`AlgebraicGeometry.Stack.spacePointHom` names: a morphism of a category of elements is
determined by the morphism of the base it lies over. -/
lemma pointOfSchemePoint_map_eq {τ₁ τ₂ : BigFppfOver B U.left.1 U.left.2} (h : τ₁ ⟶ τ₂)
    (hz : slicePointElt B S hS Z U β τ₁ =
      Z.map ((Over.map U.hom).map h).op (slicePointElt B S hS Z U β τ₂)) :
    (pointOfSchemePoint B S hS U β).map h =
      spacePointHom.{u, w} B S hS Z hZ ((Over.map U.hom).map h).op
        (slicePointElt B S hS Z U β τ₂) (slicePointElt B S hS Z U β τ₁) hz :=
  PresheafOfCategories.elements_hom_ext _ _ rfl

/-- **The restriction maps of the sheaf of vertical morphisms are the restriction maps of the
isomorphism sheaf.** Both are defined by the universal property of the image under `x₂` of the
same cartesian morphism of the category of elements of `Z`. -/
lemma vertHomRestrict_eq_pointRestrict
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {τ₁ τ₂ : BigFppfOver B U.left.1 U.left.2} (h : τ₁ ⟶ τ₂)
    (hz : slicePointElt B S hS Z U β τ₁ =
      Z.map ((Over.map U.hom).map h).op (slicePointElt B S hS Z U β τ₂))
    (φ : pointFiber B S hS Z hZ x₁ ((Over.map U.hom).obj τ₂)
        (slicePointElt B S hS Z U β τ₂) ⟶
      pointFiber B S hS Z hZ x₂ ((Over.map U.hom).obj τ₂)
        (slicePointElt B S hS Z U β τ₂)) :
    VertHom.restrict 𝒳.val.isFiberedInGroupoids
        (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
        (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂) h φ =
      pointRestrict B S hS Z hZ x₁ x₂ ((Over.map U.hom).map h).op
        (slicePointElt B S hS Z U β τ₂) (slicePointElt B S hS Z U β τ₁) hz φ :=
  (VertHom.restrict_uniq 𝒳.val.isFiberedInGroupoids
    (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
    (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂) h φ _ (by
      have key := pointRestrict_fac B S hS Z hZ x₁ x₂ ((Over.map U.hom).map h).op
        (slicePointElt B S hS Z U β τ₂) (slicePointElt B S hS Z U β τ₁) hz φ
      rw [← pointOfSchemePoint_map_eq B S hS Z hZ U β h hz] at key
      exact key)).symm

/-- **The fibre of the structure morphism of `Isom_𝒳(x₁, x₂)` over a section of `Z` is the sheaf
of vertical morphisms between the two scheme-valued points of `𝒳` the section determines.** A
section of the fibre is an isomorphism over a point of `Z` *equal to* the prescribed one, so the
comparison is `AlgebraicGeometry.Stack.pointHomCongr`, and its compatibility with restriction is
`AlgebraicGeometry.Stack.pointRestrict_pointHomCongr_section` together with
`AlgebraicGeometry.Stack.vertHomRestrict_eq_pointRestrict`. -/
noncomputable def fibreOfSectionIsoVertHomPresheaf
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    OverShriek.fibreOfSection U.hom (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) β ≅
      vertHomPresheaf 𝒳.val.isFiberedInGroupoids
        (pairFunctor_comp (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
          (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂)) :=
  NatIso.ofComponents
    (fun τ =>
      (Equiv.mk (fun s => pointHomCongr B S hS Z hZ x₁ x₂ s.2 s.1.2.1)
        (fun φ => ⟨⟨slicePointElt B S hS Z U β τ.unop,
            ⟨φ, isIso_fiberHom B S hS 𝒳 _⟩⟩, rfl⟩)
        (fun s => Subtype.ext (isomSection_eq_of_pointHomCongr B S hS Z hZ x₁ x₂ _ _ _ rfl s.2
          (pointHomCongr_eq B S hS Z hZ x₁ x₂ _ _)))
        (fun φ => pointHomCongr_eq B S hS Z hZ x₁ x₂ _ _)).toIso)
    (fun {τ₁ τ₂} g => by
      refine ConcreteCategory.hom_ext _ _ fun s => ?_
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      refine ((vertHomRestrict_eq_pointRestrict B S hS Z hZ U β x₁ x₂ g.unop
        (PresheafOfCategories.app_overMapTautHom_map U.hom β g.unop).symm _).trans ?_).symm
      exact pointRestrict_pointHomCongr_section B S hS Z hZ x₁ x₂
        ((Over.map U.hom).map g.unop).op s.1 _ rfl _ _ s.2
        ((OverShriek.fibreOfSection U.hom
          (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) β).map g s).2 _)

/-- **The fibre of the structure morphism of `Isom_𝒳(x₁, x₂)` over a section of `Z` is an
algebraic space over `U`.** It is the sheaf of vertical morphisms between two scheme-valued
points of `𝒳` over `U`, whose algebraicity is condition (2) of Stacks 045G read through
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff`, and the
diagonal of an algebraic stack is representable by algebraic spaces, which is its condition
(1). -/
theorem isAlgebraicSpace_fibreOfSection_isomSpaceOverSpaceProj
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B U.left.1 U.left.2
      (OverShriek.fibreOfSection U.hom (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) β) := by
  obtain ⟨F, hF, hE⟩ :=
    SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property U
      (pairFunctor (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
        (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂))
      (pairFunctor_comp (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
        (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂))
  obtain ⟨i⟩ := (nonempty_equivalenceOver_fst_iff 𝒳.val.isFiberedInGroupoids
    (pairFunctor_comp (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₁)
      (slicePointFunctor_comp_eq.{u, w} B S hS Z hZ U β x₂)) F).1 hE
  refine Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (fibreOfSectionIsoVertHomPresheaf B S hS Z hZ U β x₁ x₂).symm ?_
  refine AlgebraicGeometry.isAlgebraicSpace_of_iso B U.left.1 U.left.2 ?_ hF
  let eF : F ⋙ uliftFunctor.{u, u} ≅ F :=
    Functor.isoWhiskerLeft F uliftFunctorTrivial ≪≫ Functor.rightUnitor F
  exact (Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫
    Functor.rightUnitor _).symm ≪≫ i ≪≫ eF

end Representability

/-- **Stacks 06PP: the sheaf of isomorphisms of two algebraic-space-valued points of an
algebraic stack is an algebraic space over `Z`.** The structure morphism
`AlgebraicGeometry.Stack.isomSpaceOverSpaceProj` to `Z` is representable by algebraic spaces,
because its fibre over every scheme-valued point of `Z` is the sheaf of vertical morphisms
between two scheme-valued points of `𝒳`, an algebraic space by condition (2) of Stacks 045G;
`Z` is an algebraic space, so Stacks 02YS applies.

This is the representability half of Stacks 06PP, which
`AlgebraicGeometry.Stack.isomSpaceOverSpace` constructs the sheaf of. -/
@[stacks 06PP "the sheaf of isomorphisms is an algebraic space over Z"]
theorem isAlgebraicSpace_isomSpaceOverSpace
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂) :=
  isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces B S hS
    (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂)
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace_fibreOfSection B S hS _
      fun U β => isAlgebraicSpace_fibreOfSection_isomSpaceOverSpaceProj.{u, w}
        B S hS Z hZ U β x₁ x₂)
    hZ

/-- **Stacks 06PP part (2): the sheaf of isomorphisms lifting a 2-morphism is an algebraic space
over `Z`.** It is the fibre product of `Isom_𝒳(x₁, x₂)` and `Z` over `Isom_𝒴(f x₁, f x₂)` by
`AlgebraicGeometry.Stack.isPullback_relativeIsomSpaceOverSpace`, and all three of those are
algebraic spaces over `S`, so Stacks 04T9 applies. -/
@[stacks 06PP "part (2): the sheaf of isomorphisms lifting a 2-morphism is an algebraic space"]
theorem isAlgebraicSpace_relativeIsomSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α) :=
  isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂) hZ
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f)).isSheaf
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ
      (x₁ ≫ f) (x₂ ≫ f)).diagonal_representable
    (isPullback_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α)

end AlgebraicGeometry.Stack

end
