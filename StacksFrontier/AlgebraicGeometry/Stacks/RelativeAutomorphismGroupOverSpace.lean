module

public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismSpaceOverAlgebraicSpace
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.VertHomPresheafGlue

/-!
# The group of relative automorphisms of an algebraic-space-valued point

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S` and let `x : Z ⟶ 𝒳` be an algebraic-space-valued point of `𝒳`. For a point `a` of `Z` — an
object of the category of elements of `Z` — a *relative automorphism of `x` at `a`* is a vertical
automorphism of the object `x(a)` of `𝒳` which `f` kills. This file builds those into a presheaf
of groups on the category of elements of `Z`:

* at each point of `Z` the relative automorphisms form a group under composition of
  automorphisms, the inverse being the inverse automorphism, which exists because a vertical
  morphism of a category fibred in groupoids is invertible;
* along a morphism `h : a' ⟶ a` of the category of elements of `Z` a relative automorphism
  restricts to the unique vertical automorphism of `x(a')` whose composite with `x(h)` is `x(h)`
  followed by the given one, and that restriction is a group homomorphism.

This is the group law on `Isom_{𝒳/𝒴}(x, x)` over `Z`, read through the functor of points over
`Z`: a group object in algebraic spaces over `Z` is the same datum as a presheaf of groups on the
category of elements of `Z` whose underlying presheaf of sets is an algebraic space over `Z`.

## Main definitions

* `AlgebraicGeometry.Stack.RelativeAutomorphism`: the relative automorphisms of `x` at a point of
  `Z`, with their group structure `AlgebraicGeometry.Stack.RelativeAutomorphism.instGroup`.
* `AlgebraicGeometry.Stack.RelativeAutomorphism.restrict`: their restriction along a morphism of
  the category of elements of `Z`.
* `AlgebraicGeometry.Stack.relativeAutomorphismGroupPresheaf`: the resulting presheaf of groups,
  and `AlgebraicGeometry.Stack.relativeAutomorphismPresheaf` its underlying presheaf of sets.
* `AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj`: that same group law as a
  *group object* of the cartesian monoidal category of presheaves of sets on the category of
  elements of `Z`, with
  `AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj_mul`, `…_one` and `…_inv`
  identifying its multiplication, unit and inverse with composition, the identity automorphism
  and the inverse automorphism.

## Main results

* `AlgebraicGeometry.Stack.RelativeAutomorphism.map_restrict_eq_id`: the restriction of a
  relative automorphism is again killed by `f`.
* `AlgebraicGeometry.Stack.RelativeAutomorphism.restrict_mul` and
  `AlgebraicGeometry.Stack.RelativeAutomorphism.restrict_one`: restriction is a group
  homomorphism.
* `AlgebraicGeometry.Stack.isHomLift_of_map_eq_id`: a morphism of `𝒳` killed by `f` is vertical.

## References

* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.RelativeInertia.basedCategory CategoryTheory.RelativeInertia.basedProjection
  CategoryTheory.RelativeInertia.π

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
variable (f : 𝒳 ⟶ 𝒴) (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-- A *relative automorphism of `x` at a point `a` of `Z`*: a vertical automorphism of the
object `x(a)` of `𝒳` which is killed by `f`. -/
def RelativeAutomorphism
    (a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj) : Type u :=
  {φ : VertHom 𝒳.val.val.p (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      x.hom.hom.toFunctor x.hom.hom.toFunctor a //
    f.hom.hom.toFunctor.map φ.1 = 𝟙 _}

namespace RelativeAutomorphism

variable {B S hS Z hZ f x}

/-- Two relative automorphisms are equal when their underlying morphisms of `𝒳` are. -/
@[ext] lemma ext {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    {φ ψ : RelativeAutomorphism B S hS Z hZ f x a} (h : φ.1.1 = ψ.1.1) : φ = ψ :=
  Subtype.ext (Subtype.ext h)

variable (B S hS Z hZ f x)

/-- The identity automorphism is vertical. -/
lemma isHomLift_id (a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj) :
    𝒳.val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a))
      (𝟙 (x.hom.hom.toFunctor.obj a)) := by
  have h : 𝒳.val.val.p.obj (x.hom.hom.toFunctor.obj a) =
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a :=
    Functor.congr_obj x.hom.hom.w a
  rw [← h]
  infer_instance

/-- The relative automorphisms of `x` at a point of `Z` form a group under composition:
`φ * ψ` is `φ ∘ ψ`, that is `ψ` followed by `φ`. -/
noncomputable instance instGroup
    (a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj) :
    Group (RelativeAutomorphism B S hS Z hZ f x a) where
  one := ⟨⟨𝟙 _, isHomLift_id B S hS Z hZ x a⟩,
    CategoryTheory.Functor.map_id f.hom.hom.toFunctor _⟩
  mul φ ψ :=
    ⟨⟨ψ.1.1 ≫ φ.1.1, by
      have h1 := ψ.1.2
      have h2 := φ.1.2
      exact IsHomLift.comp_of_lift_id _ _ _ _⟩, by
      rw [CategoryTheory.Functor.map_comp, ψ.2, φ.2, Category.comp_id]⟩
  inv φ :=
    ⟨VertHom.symmVal 𝒳.val.isFiberedInGroupoids φ.1, by
      have hiso := VertHom.isIso_val 𝒳.val.isFiberedInGroupoids φ.1
      change f.hom.hom.toFunctor.map (CategoryTheory.inv φ.1.1) = _
      have h : f.hom.hom.toFunctor.map φ.1.1 ≫
          f.hom.hom.toFunctor.map (CategoryTheory.inv φ.1.1) = 𝟙 _ := by
        rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
          CategoryTheory.Functor.map_id]
      rwa [φ.2, Category.id_comp] at h⟩
  mul_assoc φ ψ χ := RelativeAutomorphism.ext (Category.assoc _ _ _).symm
  one_mul φ := RelativeAutomorphism.ext (Category.comp_id _)
  mul_one φ := RelativeAutomorphism.ext (Category.id_comp _)
  inv_mul_cancel φ := by
    have := VertHom.isIso_val 𝒳.val.isFiberedInGroupoids φ.1
    exact RelativeAutomorphism.ext (IsIso.hom_inv_id _)

/-- The underlying morphism of the unit relative automorphism is the identity. -/
@[simp] lemma one_val (a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj) :
    (1 : RelativeAutomorphism B S hS Z hZ f x a).1.1 = 𝟙 _ := rfl

/-- The underlying morphism of `φ * ψ` is `ψ` followed by `φ`. -/
@[simp] lemma mul_val {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ ψ : RelativeAutomorphism B S hS Z hZ f x a) : (φ * ψ).1.1 = ψ.1.1 ≫ φ.1.1 := rfl

/-- The composite `x ≫ f` lies over the category of elements of `Z`. -/
lemma comp_w :
    (x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) ⋙ 𝒴.val.val.p =
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p := by
  rw [Functor.assoc, f.hom.hom.w, x.hom.hom.w]

/-- The image under `f` of a restricted relative automorphism is the identity. -/
lemma map_restrict_eq_id
    {a' a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} (h : a' ⟶ a)
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    f.hom.hom.toFunctor.map
        (VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1).1 =
      𝟙 _ := by
  have hXF := comp_w B S hS Z hZ f x
  have hlift := VertHom.isHomLift_map (p := 𝒴.val.val.p)
    (Y₂ := x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) hXF h
  have _hsc : 𝒴.val.val.p.IsStronglyCartesian
      ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.map h)
      ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h) :=
    𝒴.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have hvert : 𝒴.val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a'))
      (f.hom.hom.toFunctor.map
        (VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1).1) := by
    have := (VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1).2
    exact Functor.isHomLift_map_of_comp_eq f.hom.hom.w _ _
  have hvert' : 𝒴.val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a'))
      (𝟙 ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).obj a')) := by
    have hobj : 𝒴.val.val.p.obj ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).obj a') =
        (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a' :=
      Functor.congr_obj hXF a'
    rw [← hobj]
    infer_instance
  have hfac := VertHom.restrict_fac 𝒳.val.isFiberedInGroupoids
    (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w h φ.1
  have e1 : f.hom.hom.toFunctor.map
      (VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1).1 ≫
        (x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h =
      (x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h := by
    change _ ≫ f.hom.hom.toFunctor.map (x.hom.hom.toFunctor.map h) = _
    rw [← CategoryTheory.Functor.map_comp, hfac, CategoryTheory.Functor.map_comp, φ.2,
      Category.comp_id]
    rfl
  have u1 := Functor.IsStronglyCartesian.map_uniq 𝒴.val.val.p
    ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.map h)
    ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h) (Category.id_comp _).symm
    ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h) _ e1
  exact u1.trans (Functor.IsStronglyCartesian.map_uniq 𝒴.val.val.p
    ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.map h)
    ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h) (Category.id_comp _).symm
    ((x.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor).map h) _ (Category.id_comp _)).symm

/-- **Restriction of a relative automorphism along a morphism of the category of elements of
`Z`**: the unique vertical automorphism of `x(a')` whose composite with `x(h)` is `x(h)`
followed by the given one. -/
noncomputable def restrict
    {a' a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} (h : a' ⟶ a)
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    RelativeAutomorphism B S hS Z hZ f x a' :=
  ⟨VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1,
    map_restrict_eq_id B S hS Z hZ f x h φ⟩

/-- The underlying vertical morphism of a restricted relative automorphism is the restriction
of the underlying vertical morphism. -/
@[simp] lemma restrict_val
    {a' a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} (h : a' ⟶ a)
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    (restrict B S hS Z hZ f x h φ).1 =
      VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1 := rfl

/-- Restriction is multiplicative: it preserves composition of relative automorphisms. -/
lemma restrict_mul {a' a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} (h : a' ⟶ a)
    (φ ψ : RelativeAutomorphism B S hS Z hZ f x a) :
    restrict B S hS Z hZ f x h (φ * ψ) =
      restrict B S hS Z hZ f x h φ * restrict B S hS Z hZ f x h ψ := by
  refine (RelativeAutomorphism.ext ?_).symm
  have hφ := VertHom.restrict_fac 𝒳.val.isFiberedInGroupoids
    (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w h φ.1
  have hψ := VertHom.restrict_fac 𝒳.val.isFiberedInGroupoids
    (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w h ψ.1
  exact congrArg Subtype.val (VertHom.restrict_uniq 𝒳.val.isFiberedInGroupoids
    (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w h
    (φ * ψ).1 ((restrict B S hS Z hZ f x h φ * restrict B S hS Z hZ f x h ψ).1) (by
      change ((VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h ψ.1).1 ≫
        (VertHom.restrict 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w h φ.1).1) ≫ _ = _
      rw [Category.assoc, hφ, ← Category.assoc, hψ, Category.assoc]
      rfl))

/-- Restriction preserves the identity automorphism. -/
lemma restrict_one {a' a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} (h : a' ⟶ a) :
    restrict B S hS Z hZ f x h 1 = 1 :=
  (RelativeAutomorphism.ext (congrArg Subtype.val (VertHom.restrict_uniq
    𝒳.val.isFiberedInGroupoids (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor)
    x.hom.hom.w x.hom.hom.w h (1 : RelativeAutomorphism B S hS Z hZ f x a).1
    (1 : RelativeAutomorphism B S hS Z hZ f x a').1
    ((Category.id_comp _).trans (Category.comp_id _).symm)))).symm

end RelativeAutomorphism

/-- The presheaf of groups on the category of elements of `Z` whose sections at a point `a` of
`Z` are the vertical automorphisms of `x(a)` killed by `f`, with composition as the group law and
restriction along a morphism of `Z` as the restriction map. -/
@[stacks 06PP "part (1): the group law on Isom_{X/Y}(x, x), as a presheaf of groups over Z"]
noncomputable def relativeAutomorphismGroupPresheaf :
    ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ ⥤ GrpCat.{u} where
  obj a := GrpCat.of (RelativeAutomorphism B S hS Z hZ f x a.unop)
  map h := GrpCat.ofHom (MonoidHom.mk'
    (fun φ => RelativeAutomorphism.restrict B S hS Z hZ f x h.unop φ)
    (fun φ ψ => RelativeAutomorphism.restrict_mul B S hS Z hZ f x h.unop φ ψ))
  map_id _ := GrpCat.hom_ext <| MonoidHom.ext fun φ =>
    Subtype.ext (VertHom.restrict_id 𝒳.val.isFiberedInGroupoids
      (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w φ.1)
  map_comp g h := GrpCat.hom_ext <| MonoidHom.ext fun φ =>
    Subtype.ext (VertHom.restrict_comp 𝒳.val.isFiberedInGroupoids
      (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w x.hom.hom.w
      h.unop g.unop φ.1)

/-- The underlying presheaf of sets of
`AlgebraicGeometry.Stack.relativeAutomorphismGroupPresheaf`. -/
noncomputable abbrev relativeAutomorphismPresheaf :
    ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ ⥤ Type u :=
  relativeAutomorphismGroupPresheaf B S hS Z hZ f x ⋙ forget GrpCat

/-- The restriction map of `AlgebraicGeometry.Stack.relativeAutomorphismPresheaf` along `h` is
`AlgebraicGeometry.Stack.RelativeAutomorphism.restrict` along `h.unop`. -/
@[simp] lemma relativeAutomorphismPresheaf_map
    {a a' : ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ} (h : a ⟶ a')
    (φ : RelativeAutomorphism B S hS Z hZ f x a.unop) :
    (relativeAutomorphismPresheaf B S hS Z hZ f x).map h φ =
      RelativeAutomorphism.restrict B S hS Z hZ f x h.unop φ := rfl

/-- A morphism of `𝒳` killed by `f` is vertical. -/
lemma isHomLift_of_map_eq_id {a : 𝒳.val.val.obj} (φ : a ⟶ a)
    (hφ : f.hom.hom.toFunctor.map φ = 𝟙 (f.hom.hom.toFunctor.obj a)) :
    𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj a)) φ := by
  refine IsHomLift.of_fac' 𝒳.val.val.p _ _ rfl rfl ?_
  have h := Functor.congr_hom f.hom.hom.w φ
  rw [Functor.comp_map, hφ, CategoryTheory.Functor.map_id] at h
  simp only [eqToHom_refl, Category.comp_id]
  have key : eqToHom (Functor.congr_obj f.hom.hom.w a) ≫ 𝒳.val.val.p.map φ ≫
      eqToHom (Functor.congr_obj f.hom.hom.w a).symm = 𝟙 _ := h.symm
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
  simpa using key

/-- The presheaf of relative automorphisms of `x`, read over the category of elements of `Z`, is a
*group object* of the cartesian monoidal category of presheaves of sets on that category: its
unit, multiplication and inverse are the identity automorphism, composition and the inverse
automorphism, taken pointwise over the points of `Z`. -/
@[instance_reducible, stacks 06PP
  "part (1): the group-object structure on Isom_{X/Y}(x, x) over Z"]
noncomputable def relativeAutomorphismPresheafGrpObj :
    GrpObj (relativeAutomorphismPresheaf B S hS Z hZ f x) where
  one :=
    { app a := ↾fun _ => (1 : RelativeAutomorphism B S hS Z hZ f x a.unop)
      naturality a a' h := by
        ext
        exact (map_one ((relativeAutomorphismGroupPresheaf B S hS Z hZ f x).map h).hom).symm }
  mul :=
    { app a := ↾fun φ => (φ.1 * φ.2 : RelativeAutomorphism B S hS Z hZ f x a.unop)
      naturality a a' h := by
        ext
        exact (map_mul ((relativeAutomorphismGroupPresheaf B S hS Z hZ f x).map h).hom _ _).symm }
  inv :=
    { app a := ↾fun φ => (φ⁻¹ : RelativeAutomorphism B S hS Z hZ f x a.unop)
      naturality a a' h := by
        ext
        exact (map_inv ((relativeAutomorphismGroupPresheaf B S hS Z hZ f x).map h).hom _).symm }
  one_mul := by ext a φ; exact one_mul _
  mul_one := by ext a φ; exact mul_one _
  mul_assoc := by ext a φ; exact mul_assoc _ _ _
  left_inv := by ext a φ; exact inv_mul_cancel _
  right_inv := by ext a φ; exact mul_inv_cancel _

/-- The multiplication of `AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj` is
composition of relative automorphisms. -/
@[stacks 06PP "part (1): the multiplication of the group object is composition"]
theorem relativeAutomorphismPresheafGrpObj_mul
    (a : ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ)
    (φ : (CategoryTheory.MonoidalCategoryStruct.tensorObj
      (relativeAutomorphismPresheaf B S hS Z hZ f x)
      (relativeAutomorphismPresheaf B S hS Z hZ f x)).obj a) :
    letI := relativeAutomorphismPresheafGrpObj B S hS Z hZ f x
    (MonObj.mul (X := relativeAutomorphismPresheaf B S hS Z hZ f x)).app a φ =
      (φ.1 * φ.2 : RelativeAutomorphism B S hS Z hZ f x a.unop) := rfl

/-- The unit of `AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj` is the identity
automorphism. -/
@[stacks 06PP "part (1): the unit of the group object is the identity automorphism"]
theorem relativeAutomorphismPresheafGrpObj_one
    (a : ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ)
    (t : (CategoryTheory.MonoidalCategoryStruct.tensorUnit
      (((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ ⥤ Type u)).obj a) :
    letI := relativeAutomorphismPresheafGrpObj B S hS Z hZ f x
    (MonObj.one (X := relativeAutomorphismPresheaf B S hS Z hZ f x)).app a t =
      (1 : RelativeAutomorphism B S hS Z hZ f x a.unop) := rfl

/-- The inverse of `AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj` is the inverse
automorphism. -/
@[stacks 06PP "part (1): the inverse of the group object is the inverse automorphism"]
theorem relativeAutomorphismPresheafGrpObj_inv
    (a : ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)ᵒᵖ)
    (φ : RelativeAutomorphism B S hS Z hZ f x a.unop) :
    (GrpObj.inv (X := relativeAutomorphismPresheaf B S hS Z hZ f x)
      (self := relativeAutomorphismPresheafGrpObj B S hS Z hZ f x)).app a φ = φ⁻¹ := rfl

end AlgebraicGeometry.Stack

end
