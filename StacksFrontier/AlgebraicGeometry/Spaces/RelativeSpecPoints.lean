module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback

/-!
# The functor of points of the relative spectrum of an algebra sheaf

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `𝒜` be a sheaf of
commutative `𝒪_X`-algebras on the small étale site of `X`. A point of the relative spectrum
`\underline{Spec}_X(𝒜)` of Stacks 081W with values in an object `T` of the site is a point
`x ∈ X(T)` together with a morphism of `𝒪_X`-algebras `𝒜 ⟶ x_* 𝒪_T` into the direct image of the
structure sheaf of `T`. This file defines the presheaf of these points on the big fppf site of `S`,
together with its projection to `X`.

## Main definitions

* `AlgebraicGeometry.Space.specPointOver`: an object `T` of the site with a point `x ∈ X(T)`, as an
  algebraic space over `X`; `AlgebraicGeometry.Space.specPointOverMap` is the morphism over `X`
  induced by a morphism `T' ⟶ T` of the site.
* `AlgebraicGeometry.Space.RelativeSpecPoint`: the points of the relative spectrum with values in
  `T`, the pairs `(x, α)` with `x ∈ X(T)` and `α : 𝒜 ⟶ x_* 𝒪_T`, and
  `AlgebraicGeometry.Space.RelativeSpecPoint.map` their pullback along a morphism of the site.
* `AlgebraicGeometry.Space.compPushforwardAlgebraMap`: a morphism of algebras into a direct image
  composed with the map of direct images induced by a morphism over `X`.
* `AlgebraicGeometry.Space.relativeSpecPoints`: the presheaf of those points on the big fppf site,
  and `AlgebraicGeometry.Space.relativeSpecPointsπ` its projection to `X`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smallness of the morphisms of algebra sheaves -/

section Smallness

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The morphisms between two algebra sheaves on the small étale site form a `u`-small type.** -/
instance AlgebraSheaf.small_hom (A C : AlgebraSheaf.{u, u} B S hS F hF) : Small.{u} (A ⟶ C) := by
  have : LocallySmall.{u} ((SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u}) :=
    locallySmall_of_faithful
      ((Functor.whiskeringLeft _ _ CommRingCat.{u}).obj
        (equivSmallModel.{u} (SmallEtale B S hS F)).inverse.op)
  exact small_of_injective (f := fun φ : A ⟶ C => φ.right.hom) fun φ ψ h =>
    AlgebraSheaf.Hom.ext (Sheaf.hom_ext h)

end Smallness

/-! ### Points of an algebraic space as algebraic spaces over it -/

section Points

variable {X : AlgebraicSpaces B S hS}

/-- An object `T` of the big fppf site with a point `x ∈ X(T)`, read as an algebraic space over
`X`: the representable algebraic space of `T` with the morphism to `X` that `x` corresponds to
under the Yoneda lemma. -/
abbrev specPointOver (T : BigFppfOver B S hS) (x : X.1.obj (op T)) : Over X :=
  Over.mk (ObjectProperty.homMk (yonedaEquiv.symm x) : yonedaSpace B S hS T ⟶ X)

/-- The morphism over `X` induced by a morphism `g : T' ⟶ T` of the site, from `T'` with the
pulled-back point `X(g)(x)` to `T` with the point `x`. -/
def specPointOverMap {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : X.1.obj (op T)) :
    specPointOver B S hS T' (X.1.map g.op x) ⟶ specPointOver B S hS T x :=
  Over.homMk (ObjectProperty.homMk (yoneda.map g))
    (ObjectProperty.hom_ext _ (yonedaEquiv_symm_map g.op x).symm)

/-- The morphism of algebraic spaces underlying `specPointOverMap` is the representable map of
`g`. -/
@[simp]
theorem specPointOverMap_left {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : X.1.obj (op T)) :
    (specPointOverMap B S hS g x).left = ObjectProperty.homMk (yoneda.map g) :=
  rfl

end Points

/-! ### The points of the relative spectrum -/

section RelativeSpecPoint

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)

/-- **The points of the relative spectrum of `𝒜` with values in `T`**: a point `x ∈ X(T)` together
with a morphism of `𝒪_X`-algebras `𝒜 ⟶ x_* 𝒪_T` into the direct image of the structure sheaf of
`T`. -/
structure RelativeSpecPoint (T : BigFppfOver B S hS) : Type (u + 1) where
  /-- The underlying point of `X`. -/
  pt : X.1.obj (op T)
  /-- The morphism of `𝒪_X`-algebras into the direct image of the structure sheaf of `T`. -/
  hom : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T pt)

/-- The points of the relative spectrum with values in `T` are the pairs `(x, α)`. -/
def RelativeSpecPoint.equivSigma (T : BigFppfOver B S hS) :
    RelativeSpecPoint B S hS A T ≃
      Σ x : X.1.obj (op T), (A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) where
  toFun p := ⟨p.pt, p.hom⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The points of the relative spectrum with values in `T` form a `u`-small type. -/
instance RelativeSpecPoint.small (T : BigFppfOver B S hS) :
    Small.{u} (RelativeSpecPoint B S hS A T) :=
  small_map (RelativeSpecPoint.equivSigma B S hS A T)

variable {A}

/-- **A morphism of algebras into a direct image, pulled back along a morphism over `X`**: the
composite of `α : 𝒜 ⟶ P_* 𝒪_P` with the map `P_* 𝒪_P ⟶ Q_* 𝒪_Q` of direct images induced by
`f : Q ⟶ P`. -/
def compPushforwardAlgebraMap {P Q : Over X} (α : A ⟶ pushforwardAlgebra B S hS P) (f : Q ⟶ P) :
    A ⟶ pushforwardAlgebra B S hS Q :=
  α ≫ pushforwardAlgebraMap B S hS f

/-- `compPushforwardAlgebraMap α f` is the composite of `α` with the map of direct images
induced by `f`. -/
theorem compPushforwardAlgebraMap_def {P Q : Over X} (α : A ⟶ pushforwardAlgebra B S hS P)
    (f : Q ⟶ P) :
    compPushforwardAlgebraMap B S hS α f = α ≫ pushforwardAlgebraMap B S hS f :=
  rfl

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem compPushforwardAlgebraMap_id {P : Over X} (α : A ⟶ pushforwardAlgebra B S hS P) :
    compPushforwardAlgebraMap B S hS α (𝟙 P) = α := by
  rw [compPushforwardAlgebraMap_def, pushforwardAlgebraMap_id, Category.comp_id]

/-- Pulling back along a composite is pulling back twice. -/
theorem compPushforwardAlgebraMap_comp {P Q R : Over X} (α : A ⟶ pushforwardAlgebra B S hS P)
    (f : Q ⟶ P) (k : R ⟶ Q) :
    compPushforwardAlgebraMap B S hS α (k ≫ f) =
      compPushforwardAlgebraMap B S hS (compPushforwardAlgebraMap B S hS α f) k := by
  rw [compPushforwardAlgebraMap_def, compPushforwardAlgebraMap_def,
    compPushforwardAlgebraMap_def, pushforwardAlgebraMap_comp, Category.assoc]

/-- **Two pullbacks of a point of the relative spectrum agree** as soon as the points of `X` agree
and the two morphisms over `X` have the same underlying morphism of algebraic spaces. -/
theorem RelativeSpecPoint.mk_comp_eq {T : BigFppfOver B S hS} {P : Over X}
    (α : A ⟶ pushforwardAlgebra B S hS P) {x₁ x₂ : X.1.obj (op T)} (h : x₁ = x₂)
    (f₁ : specPointOver B S hS T x₁ ⟶ P) (f₂ : specPointOver B S hS T x₂ ⟶ P)
    (hf : f₁.left = f₂.left) :
    (⟨x₁, compPushforwardAlgebraMap B S hS α f₁⟩ : RelativeSpecPoint B S hS A T) =
      ⟨x₂, compPushforwardAlgebraMap B S hS α f₂⟩ := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

/-- The pullback of a point of the relative spectrum along a morphism `g : T' ⟶ T` of the site:
the point of `X` is pulled back, and the morphism of algebras is composed with the map of direct
images that `g` induces. -/
def RelativeSpecPoint.map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : RelativeSpecPoint B S hS A T) : RelativeSpecPoint B S hS A T' :=
  ⟨X.1.map g.op p.pt, compPushforwardAlgebraMap B S hS p.hom (specPointOverMap B S hS g p.pt)⟩

/-- The underlying point of `X` of a pulled-back point is the pulled-back point of `X`. -/
@[simp]
theorem RelativeSpecPoint.map_pt {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : RelativeSpecPoint B S hS A T) : (p.map B S hS g).pt = X.1.map g.op p.pt :=
  rfl

/-- The pullback of the point `(x, α)` along `g` is `(X(g)(x), α ∘ g_*)`. -/
theorem RelativeSpecPoint.map_mk {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : X.1.obj (op T))
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    RelativeSpecPoint.map B S hS g (⟨x, α⟩ : RelativeSpecPoint B S hS A T) =
      ⟨X.1.map g.op x, compPushforwardAlgebraMap B S hS α (specPointOverMap B S hS g x)⟩ :=
  rfl

/-- Pulling back a point along the identity does nothing. -/
theorem RelativeSpecPoint.map_id {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A T) :
    p.map B S hS (𝟙 T) = p := by
  obtain ⟨x, α⟩ := p
  rw [RelativeSpecPoint.map_mk]
  have h := RelativeSpecPoint.mk_comp_eq B S hS α
    (show X.1.map (𝟙 T).op x = x from FunctorToTypes.map_id_apply X.1 x)
    (specPointOverMap B S hS (𝟙 T) x) (𝟙 _) (ObjectProperty.hom_ext _ (yoneda.map_id T))
  rwa [compPushforwardAlgebraMap_id] at h

/-- Pulling back a point along a composite is pulling back twice. -/
theorem RelativeSpecPoint.map_comp {T T' T'' : BigFppfOver B S hS} (g : T' ⟶ T) (k : T'' ⟶ T')
    (p : RelativeSpecPoint B S hS A T) :
    p.map B S hS (k ≫ g) = (p.map B S hS g).map B S hS k := by
  obtain ⟨x, α⟩ := p
  rw [RelativeSpecPoint.map_mk, RelativeSpecPoint.map_mk, RelativeSpecPoint.map_mk,
    ← compPushforwardAlgebraMap_comp]
  exact RelativeSpecPoint.mk_comp_eq B S hS α
    (show X.1.map (k ≫ g).op x = X.1.map k.op (X.1.map g.op x) from
      FunctorToTypes.map_comp_apply X.1 g.op k.op x) _ _
    (ObjectProperty.hom_ext _ (yoneda.map_comp k g))

variable (A)

/-- **The functor of points of the relative spectrum of `𝒜`**, a presheaf on the big fppf site of
`S`: its value at `T` is (a `u`-small copy of) the set of pairs `(x, α)` with `x ∈ X(T)` and
`α : 𝒜 ⟶ x_* 𝒪_T` a morphism of `𝒪_X`-algebras. -/
def relativeSpecPoints : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (RelativeSpecPoint B S hS A T.unop)
  map g := ↾fun p => equivShrink _ (((equivShrink _).symm p).map B S hS g.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun p => by simp [RelativeSpecPoint.map_id]
  map_comp g k := ConcreteCategory.hom_ext _ _ fun p => by simp [RelativeSpecPoint.map_comp]

/-- The values of `AlgebraicGeometry.Space.relativeSpecPoints` are the points of the relative
spectrum. -/
def relativeSpecPointsEquiv (T : BigFppfOver B S hS) :
    (relativeSpecPoints B S hS A).obj (op T) ≃ RelativeSpecPoint B S hS A T :=
  (equivShrink _).symm

/-- `AlgebraicGeometry.Space.relativeSpecPointsEquiv` turns the action of the presheaf into the
pullback of points. -/
theorem relativeSpecPointsEquiv_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : (relativeSpecPoints B S hS A).obj (op T)) :
    relativeSpecPointsEquiv B S hS A T' ((relativeSpecPoints B S hS A).map g.op p) =
      (relativeSpecPointsEquiv B S hS A T p).map B S hS g :=
  (equivShrink _).symm_apply_apply _

/-- **The projection of the relative spectrum to `X`**, forgetting the morphism of algebras. -/
def relativeSpecPointsπ : relativeSpecPoints B S hS A ⟶ X.1 where
  app T := ↾fun p => (relativeSpecPointsEquiv B S hS A T.unop p).pt
  naturality _ _ g := ConcreteCategory.hom_ext _ _ fun p =>
    congrArg RelativeSpecPoint.pt (relativeSpecPointsEquiv_map B S hS A g.unop p)

/-- The projection to `X` sends a point of the relative spectrum to its underlying point of
`X`. -/
theorem relativeSpecPointsπ_app (T : BigFppfOver B S hS)
    (p : (relativeSpecPoints B S hS A).obj (op T)) :
    (relativeSpecPointsπ B S hS A).app (op T) p = (relativeSpecPointsEquiv B S hS A T p).pt :=
  rfl

end RelativeSpecPoint

end AlgebraicGeometry.Space

end
