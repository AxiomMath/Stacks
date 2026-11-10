module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
import all StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison

/-!
# The tangent space of a predeformation category does not depend on the presentation

Section 07T2 forms the predeformation category `𝓕_{𝒳,k,x₀}` of a point `x₀` of `𝒳` over `Spec k`
over the category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k`, for a chosen
factorization `Spec k ⟶ Spec Λ ⟶ S` of the point. The source remarks that the result does not
depend on the choice of `Λ`. This file proves the part of that independence which the tangent
spaces see: for two factorizations `Spec k ⟶ Spec Λ₁ ⟶ S` and `Spec k ⟶ Spec Λ₂ ⟶ S` of the
same point, the functors `V ↦ F(k[V])` of fibrewise isomorphism classes of the two predeformation
categories on finite-dimensional `k`-vector spaces are naturally isomorphic, and so the two
tangent spaces are `k`-linearly isomorphic for their canonical structures (Stacks 06IH).

The reason is that the structure map `Λ → k[V]` of a square-zero extension of `k` factors through
`k`. So the composite `Spec k[V] ⟶ Spec Λ ⟶ S` is `Spec k[V] ⟶ Spec k ⟶ S` whatever `Λ` is,
and a deformation of `x₀` over `k[V]` for `Λ₁` is literally a deformation over `k[V]` for `Λ₂`:
the same object of `𝒳`, the same arrow out of `x₀`. The same holds for the arrows between such
deformations lying over `k[V] ⟶ k[W]` for a linear map `V ⟶ W`. No relation between `Λ₁` and
`Λ₂` is needed, in particular no localization, so the result applies to the local ring
`𝒪_{S,s}` with any ring structure it may be presented with.

## Main definitions

* `Deformation.FiberEquivPreservesLifts`: a family of bijections between fibres of two cofibred
  categories over images of a common functor, matching the arrows over images of each arrow.
* `Deformation.fiberEquivClassIso`: the natural isomorphism of functors of isomorphism classes it
  induces.
* `Deformation.Artin.DeformationObject.changePresentation`: a deformation over a square-zero
  extension, read for another presentation of the point.
* `Deformation.Artin.squareZeroClassesIsoOfPresentations`: the natural isomorphism of the
  square-zero functors of isomorphism classes of the two predeformation categories.

## Main results

* `Deformation.nonempty_artinianTangentSpace_linearEquiv_of_iso`: naturally isomorphic
  square-zero functors of isomorphism classes give linearly isomorphic tangent spaces.
* `Deformation.Artin.nonempty_artinianTangentSpace_linearEquiv_of_presentations`: the tangent
  spaces of the predeformation categories at two presentations of a point are linearly
  isomorphic.
* `Deformation.Artin.finiteDimensional_artinianTangentSpace_of_presentation`: the finiteness of
  the tangent space passes from one presentation to another.

## Implementation notes

Everything is stated for arbitrary realizations `Deformation.Artin.PredeformationConstruction` of
the two predeformation categories and uses only their characterizing fields, never the defining
equations of `Deformation.Artin.predeformationCategory`.

The linear comparison is the one Stacks 06I6 and 06I7 force: both tangent spaces carry the unique
linear structure of a finite-product preserving set-valued functor on finite-dimensional vector
spaces, and a natural isomorphism of those functors lifts to a natural isomorphism of their linear
lifts. It is the lemma `exists_linearEquiv_of_natIso` of
`StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison`.

## References

* [Stacks Project, Section 07T2](https://stacks.math.columbia.edu/tag/07T2)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public section

open CategoryTheory

/-! ### Isomorphism classes along fibrewise bijections -/

namespace Deformation

section FiberTransport

universe v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃ v₄

/-- **Two objects of a fibre have the same class exactly when a vertical arrow joins them.** In a
category cofibred in groupoids a vertical arrow is an isomorphism of the fibre, and an isomorphism
of the fibre is a vertical arrow. -/
theorem classOf_eq_iff_exists_isHomLift_id {C : Type u₁} [Category.{v₁} C]
    (𝓕 : BasedCategory.{v₃, u₃} C) (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {A : C}
    (x y : 𝓕.p.Fiber A) :
    classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y ↔ ∃ m : x.1 ⟶ y.1, 𝓕.p.IsHomLift (𝟙 A) m := by
  constructor
  · intro h
    have hq : Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) x =
        Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) y := by
      rw [← classOf_eq 𝓕 h𝓕 x, ← classOf_eq 𝓕 h𝓕 y, h]
    obtain ⟨i⟩ := Quotient.exact hq
    exact ⟨i.hom.1, i.hom.2⟩
  · rintro ⟨m, hm⟩
    have := hm
    simpa using map_classOf 𝓕 h𝓕 (𝟙 A) x y m

variable {D : Type u₀} [Category.{v₀} D] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] (s₁ : D ⥤ C₁) (s₂ : D ⥤ C₂)
  {𝓕₁ : BasedCategory.{v₃, u₃} C₁} {𝓕₂ : BasedCategory.{v₄, u₃} C₂}
  (e : ∀ V : D, 𝓕₁.p.Fiber (s₁.obj V) ≃ 𝓕₂.p.Fiber (s₂.obj V))

/-- A family of bijections `e V` between the fibres of `𝓕₁` over `s₁ V` and of `𝓕₂` over `s₂ V`
*preserves lifts* when, for every arrow `g : V ⟶ W` of the indexing category, two objects of the
fibres of `𝓕₁` are joined by an arrow over `s₁ g` exactly when their images are joined by an arrow
over `s₂ g`. -/
def FiberEquivPreservesLifts : Prop :=
  ∀ ⦃V W : D⦄ (g : V ⟶ W) (x : 𝓕₁.p.Fiber (s₁.obj V)) (y : 𝓕₁.p.Fiber (s₁.obj W)),
    (∃ m : x.1 ⟶ y.1, 𝓕₁.p.IsHomLift (s₁.map g) m) ↔
      ∃ m : (e V x).1 ⟶ (e W y).1, 𝓕₂.p.IsHomLift (s₂.map g) m

variable {s₁ s₂ e}

/-- The inverse bijections of a lift-preserving family preserve lifts. -/
theorem FiberEquivPreservesLifts.symm (he : FiberEquivPreservesLifts s₁ s₂ e) :
    FiberEquivPreservesLifts s₂ s₁ (fun V => (e V).symm) := by
  intro V W g x y
  have h := he g ((e V).symm x) ((e W).symm y)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

variable (h₁ : IsCofiberedInGroupoids 𝓕₁.p) (h₂ : IsCofiberedInGroupoids 𝓕₂.p)

/-- A lift-preserving family of bijections preserves and reflects fibrewise isomorphy. -/
theorem FiberEquivPreservesLifts.classOf_eq_iff (he : FiberEquivPreservesLifts s₁ s₂ e) {V : D}
    (x y : 𝓕₁.p.Fiber (s₁.obj V)) :
    classOf 𝓕₂ h₂ (e V x) = classOf 𝓕₂ h₂ (e V y) ↔ classOf 𝓕₁ h₁ x = classOf 𝓕₁ h₁ y := by
  rw [classOf_eq_iff_exists_isHomLift_id, classOf_eq_iff_exists_isHomLift_id]
  have h := he (𝟙 V) x y
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact h.symm

variable (s₁ s₂ e)

/-- The map of isomorphism classes induced by a family of bijections of fibres: the class of `x`
goes to the class of `e V x` (`Deformation.fiberEquivClassMap_classOf`). -/
noncomputable def fiberEquivClassMap (V : D) :
    (isomorphismClasses 𝓕₁ h₁).obj (s₁.obj V) → (isomorphismClasses 𝓕₂ h₂).obj (s₂.obj V) :=
  fun z => classOf 𝓕₂ h₂ (e V (classOf_surjective 𝓕₁ h₁ _ z).choose)

variable {s₁ s₂ e}

/-- The induced map of isomorphism classes sends the class of `x` to the class of `e V x`. -/
theorem fiberEquivClassMap_classOf (he : FiberEquivPreservesLifts s₁ s₂ e) {V : D}
    (x : 𝓕₁.p.Fiber (s₁.obj V)) :
    fiberEquivClassMap s₁ s₂ e h₁ h₂ V (classOf 𝓕₁ h₁ x) = classOf 𝓕₂ h₂ (e V x) :=
  (he.classOf_eq_iff h₁ h₂ _ _).2 (classOf_surjective 𝓕₁ h₁ _ (classOf 𝓕₁ h₁ x)).choose_spec

/-- The induced map of isomorphism classes is natural. -/
theorem fiberEquivClassMap_naturality (he : FiberEquivPreservesLifts s₁ s₂ e) {V W : D}
    (g : V ⟶ W) (z : (isomorphismClasses 𝓕₁ h₁).obj (s₁.obj V)) :
    fiberEquivClassMap s₁ s₂ e h₁ h₂ W ((isomorphismClasses 𝓕₁ h₁).map (s₁.map g) z) =
      (isomorphismClasses 𝓕₂ h₂).map (s₂.map g) (fiberEquivClassMap s₁ s₂ e h₁ h₂ V z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective 𝓕₁ h₁ _ z
  obtain ⟨y, m, hm⟩ := exists_pushforward h₁ (s₁.map g) x.1 x.2
  have := hm
  let y' : 𝓕₁.p.Fiber (s₁.obj W) := ⟨y, IsHomLift.codomain_eq 𝓕₁.p (s₁.map g) m⟩
  obtain ⟨m', hm'⟩ := (he g x y').1 ⟨m, hm⟩
  have := hm'
  rw [map_classOf 𝓕₁ h₁ (s₁.map g) x y' m, fiberEquivClassMap_classOf h₁ h₂ he,
    fiberEquivClassMap_classOf h₁ h₂ he, map_classOf 𝓕₂ h₂ (s₂.map g) (e V x) (e W y') m']

/-- The bijection of isomorphism classes induced by a lift-preserving family of bijections of
fibres. -/
noncomputable def fiberEquivClassEquiv (he : FiberEquivPreservesLifts s₁ s₂ e) (V : D) :
    (isomorphismClasses 𝓕₁ h₁).obj (s₁.obj V) ≃ (isomorphismClasses 𝓕₂ h₂).obj (s₂.obj V) where
  toFun := fiberEquivClassMap s₁ s₂ e h₁ h₂ V
  invFun := fiberEquivClassMap s₂ s₁ (fun V => (e V).symm) h₂ h₁ V
  left_inv z := by
    obtain ⟨x, rfl⟩ := classOf_surjective 𝓕₁ h₁ _ z
    simp only [fiberEquivClassMap_classOf h₁ h₂ he, fiberEquivClassMap_classOf h₂ h₁ he.symm,
      Equiv.symm_apply_apply]
  right_inv z := by
    obtain ⟨y, rfl⟩ := classOf_surjective 𝓕₂ h₂ _ z
    simp only [fiberEquivClassMap_classOf h₂ h₁ he.symm, fiberEquivClassMap_classOf h₁ h₂ he,
      Equiv.apply_symm_apply]

/-- **A lift-preserving family of bijections of fibres induces a natural isomorphism of the
functors of isomorphism classes**, restricted along `s₁` and `s₂`. Its component at `V` sends the
class of `x` to the class of `e V x`. -/
noncomputable def fiberEquivClassIso (he : FiberEquivPreservesLifts s₁ s₂ e) :
    s₁ ⋙ isomorphismClasses 𝓕₁ h₁ ≅ s₂ ⋙ isomorphismClasses 𝓕₂ h₂ :=
  NatIso.ofComponents (fun V => Equiv.toIso (fiberEquivClassEquiv h₁ h₂ he V))
    (fun {V W} g => by
      ext z
      exact fiberEquivClassMap_naturality h₁ h₂ he g z)

end FiberTransport

/-! ### Linearly isomorphic tangent spaces from naturally isomorphic square-zero functors -/

section LinearEquiv

universe u u' w v₁ v₂ u₁

/-- **Predeformation categories whose square-zero functors of isomorphism classes are naturally
isomorphic have linearly isomorphic tangent spaces**, for the canonical vector-space structures of
Stacks 06IH. The two categories may lie over the categories `𝒞_{Λ₁}` and `𝒞_{Λ₂}` of two different
coefficient rings with the same residue field `k`. -/
theorem nonempty_artinianTangentSpace_linearEquiv_of_iso {Λ₁ : Type u} {Λ₂ : Type u'}
    {k : Type w} [CommRing Λ₁] [CommRing Λ₂] [Field k] [Algebra Λ₁ k] [Algebra Λ₂ k]
    (𝓖₁ : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ₁ k))
    (𝓖₂ : BasedCategory.{v₂, u₁} (ArtinianLocalAlgCat.{u', w, w} Λ₂ k))
    [h₁ : Fact (IsPredeformationCategory 𝓖₁.p)] [h₂ : Fact (IsPredeformationCategory 𝓖₂.p)]
    [hS₁ : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖₁ h₁.out.cofibered)))]
    [hS₂ : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖₂ h₂.out.cofibered)))]
    (α : squareZeroExtensionArtinian.{u, w, w} Λ₁ k ⋙ isomorphismClasses 𝓖₁ h₁.out.cofibered ≅
      squareZeroExtensionArtinian.{u', w, w} Λ₂ k ⋙ isomorphismClasses 𝓖₂ h₂.out.cofibered) :
    Nonempty (artinianTangentSpace Λ₁ k (isomorphismClasses 𝓖₁ h₁.out.cofibered) ≃ₗ[k]
      artinianTangentSpace Λ₂ k (isomorphismClasses 𝓖₂ h₂.out.cofibered)) := by
  let F₁ := squareZeroExtensionArtinian.{u, w, w} Λ₁ k ⋙ isomorphismClasses 𝓖₁ h₁.out.cofibered
  let F₂ := squareZeroExtensionArtinian.{u', w, w} Λ₂ k ⋙ isomorphismClasses 𝓖₂ h₂.out.cofibered
  let A₁ := associatedTangentSpaceModuleStructureUnlifted 𝓖₁ h₁.out hS₁.out
  let A₂ := associatedTangentSpaceModuleStructureUnlifted 𝓖₂ h₂.out hS₂.out
  have hc₁ := associatedSquareZeroFunctor_conditions 𝓖₁ h₁.out hS₁.out
  have hc₂ := associatedSquareZeroFunctor_conditions 𝓖₂ h₂.out hS₂.out
  have : Unique (F₁.obj (FGModuleCat.of k PUnit.{w + 1})) := @Unique.mk' _ ⟨hc₁.1.some⟩ hc₁.2.1
  have : Unique (F₂.obj (FGModuleCat.of k PUnit.{w + 1})) := @Unique.mk' _ ⟨hc₂.1.some⟩ hc₂.2.1
  have : Limits.PreservesFiniteProducts F₁ :=
    ⟨fun _ => Limits.preservesLimitsOfShape_of_natIso (eqToIso A₁.forget_comp)⟩
  have : Limits.PreservesFiniteProducts F₂ :=
    ⟨fun _ => Limits.preservesLimitsOfShape_of_natIso (eqToIso A₂.forget_comp)⟩
  obtain ⟨e, -⟩ := Deformation.Artin.exists_linearEquiv_of_natIso F₁ F₂ A₁ A₂ α (FGModuleCat.of k k)
  exact ⟨(associatedTangentSpaceCarrierLinearEquivUnlifted 𝓖₁ h₁.out hS₁.out).symm.trans
    (e.trans (associatedTangentSpaceCarrierLinearEquivUnlifted 𝓖₂ h₂.out hS₂.out))⟩

end LinearEquiv

end Deformation

/-! ### Changing the presentation of the point -/

namespace Deformation.Artin

noncomputable section PresentationChange

open AlgebraicGeometry

universe u v w

/-- A finite-dimensional `k`-vector space as a module over `kᵐᵒᵖ`, through `MulOpposite.unop`. -/
local instance instModuleMulOppositeFGModuleCatPresentationChange {k : Type u} [Field k]
    (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The scalar actions of `k` and of `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance instIsCentralScalarFGModuleCatPresentationChange {k : Type u} [Field k]
    (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

attribute [local instance] PredeformationConstruction.category

/-- Equal objects of a slice category have equal structure morphisms. -/
theorem eq_of_overMk_eq {S Y : Scheme.{u}} {f g : Y ⟶ S} (h : Over.mk f = Over.mk g) : f = g :=
  eq_of_heq (congr_arg_heq (fun Z : Over S => Z.hom) h)

variable {k : Type u} [Field k] {S : Scheme.{u}}

/-- The structure map of a square-zero extension `k[V]` of `k` over `Spec Λ ⟶ S` factors through
`Spec k`. -/
theorem specMap_algebraMap_squareZero (Λ : Type u) [CommRing Λ] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (V : FGModuleCat.{u} k) :
    Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj V))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k V))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  change Spec.map (CommRingCat.ofHom
    ((algebraMap k (TrivSqZeroExt k V)).comp (algebraMap Λ k))) ≫ iΛ = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

variable {Λ₁ : Type u} [CommRing Λ₁] [Algebra Λ₁ k] {i₁ : Spec (.of Λ₁) ⟶ S}
  {Λ₂ : Type u} [CommRing Λ₂] [Algebra Λ₂ k] {i₂ : Spec (.of Λ₂) ⟶ S}
  {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
  {hx₁ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ₁ k)) ≫ i₁)}
  {hx₂ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ₂ k)) ≫ i₂)}

variable (hx₁ hx₂) in
include hx₁ hx₂ in
/-- Over two presentations of the same point, a square-zero extension `k[V]` lies over the same
scheme over `S`. -/
theorem overMk_squareZero_eq (V : FGModuleCat.{u} k) :
    Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ₁ ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V))) ≫ i₁) =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ₂ ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V))) ≫ i₂) := by
  rw [specMap_algebraMap_squareZero, specMap_algebraMap_squareZero,
    eq_of_overMk_eq (hx₁.symm.trans hx₂)]
  rfl

/-- The residue maps of the square-zero extension `k[V]` in `𝒞_{Λ₁}` and in `𝒞_{Λ₂}` agree: both
are the first projection. -/
theorem residueMap_squareZero_eq (V : FGModuleCat.{u} k) :
    residueMap ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V) =
      residueMap ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) :=
  RingHom.ext fun x => (squareZeroExtensionArtinian_residue Λ₂ k V x).trans
    (squareZeroExtensionArtinian_residue Λ₁ k V x).symm

/-- A deformation of `x₀` over a square-zero extension `k[V]` of `𝒞_{Λ₁}`, read as a deformation
over the square-zero extension `k[V]` of `𝒞_{Λ₂}`: the same deformed object and the same arrow out
of `x₀`. -/
def DeformationObject.changePresentation (V : FGModuleCat.{u} k)
    (a : DeformationObject i₁ q x₀ hx₁)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) :
    DeformationObject i₂ q x₀ hx₂ where
  algebra := (squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V
  point := a.point
  arrow := a.arrow
  base := a.base.trans ((congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ₁ k =>
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ₁ A)) ≫ i₁)) ha).trans
      (overMk_squareZero_eq hx₁ hx₂ V))
  arrow_base := by
    obtain ⟨A, pt, arr, base, ab⟩ := a
    dsimp only at ha
    subst ha
    exact ab.trans (congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
      (residueMap_squareZero_eq (Λ₁ := Λ₁) (Λ₂ := Λ₂) V).symm)

/-- The algebra of a deformation read for the presentation by `Λ₂` is `k[V]` over `Λ₂`. -/
@[simp]
theorem DeformationObject.changePresentation_algebra (V : FGModuleCat.{u} k)
    (a : DeformationObject i₁ q x₀ hx₁)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) :
    (a.changePresentation (hx₂ := hx₂) V ha).algebra =
      (squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V :=
  rfl

/-- Reading a deformation for another presentation does not change its object. -/
@[simp]
theorem DeformationObject.changePresentation_point (V : FGModuleCat.{u} k)
    (a : DeformationObject i₁ q x₀ hx₁)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) :
    (a.changePresentation (hx₂ := hx₂) V ha).point = a.point :=
  rfl

/-- Reading a deformation for another presentation does not change its arrow. -/
@[simp]
theorem DeformationObject.changePresentation_arrow (V : FGModuleCat.{u} k)
    (a : DeformationObject i₁ q x₀ hx₁)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) :
    (a.changePresentation (hx₂ := hx₂) V ha).arrow = a.arrow :=
  rfl

/-- The arrow of a deformation, compared along an equality of deformations. -/
theorem DeformationObject.arrow_eq_of_eq {iΛ : Spec (.of Λ₁) ⟶ S}
    {hx : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ₁ k)) ≫ iΛ)}
    {c b : DeformationObject iΛ q x₀ hx} (h : c = b) :
    c.arrow = b.arrow ≫ eqToHom (congrArg DeformationObject.point h).symm := by
  subst h
  simp

/-- A morphism of deformations over the image `k[V] ⟶ k[W]` of a linear map `g : V ⟶ W` in
`𝒞_{Λ₁}`, read for the presentation by `Λ₂`: the same reversed arrow of `X`, over the image of `g`
in `𝒞_{Λ₂}`. -/
def DeformationMorphism.changePresentation {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    {a b : DeformationObject i₁ q x₀ hx₁}
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj W)
    (m : DeformationMorphism i₁ q x₀ hx₁ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g ≫
      eqToHom hb.symm) :
    DeformationMorphism i₂ q x₀ hx₂ (a.changePresentation V ha) (b.changePresentation W hb) where
  ringHom := (squareZeroExtensionArtinian.{u, u, u} Λ₂ k).map g
  arrow := m.arrow
  triangle := m.triangle
  arrow_base := by
    obtain ⟨A, pt, arr, base, ab⟩ := a
    obtain ⟨B, pt', arr', base', ab'⟩ := b
    obtain ⟨r, marr, tri, mab⟩ := m
    dsimp only at ha hb hm ⊢
    subst ha hb
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
    subst hm
    have hmap : ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).map g).hom.toRingHom =
        ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g).hom.toRingHom :=
      RingHom.ext fun _ => rfl
    exact mab.trans (congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hmap.symm)

/-- The ring map of a morphism of deformations read for the presentation by `Λ₂` is the image
of `g` in `𝒞_{Λ₂}`. -/
@[simp]
theorem DeformationMorphism.changePresentation_ringHom {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    {a b : DeformationObject i₁ q x₀ hx₁}
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj W)
    (m : DeformationMorphism i₁ q x₀ hx₁ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g ≫
      eqToHom hb.symm) :
    (m.changePresentation (hx₂ := hx₂) g ha hb hm).ringHom =
      (squareZeroExtensionArtinian.{u, u, u} Λ₂ k).map g :=
  rfl

/-- Reading a morphism of deformations for another presentation does not change its arrow. -/
@[simp]
theorem DeformationMorphism.changePresentation_arrow {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    {a b : DeformationObject i₁ q x₀ hx₁}
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj W)
    (m : DeformationMorphism i₁ q x₀ hx₁ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g ≫
      eqToHom hb.symm) :
    (m.changePresentation (hx₂ := hx₂) g ha hb hm).arrow = m.arrow :=
  rfl

variable (D₁ : PredeformationConstruction i₁ q x₀ hx₁) (D₂ : PredeformationConstruction i₂ q x₀ hx₂)

/-- The algebra of the deformation underlying an object of a fibre is the base of that fibre. -/
theorem PredeformationConstruction.algebra_eq_of_fiber {A : ArtinianLocalAlgCat.{u, u, u} Λ₁ k}
    (z : (BasedCategory.ofFunctor D₁.projection).p.Fiber A) : (D₁.objects z.1).algebra = A :=
  (D₁.object_projection z.1).symm.trans z.2

/-- An object of the fibre of `𝓕` over `k[V]` for the presentation by `Λ₁`, read as an object of
the fibre over `k[V]` for the presentation by `Λ₂`. -/
def changePresentationFiber (V : FGModuleCat.{u} k)
    (z : (BasedCategory.ofFunctor D₁.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)) :
    (BasedCategory.ofFunctor D₂.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V) :=
  ⟨D₂.objects.symm ((D₁.objects z.1).changePresentation V (D₁.algebra_eq_of_fiber z)),
    (D₂.object_projection _).trans
      (congrArg DeformationObject.algebra (D₂.objects.apply_symm_apply _))⟩

/-- The deformation underlying the read object of a fibre. -/
theorem objects_changePresentationFiber (V : FGModuleCat.{u} k)
    (z : (BasedCategory.ofFunctor D₁.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)) :
    D₂.objects (changePresentationFiber D₁ D₂ V z).1 =
      (D₁.objects z.1).changePresentation V (D₁.algebra_eq_of_fiber z) :=
  D₂.objects.apply_symm_apply _

/-- Reading an object of a fibre for the presentation by `Λ₂` and back gives the object back. -/
theorem changePresentationFiber_changePresentationFiber (V : FGModuleCat.{u} k)
    (z : (BasedCategory.ofFunctor D₁.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V)) :
    changePresentationFiber D₂ D₁ V (changePresentationFiber D₁ D₂ V z) = z := by
  apply Subtype.ext
  change D₁.objects.symm _ = z.1
  apply D₁.objects.symm_apply_eq.mpr
  have hz := objects_changePresentationFiber D₁ D₂ V z
  have hp : (D₂.objects (changePresentationFiber D₁ D₂ V z).1).point = (D₁.objects z.1).point :=
    congrArg DeformationObject.point hz
  refine deformationObject_ext_of_arrow (D₁.algebra_eq_of_fiber z).symm hp ?_
  exact DeformationObject.arrow_eq_of_eq hz

/-- **A morphism of a predeformation category lies over `f` exactly when its ring map is `f`**, up
to the identifications of the algebras of its endpoints with the source and target of `f`. This
is the direction from the lift to the ring map. -/
theorem PredeformationConstruction.ringHom_eq_of_isHomLift
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ₁ k} (f : A ⟶ B) {a b : D₁.carrier}
    (ha : (D₁.objects a).algebra = A) (hb : (D₁.objects b).algebra = B) (m : a ⟶ b)
    (hm : (BasedCategory.ofFunctor D₁.projection).p.IsHomLift f m) :
    (D₁.morphisms a b m).ringHom = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
  have : D₁.projection.IsHomLift f m := hm
  rw [← D₁.morphism_projection m, IsHomLift.fac' D₁.projection f m]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **A morphism of a predeformation category lies over `f` exactly when its ring map is `f`**:
the direction from the ring map to the lift. -/
theorem PredeformationConstruction.isHomLift_of_ringHom_eq
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ₁ k} (f : A ⟶ B) {a b : D₁.carrier}
    (ha : (D₁.objects a).algebra = A) (hb : (D₁.objects b).algebra = B) (m : a ⟶ b)
    (hm : (D₁.morphisms a b m).ringHom = eqToHom ha ≫ f ≫ eqToHom hb.symm) :
    (BasedCategory.ofFunctor D₁.projection).p.IsHomLift f m := by
  refine IsHomLift.of_fac' (p := D₁.projection) f m ((D₁.object_projection a).trans ha)
    ((D₁.object_projection b).trans hb) ?_
  have h := D₁.morphism_projection m
  rw [hm] at h
  rw [← cancel_epi (eqToHom (D₁.object_projection a).symm),
    ← cancel_mono (eqToHom (D₁.object_projection b)), Category.assoc, h]
  simp

/-- An arrow between objects of fibres over the images of a linear map `g`, for the presentation
by `Λ₁`, gives an arrow between the read objects over the image of `g` for the presentation by
`Λ₂`. -/
theorem exists_isHomLift_changePresentationFiber {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (x : (BasedCategory.ofFunctor D₁.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V))
    (y : (BasedCategory.ofFunctor D₁.projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj W))
    (m : x.1 ⟶ y.1)
    (hm : (BasedCategory.ofFunctor D₁.projection).p.IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g) m) :
    ∃ m' : (changePresentationFiber D₁ D₂ V x).1 ⟶ (changePresentationFiber D₁ D₂ W y).1,
      (BasedCategory.ofFunctor D₂.projection).p.IsHomLift
        ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).map g) m' := by
  have hx := objects_changePresentationFiber D₁ D₂ V x
  have hy := objects_changePresentationFiber D₁ D₂ W y
  have hr := D₁.ringHom_eq_of_isHomLift ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).map g)
    (D₁.algebra_eq_of_fiber x) (D₁.algebra_eq_of_fiber y) m hm
  refine ⟨(D₂.morphisms (changePresentationFiber D₁ D₂ V x).1
    (changePresentationFiber D₁ D₂ W y).1).symm (transportDeformationMorphism hx hy
      ((D₁.morphisms x.1 y.1 m).changePresentation g (D₁.algebra_eq_of_fiber x)
        (D₁.algebra_eq_of_fiber y) hr)), ?_⟩
  refine D₂.isHomLift_of_ringHom_eq ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).map g)
    (congrArg DeformationObject.algebra hx) (congrArg DeformationObject.algebra hy) _ ?_
  rw [Equiv.apply_symm_apply, transportDeformationMorphism_ringHom]
  rfl

/-- **The fibres of the two predeformation categories over a square-zero extension correspond.**
For two presentations `Spec k ⟶ Spec Λ₁ ⟶ S` and `Spec k ⟶ Spec Λ₂ ⟶ S` of the same point, an
object of `𝓕_{Λ₁}` over `k[V]` is read as an object of `𝓕_{Λ₂}` over `k[V]` with the same deformed
object and the same arrow out of `x₀`. -/
def changePresentationFiberEquiv (V : FGModuleCat.{u} k) :
    (BasedCategory.ofFunctor D₁.projection).p.Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ₁ k).obj V) ≃
      (BasedCategory.ofFunctor D₂.projection).p.Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ₂ k).obj V) where
  toFun := changePresentationFiber D₁ D₂ V
  invFun := changePresentationFiber D₂ D₁ V
  left_inv := changePresentationFiber_changePresentationFiber D₁ D₂ V
  right_inv := changePresentationFiber_changePresentationFiber D₂ D₁ V

/-- The correspondence of fibres over square-zero extensions preserves lifts: arrows over the image
of a linear map correspond. -/
theorem changePresentationFiberEquiv_preservesLifts :
    FiberEquivPreservesLifts (squareZeroExtensionArtinian.{u, u, u} Λ₁ k)
      (squareZeroExtensionArtinian.{u, u, u} Λ₂ k) (changePresentationFiberEquiv D₁ D₂) := by
  intro V W g x y
  refine ⟨fun ⟨m, hm⟩ => exists_isHomLift_changePresentationFiber D₁ D₂ g x y m hm,
    fun ⟨m, hm⟩ => ?_⟩
  have h := exists_isHomLift_changePresentationFiber D₂ D₁ g (changePresentationFiber D₁ D₂ V x)
    (changePresentationFiber D₁ D₂ W y) m hm
  rw [changePresentationFiber_changePresentationFiber,
    changePresentationFiber_changePresentationFiber] at h
  exact h

/-- **The square-zero functors of isomorphism classes of the predeformation categories at two
presentations of a point are naturally isomorphic.** The component at `V` sends the class of a
deformation over `k[V]` for `Λ₁` to the class of the same deformation read for `Λ₂`. -/
noncomputable def squareZeroClassesIsoOfPresentations
    (h₁ : IsCofiberedInGroupoids (BasedCategory.ofFunctor D₁.projection).p)
    (h₂ : IsCofiberedInGroupoids (BasedCategory.ofFunctor D₂.projection).p) :
    squareZeroExtensionArtinian.{u, u, u} Λ₁ k ⋙
        isomorphismClasses (BasedCategory.ofFunctor D₁.projection) h₁ ≅
      squareZeroExtensionArtinian.{u, u, u} Λ₂ k ⋙
        isomorphismClasses (BasedCategory.ofFunctor D₂.projection) h₂ :=
  fiberEquivClassIso h₁ h₂ (changePresentationFiberEquiv_preservesLifts D₁ D₂)

/-- **The tangent spaces of the predeformation categories at two presentations of a point are
linearly isomorphic**, for their canonical vector-space structures of Stacks 06IH. -/
theorem nonempty_artinianTangentSpace_linearEquiv_of_presentations
    [h₁ : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₁.projection).p)]
    [h₂ : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₂.projection).p)]
    [Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor D₁.projection) h₁.out.cofibered)))]
    [Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor D₂.projection) h₂.out.cofibered)))] :
    Nonempty (artinianTangentSpace Λ₁ k
        (isomorphismClasses (BasedCategory.ofFunctor D₁.projection) h₁.out.cofibered) ≃ₗ[k]
      artinianTangentSpace Λ₂ k
        (isomorphismClasses (BasedCategory.ofFunctor D₂.projection) h₂.out.cofibered)) :=
  nonempty_artinianTangentSpace_linearEquiv_of_iso _ _
    (squareZeroClassesIsoOfPresentations D₁ D₂ h₁.out.cofibered h₂.out.cofibered)

/-- **The finiteness of the tangent space of a predeformation category does not depend on the
presentation of the point.** -/
theorem finiteDimensional_artinianTangentSpace_of_presentation
    [h₁ : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₁.projection).p)]
    [h₂ : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₂.projection).p)]
    [Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor D₁.projection) h₁.out.cofibered)))]
    [Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor D₂.projection) h₂.out.cofibered)))]
    [FiniteDimensional k (artinianTangentSpace Λ₁ k
      (isomorphismClasses (BasedCategory.ofFunctor D₁.projection) h₁.out.cofibered))] :
    FiniteDimensional k (artinianTangentSpace Λ₂ k
      (isomorphismClasses (BasedCategory.ofFunctor D₂.projection) h₂.out.cofibered)) :=
  (nonempty_artinianTangentSpace_linearEquiv_of_presentations D₁ D₂).some.finiteDimensional

/-- **The finiteness of the tangent space of a deformation category does not depend on the
presentation of the point**, in the form in which it is produced and consumed: from the lifted
model `Deformation.tangentSpaceArtinian` at the first presentation to the unlifted model
`Deformation.artinianTangentSpace` at the second, each for the canonical vector-space structure
of Stacks 06IH coming from the deformation-category structure. -/
theorem finiteDimensional_artinianTangentSpace_of_isDeformationCategory_of_presentation
    (hD₁ : IsDeformationCategory D₁.projection) (hD₂ : IsDeformationCategory D₂.projection)
    (h : letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₁.projection).p) :=
        ⟨hD₁.predeformation⟩
      letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
          (isomorphismClasses (BasedCategory.ofFunctor D₁.projection)
            hD₁.predeformation.cofibered))) :=
        ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
          (BasedCategory.ofFunctor D₁.projection) hD₁⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, u, u} Λ₁ k
        (isomorphismClasses (BasedCategory.ofFunctor D₁.projection)
          hD₁.predeformation.cofibered))) :
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₂.projection).p) :=
      ⟨hD₂.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
        (isomorphismClasses (BasedCategory.ofFunctor D₂.projection)
          hD₂.predeformation.cofibered))) :=
      ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor D₂.projection) hD₂⟩
    FiniteDimensional k (artinianTangentSpace Λ₂ k
      (isomorphismClasses (BasedCategory.ofFunctor D₂.projection)
        hD₂.predeformation.cofibered)) := by
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₁.projection).p) :=
    ⟨hD₁.predeformation⟩
  let := Fact.mk (schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
    (BasedCategory.ofFunctor D₁.projection) hD₁)
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D₂.projection).p) :=
    ⟨hD₂.predeformation⟩
  let := Fact.mk (schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
    (BasedCategory.ofFunctor D₂.projection) hD₂)
  have := h
  have : FiniteDimensional k (artinianTangentSpace Λ₁ k
      (isomorphismClasses (BasedCategory.ofFunctor D₁.projection)
        hD₁.predeformation.cofibered)) :=
    (tangentSpaceArtinianLinearEquivUnlifted (BasedCategory.ofFunctor D₁.projection)
      hD₁.predeformation (schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor D₁.projection) hD₁)).finiteDimensional
  exact finiteDimensional_artinianTangentSpace_of_presentation D₁ D₂

end PresentationChange

end Deformation.Artin

end
