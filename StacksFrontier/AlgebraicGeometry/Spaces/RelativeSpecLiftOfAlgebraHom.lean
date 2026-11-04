module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded

/-!
# Morphisms into a relative spectrum from algebra maps into a direct image

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `𝒜` a sheaf of commutative
`𝒪_X`-algebras, and `y : Y ⟶ X` a morphism of algebraic spaces. A morphism of `𝒪_X`-algebras
`β : 𝒜 ⟶ y_* 𝒪_Y` gives a morphism `Y ⟶ \underline{Spec}_X(𝒜)` over `X`: a point `t ∈ Y(T)`
goes to the point `(y ∘ t, α)` of the relative spectrum, where `α : 𝒜 ⟶ (y ∘ t)_* 𝒪_T` is `β`
followed by the map of direct images induced by `t`. This is half of the universal property of
the relative spectrum (Stacks 081W, Stacks 01LY for schemes); for `Y = X` and `y = 𝟙` it is the
section of `AlgebraicGeometry.Space.relativeSpecSection`.

## Main definitions

* `AlgebraicGeometry.Space.pointOverOfPoint`: a point `t ∈ Y(T)` as a morphism over `X` from `T`
  to `Y`.
* `AlgebraicGeometry.Space.relativeSpecLiftPoint`: the point `(y ∘ t, α)` of the relative
  spectrum.
* `AlgebraicGeometry.Space.relativeSpecLift`: the morphism of presheaves
  `Y ⟶ \underline{Spec}_X(𝒜)`, and `AlgebraicGeometry.Space.boundedRelativeSpecLift` the
  morphism of algebraic spaces into the bounded relative spectrum.

## Main results

* `AlgebraicGeometry.Space.relativeSpecLift_comp_π`: the morphism lies over `X`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Lift

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)

/-- The morphism of representable spaces given by a point is compatible with the morphisms to
`X`. -/
theorem yonedaEquiv_symm_comp_hom {T : BigFppfOver B S hS} (t : Y.1.obj (op T)) :
    yonedaEquiv.symm t ≫ y.hom = yonedaEquiv.symm (y.hom.app (op T) t) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **A point `t ∈ Y(T)` as a morphism over `X`** from `T`, with the point `y ∘ t` of `X`, to
`Y`. -/
def pointOverOfPoint (T : BigFppfOver B S hS) (t : Y.1.obj (op T)) :
    specPointOver B S hS T (y.hom.app (op T) t) ⟶ Over.mk y :=
  Over.homMk (ObjectProperty.homMk (yonedaEquiv.symm t)) (by
    refine ObjectProperty.hom_ext _ ?_
    exact yonedaEquiv_symm_comp_hom B S hS y t)

/-- The underlying morphism of `pointOverOfPoint` is the morphism of representable spaces given
by `t`. -/
@[simp]
theorem pointOverOfPoint_left (T : BigFppfOver B S hS) (t : Y.1.obj (op T)) :
    (pointOverOfPoint B S hS y T t).left = ObjectProperty.homMk (yonedaEquiv.symm t) :=
  rfl

variable {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (β : A ⟶ pushforwardAlgebra B S hS (Over.mk y))

/-- **The point of the relative spectrum given by a point `t ∈ Y(T)`**: the point `y ∘ t` of
`X`, with `β` followed by the map of direct images that `t` induces. -/
def relativeSpecLiftPoint (T : BigFppfOver B S hS) (t : Y.1.obj (op T)) :
    RelativeSpecPoint B S hS A T :=
  ⟨y.hom.app (op T) t, compPushforwardAlgebraMap B S hS β (pointOverOfPoint B S hS y T t)⟩

/-- The point of `X` underlying `relativeSpecLiftPoint` is `y ∘ t`. -/
@[simp]
theorem relativeSpecLiftPoint_pt (T : BigFppfOver B S hS) (t : Y.1.obj (op T)) :
    (relativeSpecLiftPoint B S hS y β T t).pt = y.hom.app (op T) t :=
  rfl

/-- Pulling back `relativeSpecLiftPoint` along `g : T' ⟶ T` gives the point attached to the
restriction of `t` to `T'`. -/
theorem relativeSpecLiftPoint_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (t : Y.1.obj (op T)) :
    (relativeSpecLiftPoint B S hS y β T t).map B S hS g =
      relativeSpecLiftPoint B S hS y β T' (Y.1.map g.op t) := by
  rw [relativeSpecLiftPoint, RelativeSpecPoint.map_mk, ← compPushforwardAlgebraMap_comp]
  refine RelativeSpecPoint.mk_comp_eq B S hS β
    (show X.1.map g.op (y.hom.app (op T) t) = y.hom.app (op T') (Y.1.map g.op t) from
      (y.hom.naturality_apply g.op t).symm) _ _ ?_
  refine ObjectProperty.hom_ext _ ?_
  exact (yonedaEquiv_symm_map g.op t).symm

/-- **The morphism `Y ⟶ \underline{Spec}_X(𝒜)` given by `β : 𝒜 ⟶ y_* 𝒪_Y`**, as a morphism of
presheaves into the functor of points of the relative spectrum. -/
def relativeSpecLift : Y.1 ⟶ relativeSpecPoints B S hS A where
  app T := ↾fun t => (relativeSpecPointsEquiv B S hS A T.unop).symm
    (relativeSpecLiftPoint B S hS y β T.unop t)
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    intro t
    apply (relativeSpecPointsEquiv B S hS A T'.unop).injective
    change relativeSpecPointsEquiv B S hS A T'.unop
        ((relativeSpecPointsEquiv B S hS A T'.unop).symm
          (relativeSpecLiftPoint B S hS y β T'.unop (Y.1.map g t))) =
      relativeSpecPointsEquiv B S hS A T'.unop ((relativeSpecPoints B S hS A).map g.unop.op
        ((relativeSpecPointsEquiv B S hS A T.unop).symm
          (relativeSpecLiftPoint B S hS y β T.unop t)))
    rw [relativeSpecPointsEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      relativeSpecLiftPoint_map]
    rfl

/-- Under `relativeSpecPointsEquiv`, the image of `t` by `relativeSpecLift` is
`relativeSpecLiftPoint`. -/
theorem relativeSpecPointsEquiv_relativeSpecLift_app (T : BigFppfOver B S hS)
    (t : Y.1.obj (op T)) :
    relativeSpecPointsEquiv B S hS A T ((relativeSpecLift B S hS y β).app (op T) t) =
      relativeSpecLiftPoint B S hS y β T t :=
  Equiv.apply_symm_apply _ _

/-- **The morphism into the relative spectrum lies over `X`.** -/
@[reassoc (attr := simp)]
theorem relativeSpecLift_comp_π :
    relativeSpecLift B S hS y β ≫ relativeSpecPointsπ B S hS A = y.hom := by
  ext T t
  exact congrArg RelativeSpecPoint.pt
    (relativeSpecPointsEquiv_relativeSpecLift_app B S hS y β T.unop t)

end Lift

section Bounded

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X) (A : QuasicoherentAlgebra B S hS X)
  (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
  (β : A.obj ⟶ pushforwardAlgebra B S hS (Over.mk y))

/-- **The morphism `Y ⟶ \underline{Spec}_X(𝒜)` of algebraic spaces given by `β : 𝒜 ⟶ y_* 𝒪_Y`**,
into the bounded relative spectrum. -/
def boundedRelativeSpecLift : Y ⟶ (boundedRelativeSpec B S hS A hA).obj.left :=
  ObjectProperty.homMk (relativeSpecLift B S hS y β)

/-- **The morphism into the bounded relative spectrum lies over `X`.** -/
@[reassoc (attr := simp)]
theorem boundedRelativeSpecLift_comp_hom :
    boundedRelativeSpecLift B S hS y A hA β ≫ (boundedRelativeSpec B S hS A hA).obj.hom = y :=
  ObjectProperty.hom_ext _ (relativeSpecLift_comp_π B S hS y β)

end Bounded

end AlgebraicGeometry.Space

end
