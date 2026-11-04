module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeIsomSectionsOver
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionReindex

/-!
# 2-morphisms over a stack of an algebraic space lie over every 2-morphism of the target

For a 1-morphism `f : 𝒳 ⟶ Y` from an algebraic stack to (the stack of) an algebraic space, the
condition "`f(η) = α`" on a 2-morphism `η : x₁ ∘ q ⟶ x₂ ∘ q` is automatic: the fibres of the
category attached to `Y` are discrete, so two vertical morphisms between the same two objects
agree. Hence every 2-morphism `x₁ ∘ q ⟶ x₂ ∘ q` is a natural family of vertical morphisms over
`α`, i.e. a lift of `q` along `Isom^α(x₁, x₂) ⟶ Z`
(`AlgebraicGeometry.Stack.ChowGerbeIsomOver.relativeIsomorphismSectionOverEquiv`). In the proof
of [Stacks, Tag 0CQ7] `f` always has an algebraic space as target, and this is how the
isomorphisms `φ_{ij} : x_i ⟶ x_j` become sections of `I_{ij}`.

## Main results

* `AlgebraicGeometry.Stack.ChowGerbeIsomOver.map_app_eq_iso_hom_of_algebraicSpaceStack`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack.ChowGerbeIsomOver

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Over an algebraic space every 2-morphism `x₁ ∘ q ⟶ x₂ ∘ q` lies over `α`.** -/
theorem map_app_eq_iso_hom_of_algebraicSpaceStack {T Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : T ⟶ Z) (hT : IsAlgebraicSpace B S hS T) (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (η : algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₁ ⟶
      algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₂)
    (a : (fibredCategory B S hS T).val.obj) :
    f.hom.hom.map (η.hom.hom.toNatTrans.app a) =
      ((twistedPointOver q hZ f x₁ x₂ α).obj a).iso.hom := by
  have h1 : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 a.base)
      (f.hom.hom.map (η.hom.hom.toNatTrans.app a)) :=
    (BasedFunctor.isHomLift_iff f.hom.hom (𝟙 a.base) (η.hom.hom.toNatTrans.app a)).2
      (η.hom.hom.isHomLift' a)
  have h2 : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 a.base)
      ((twistedPointOver q hZ f x₁ x₂ α).obj a).iso.hom :=
    ((twistedPointOver q hZ f x₁ x₂ α).obj a).vertical
  exact fibredCategory_hom_ext' _ _
    ((IsHomLift.fac' _ (𝟙 a.base) _).trans (IsHomLift.fac' _ (𝟙 a.base)
      ((twistedPointOver q hZ f x₁ x₂ α).obj a).iso.hom).symm)

/-- **A 2-morphism `x₁ ∘ q ⟶ x₂ ∘ q` over an algebraic space is a lift of `q` along
`Isom^α(x₁, x₂) ⟶ Z`**, read through `relativeIsomorphismSectionOverEquiv`. -/
noncomputable def relVertFamilyOfTwoMorphismOfAlgebraicSpaceStack
    {T Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : T ⟶ Z) (hT : IsAlgebraicSpace B S hS T) (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (η : algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₁ ⟶
      algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₂) :
    RelVertFamily (fibredCategory B S hS T).val.p (twistedPointOver q hZ f x₁ x₂ α) :=
  relVertFamilyOfTwoMorphism q hT hZ f x₁ x₂ α η
    (map_app_eq_iso_hom_of_algebraicSpaceStack q hT hZ hY f x₁ x₂ α η)

end AlgebraicGeometry.Stack.ChowGerbeIsomOver

end
