module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapToRepresentingSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# The relative map of Stacks 06CK does not depend on the data exhibiting it

The morphism `x_α : Z ⟶ X_y` of Stacks 06CK is attached to a scheme-valued point `y` of `𝒴` over
`U`, an algebraic space `X_y` over `U` together with an equivalence exhibiting it as representing
the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`, and a comparison isomorphism
`α : y|_Z ≅ F x`. None of these three is canonical: the point is produced by the 2-Yoneda lemma,
the representing algebraic space only exists, and `α` is pinned down only after the point is
chosen. The remark following Stacks 06CK is that `x_α` is nevertheless independent of all of
them, and this file proves it.

Concretely, let `θ : y₁ ≅ y₂` be a 2-isomorphism of two points — a natural isomorphism all of
whose components are vertical — and let `X_1`, `X_2` represent the 2-fibre products taken along
`y₁` and along `y₂`. Reindexing the 2-fibre product along `θ` identifies the two base changes
over the big fppf site of `U`, so `X_1` and `X_2` are isomorphic; and the isomorphism carries the
relative map attached to `α₁` to the relative map attached to `α₂`, for any two comparison
isomorphisms with `α₁ = θ|_Z ≫ α₂`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeSpaceIso`: the isomorphism of the two representing algebraic
  spaces induced by a 2-isomorphism of the two points.

## Main results

* `AlgebraicGeometry.Stack.relativeSpaceIso_hom_app_relativeSection`: that isomorphism carries
  the section of Stacks 06CK named by one set of data to the section named by the other.
* `AlgebraicGeometry.Stack.relativeMap_hom_comp_relativeSpaceIso`: the same statement for the
  morphism `x_α` itself.

## Implementation notes

Reindexing is `CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`, which is stated for a
2-isomorphism of the *first* leg of the 2-fibre product; the point is the first leg in the
presentation of Stacks 02ZW and Stacks 03YK that this library uses. The identification of the two
representing presheaves is then
`CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver` — two presheaves whose categories of
elements are equivalent over the site to one and the same category are isomorphic — and the
compatibility with named sections is
`CategoryTheory.PresheafOfCategories.hom_app_sectionOfObj_isoOfEquivalenceOver`.

What makes the computation short is that reindexing changes *only* the comparison isomorphism of
an object of the 2-fibre product, replacing `α` by `θ⁻¹ ≫ α`; so the object attached to the first
set of data is carried to the object attached to the second **on the nose**, by
`CategoryTheory.TwoFibreProductOver.obj_ext`, as soon as the two comparison isomorphisms are
related by `θ`. No transport of the section along an equality of objects of the site is needed.

The hypothesis `α₁ = θ|_Z ≫ α₂` is not a restriction: for two sets of data describing one object
of a category fibred in groupoids, the two comparison isomorphisms satisfy it automatically, by
the universal property of the strongly cartesian morphism through which both factor. That
deduction is carried out where the data are the `AlgebraicGeometry.Stack.FiniteHilbert.
RelativeMapData` of a quintuple.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  (F : 𝒳 ⥤ᵇ 𝒴) {U : BigFppfOver B S hS}
  {y₁ y₂ : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj}
  {Xy₁ Xy₂ : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
  (e₁ : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y₁ F.toFunctor)
    (PresheafOfCategories.discreteProjection Xy₁))
  (e₂ : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y₂ F.toFunctor)
    (PresheafOfCategories.discreteProjection Xy₂))
  (θ : y₁ ≅ y₂)
  (hθ : ∀ a : BigFppfOver B U.left.1 U.left.2,
    𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj a)) (θ.hom.app a))

/-- **The representing algebraic space of Stacks 06CK does not depend on the point.** A
2-isomorphism of two scheme-valued points of `𝒴` over `U` identifies any presheaf representing
the 2-fibre product taken along the first with any presheaf representing the one taken along the
second: reindexing the 2-fibre product along the 2-isomorphism identifies the two base changes
over the big fppf site of `U`, and a category over that site determines the presheaf representing
it. -/
noncomputable def relativeSpaceIso : Xy₁ ≅ Xy₂ :=
  PresheafOfCategories.isoOfEquivalenceOver e₁
    ((TwoFibreProductOver.reindexEquivalenceOver (p𝒴 := 𝒳.p) (G := F.toFunctor) θ hθ).trans e₂)

/-- **The relative map of Stacks 06CK does not depend on the data exhibiting it, at the level of
sections.** The identification of the two representing algebraic spaces carries the section of
`X_1` over `Z` named by `(Z, x, α₁)` to the section of `X_2` over `Z` named by `(Z, x, α₂)`,
whenever the two comparison isomorphisms are related by the 2-isomorphism of the points. -/
theorem relativeSpaceIso_hom_app_relativeSection
    (Z : BigFppfOver B U.left.1 U.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z)
    (α₁ : y₁.obj Z ≅ F.toFunctor.obj x)
    (hα₁ : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α₁.hom)
    (α₂ : y₂.obj Z ≅ F.toFunctor.obj x)
    (hα₂ : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α₂.hom)
    (hα : α₁.hom = θ.hom.app Z ≫ α₂.hom) :
    (relativeSpaceIso F e₁ e₂ θ hθ).hom.app (op Z)
        (relativeSection F y₁ e₁ Z x hx α₁ hα₁) =
      relativeSection F y₂ e₂ Z x hx α₂ hα₂ := by
  set E := TwoFibreProductOver.reindexEquivalenceOver (p𝒴 := 𝒳.p) (G := F.toFunctor) θ hθ
  set o₁ := relativeObj F y₁ Z x hx α₁ hα₁
  have hobj : (TwoFibreProductOver.reindex (p𝒴 := 𝒳.p) (G := F.toFunctor) θ hθ).obj o₁ =
      relativeObj F y₂ Z x hx α₂ hα₂ := by
    refine TwoFibreProductOver.obj_ext (Iso.ext ?_)
    change θ.inv.app Z ≫ α₁.hom = α₂.hom
    rw [hα, ← Category.assoc]
    simp
  have h1 := PresheafOfCategories.hom_app_sectionOfObj_isoOfEquivalenceOver e₁ (E.trans e₂) o₁
    (W := Z) rfl
  have h2 := PresheafOfCategories.sectionOfObj_trans E e₂ o₁ (W := Z) rfl
  have h3 := PresheafOfCategories.sectionOfObj_eq_of_obj_eq e₂ e₂ (E.hom.functor.obj o₁)
    (relativeObj F y₂ Z x hx α₂ hα₂)
    (Functor.congr_obj (TwoFibreProductOver.reindex_comp_fst
      (p𝒴 := 𝒳.p) (G := F.toFunctor) θ hθ) o₁)
    rfl (congrArg e₂.hom.functor.obj hobj)
  change (PresheafOfCategories.isoOfEquivalenceOver e₁ (E.trans e₂)).hom.app (op Z)
      (PresheafOfCategories.sectionOfObj e₁ o₁ rfl) = _
  rw [h1, h2]
  exact h3

/-- **The relative map of Stacks 06CK does not depend on the data exhibiting it.** The morphism
`x_α : Z ⟶ X_1` attached to one set of data, followed by the identification of the two
representing algebraic spaces, is the morphism `x_α : Z ⟶ X_2` attached to the other. -/
theorem relativeMap_hom_comp_relativeSpaceIso
    {hXy₁ : IsAlgebraicSpace B U.left.1 U.left.2 Xy₁}
    {hXy₂ : IsAlgebraicSpace B U.left.1 U.left.2 Xy₂}
    (Z : BigFppfOver B U.left.1 U.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z)
    (α₁ : y₁.obj Z ≅ F.toFunctor.obj x)
    (hα₁ : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α₁.hom)
    (α₂ : y₂.obj Z ≅ F.toFunctor.obj x)
    (hα₂ : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α₂.hom)
    (hα : α₁.hom = θ.hom.app Z ≫ α₂.hom) :
    (relativeMap F y₁ e₁ hXy₁ Z x hx α₁ hα₁).hom ≫ (relativeSpaceIso F e₁ e₂ θ hθ).hom =
      (relativeMap F y₂ e₂ hXy₂ Z x hx α₂ hα₂).hom := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, yonedaEquiv_relativeMap_hom, yonedaEquiv_relativeMap_hom]
  exact relativeSpaceIso_hom_app_relativeSection F e₁ e₂ θ hθ Z x hx α₁ hα₁ α₂ hα₂ hα

end AlgebraicGeometry.Stack

end
