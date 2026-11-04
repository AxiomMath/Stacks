module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data for a sub-pseudofunctor cut out by a property of objects

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and let `P : F.ObjectProperty` be a
property of objects of the categories `F.obj Z` which is preserved by the functors `F.map`
(`CategoryTheory.Pseudofunctor.ObjectProperty.IsClosedUnderMapObj`).  Mathlib's
`CategoryTheory.Pseudofunctor.ObjectProperty.fullsubcategory` is then a pseudofunctor again,
sending `Z` to the full subcategory of `F.obj Z` on the objects satisfying `P`.

This file compares the two categories of descent data that a family of morphisms
`f i : X i ⟶ S` has in this situation:

* `P.fullsubcategory.DescentData f`, the descent data of the sub-pseudofunctor, and
* the full subcategory of `F.DescentData f` on the descent data whose components satisfy `P`.

They are **isomorphic**, not merely equivalent: the two comparison functors are mutually
inverse on the nose.

## Main definitions

* `Stacks.Descent.subDescentDataProp` is the property of a descent datum for `F` that all its
  components satisfy `P`.
* `Stacks.Descent.subDescentDataFunctor` and `Stacks.Descent.subDescentDataInverse` are the two
  comparison functors, and `Stacks.Descent.subDescentDataEquivalence` bundles them.

## Main results

* `Stacks.Descent.subDescentDataFunctor_comp_inverse` and
  `Stacks.Descent.subDescentDataInverse_comp_functor`: the comparison functors compose to the
  identity functors, so the comparison is an isomorphism of categories.
* `Stacks.Descent.toDescentData_comp_subDescentDataFunctor`: the comparison carries the
  canonical descent functor of the sub-pseudofunctor to the lift of
  `ι ⋙ F.toDescentData f` along the inclusion of the full subcategory of descent data.

## Implementation notes

Every proof here is `rfl`, `congrArg` or `CategoryTheory.ObjectProperty.hom_ext`.  That is not an
accident: a component of a descent datum for `P.fullsubcategory` *is* a component of a descent
datum for `F` together with a proof, the transition morphisms of `P.fullsubcategory` are those of
`F` wrapped in `CategoryTheory.ObjectProperty.homMk`, and
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` for `P.fullsubcategory` is
definitionally `pullHom` for `F`, because `mapId` and `mapComp` of the sub-pseudofunctor are
defined by applying `homMk` to those of `F`.

`toDescentData_comp_subDescentDataFunctor` is stated and proved **at this generality on
purpose**, and must not be re-proved by `rfl` at a concrete pseudofunctor.  At a concrete `F`
whose categories `F.obj Z` carry their own `Category` instance — `AlgebraicGeometry.Scheme.Modules`
is the motivating case, where the instance is only definitionally that of
`SheafOfModules` — the same `rfl` sends both the elaborator and the kernel past their default
heartbeat budget, since checking it forces the pullback–pushforward adjunction open.  Here no
such instance is in play, and instantiating an already-proved equation is free.

No Stacks tag is claimed: this is the bookkeeping that lets a statement about a
sub-pseudofunctor's descent data be read as a statement about descent data with constrained
components, and carries no mathematical content of its own.
-/

@[expose] public section

open CategoryTheory Opposite Bicategory CategoryTheory.Pseudofunctor

universe t v' v u' u

namespace Stacks.Descent

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The property of a descent datum for `F` relative to `f` that every one of its components
satisfies `P`. -/
def subDescentDataProp : ObjectProperty (F.DescentData f) :=
  fun D ↦ ∀ i, P.prop _ (D.obj i)

/-- A descent datum for the sub-pseudofunctor `P.fullsubcategory` is a descent datum for `F`
whose components satisfy `P`: this is the comparison in that direction, obtained by forgetting
the proofs of `P` from the components and from the transition morphisms. -/
def subDescentDataFunctor :
    P.fullsubcategory.DescentData f ⥤ (subDescentDataProp P f).FullSubcategory where
  obj D :=
    { obj :=
        { obj i := (D.obj i).obj
          hom _ q _ _ f₁ f₂ h₁ h₂ := (D.hom q f₁ f₂ h₁ h₂).hom
          pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
            congrArg (fun ψ ↦ ψ.hom)
              (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
          hom_self _ q _ g hg := congrArg (fun ψ ↦ ψ.hom) (D.hom_self q g hg)
          hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
            congrArg (fun ψ ↦ ψ.hom) (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
      property i := (D.obj i).property }
  map {_ _} φ :=
    ObjectProperty.homMk
      { hom i := (φ.hom i).hom
        comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
          congrArg (fun ψ ↦ ψ.hom) (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- The inverse of `Stacks.Descent.subDescentDataFunctor`: a descent datum for `F` whose
components satisfy `P` is a descent datum for the sub-pseudofunctor `P.fullsubcategory`. -/
def subDescentDataInverse :
    (subDescentDataProp P f).FullSubcategory ⥤ P.fullsubcategory.DescentData f where
  obj D :=
    { obj i := ⟨D.obj.obj i, D.property i⟩
      hom _ q _ _ f₁ f₂ h₁ h₂ := ObjectProperty.homMk (D.obj.hom q f₁ f₂ h₁ h₂)
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
        ObjectProperty.hom_ext _
          (D.obj.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
      hom_self _ q _ g hg := ObjectProperty.hom_ext _ (D.obj.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        ObjectProperty.hom_ext _ (D.obj.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {_ _} φ :=
    { hom i := ObjectProperty.homMk (φ.hom.hom i)
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := ObjectProperty.hom_ext _ (φ.hom.comm q f₁ f₂ hf₁ hf₂) }

/-- Forgetting the proofs of `P` and putting them back is the identity. -/
theorem subDescentDataFunctor_comp_inverse :
    subDescentDataFunctor P f ⋙ subDescentDataInverse P f = 𝟭 _ := rfl

/-- Putting the proofs of `P` in and forgetting them again is the identity. -/
theorem subDescentDataInverse_comp_functor :
    subDescentDataInverse P f ⋙ subDescentDataFunctor P f = 𝟭 _ := rfl

/-- **The descent data of a sub-pseudofunctor are the descent data with components in the
subcategory.**  The comparison is an isomorphism of categories: its unit and counit are the
identity, by `Stacks.Descent.subDescentDataFunctor_comp_inverse` and
`Stacks.Descent.subDescentDataInverse_comp_functor`. -/
def subDescentDataEquivalence :
    P.fullsubcategory.DescentData f ≌ (subDescentDataProp P f).FullSubcategory where
  functor := subDescentDataFunctor P f
  inverse := subDescentDataInverse P f
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by ext i; exact Category.comp_id _

/-- The comparison functor `Stacks.Descent.subDescentDataFunctor` is an equivalence. -/
instance : (subDescentDataFunctor P f).IsEquivalence :=
  (subDescentDataEquivalence P f).isEquivalence_functor

/-- **The comparison carries the canonical descent functor to the canonical descent functor.**
Composing the canonical descent functor of the sub-pseudofunctor with the comparison gives the
lift of `ι ⋙ F.toDescentData f` to the descent data with components satisfying `P`.

Instantiate this equation rather than re-proving it by `rfl`: see the implementation notes. -/
theorem toDescentData_comp_subDescentDataFunctor :
    P.fullsubcategory.toDescentData f ⋙ subDescentDataFunctor P f =
      ObjectProperty.lift (subDescentDataProp P f)
        ((P.prop (.mk (op S))).ι ⋙ F.toDescentData f)
        (fun M _ ↦ P.map_obj M.2 _) := rfl

end Stacks.Descent

end
