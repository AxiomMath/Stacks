module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ModelExtensionClass

/-!
# Every class on the model of the small étale site is the class of an extension

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `ℳ` an `𝒪_X`-module. The class of an
extension of `f⁻¹𝒪_Y`-algebras of `𝒪_X` by `ℳ` is taken on the `Type u`-presented model of the
small étale site of `X` (`AlgebraicGeometry.Space.modelExtClass`). Every class in
`Ext¹(NL_{X/Y}, ℳ)` on the model is the class of an extension on the small étale site itself:
the model class of [Stacks Project, Tag 0GQ5] is surjective on the model, and extensions restrict
to the model by an equivalence of categories.

## Main results

* `AlgebraicGeometry.Space.exists_modelExtClass_eq`: every class is the class of an extension.
* `AlgebraicGeometry.Space.modelExtClass_eq_of_iso`: isomorphic extensions have the same class.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.AlgebraExtension

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  {f : X ⟶ Y}

/-- **Isomorphic extensions have the same class on the model.** -/
theorem modelExtClass_eq_of_iso
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    {P Q : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M}
    (e : P ≅ Q) : modelExtClass B S hS P = modelExtClass B S hS Q :=
  extClass_eq_of_iso (J := smallEtaleModelTopology B S hS X.1)
    ((siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
      (inverseImageBaseMap B S hS f) M).mapIso e)

/-- **Every class on the model is the class of an extension** on the small étale site of `X`
(Stacks 0GQ5 on the model, and the equivalence of extensions on the site with extensions on the
model). -/
theorem exists_modelExtClass_eq
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (ξ : ExtOne (J := smallEtaleModelTopology B S hS X.1) (modelBaseMap B S hS f)
      (modelModule B S hS M)) :
    ∃ P : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M,
      modelExtClass B S hS P = ξ := by
  have := isEquivalence_siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
    (inverseImageBaseMap B S hS f) M
  obtain ⟨Q, hQ⟩ := exists_extClass_eq (J := smallEtaleModelTopology B S hS X.1) ξ
  let F := siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
    (inverseImageBaseMap B S hS f) M
  exact ⟨F.objPreimage Q,
    (extClass_eq_of_iso (J := smallEtaleModelTopology B S hS X.1) (F.objObjPreimageIso Q)).trans hQ⟩

end AlgebraicGeometry.Space

end
