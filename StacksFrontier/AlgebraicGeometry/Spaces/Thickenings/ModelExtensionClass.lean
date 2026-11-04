module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutEquivalence
public import StacksFrontier.Deformation.AlgebraExtension.ExtClass

/-!
# The class of an extension of algebras on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `ℳ` an `𝒪_X`-module. An extension
`0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_Y`-algebras on the small étale site of `X` has a class in
`Ext¹(NL_{X/Y}, ℳ)` ([Stacks Project, Tag 0GQ5]). The small étale site has its objects in
`Type (u + 1)`, so the class is taken on the `Type u`-presented model of the site
(`AlgebraicGeometry.Space.smallEtaleModelRingedTopos`), to which extensions restrict by an
equivalence of categories (`Deformation.AlgebraExtension.isEquivalence_siteRestriction`).

The class is natural along morphisms of extensions, and two extensions with the same class are
isomorphic.

## Main definitions

* `AlgebraicGeometry.Space.modelExtClass`: the class in `Ext¹(NL_{X/Y}, ℳ)`, on the model.

## Main results

* `AlgebraicGeometry.Space.modelExtClass_mapAlong`: naturality along morphisms of extensions.
* `AlgebraicGeometry.Space.nonempty_iso_of_modelExtClass_eq`: extensions with the same class are
  isomorphic.

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
  (f : X ⟶ Y)

/-- The restriction to the model of the small étale site of `X` of an `𝒪_X`-module. -/
abbrev modelModule
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))) :=
  (moduleRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse
    (structureSheaf B S hS X.1 X.2)).obj M

variable {f}

/-- **The class of an extension of `f⁻¹𝒪_Y`-algebras in `Ext¹(NL_{X/Y}, ℳ)`**, Stacks 0GQ5,
taken on the model of the small étale site of `X`. -/
def modelExtClass
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (P : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M) :
    ExtOne (J := smallEtaleModelTopology B S hS X.1) (modelBaseMap B S hS f)
      (modelModule B S hS M) :=
  extClass (J := smallEtaleModelTopology B S hS X.1)
    ((siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
    (inverseImageBaseMap B S hS f) M).obj P)

/-- **Naturality of the class.** A morphism of extensions along `φ : ℳ ⟶ 𝒩` carries the class
of the source to the class of the target, pushed along `φ`. -/
theorem modelExtClass_mapAlong
    {M N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    {φ : M ⟶ N}
    {P : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M}
    {Q : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) N}
    (g : MapAlong (J := SmallEtale.topology B S hS X.1) φ P Q) :
    modelExtClass B S hS Q =
      extOneMap (J := smallEtaleModelTopology B S hS X.1)
        ((moduleRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse
        (structureSheaf B S hS X.1 X.2)).map φ) (modelExtClass B S hS P) :=
  extClass_mapAlong (J := smallEtaleModelTopology B S hS X.1)
    (MapAlong.restrictVia (K := smallEtaleModelTopology B S hS X.1)
      (G := (modelEquiv B S hS X).inverse)
      (idRingComparison (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
        (inverseImageBaseMap B S hS f))
      (idModuleComparison _ _ _ M) (idModuleComparison _ _ _ N) (fun _ _ => rfl) g)

/-- **Extensions with the same class are isomorphic.** -/
theorem nonempty_iso_of_modelExtClass_eq
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    {P Q : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M}
    (h : modelExtClass B S hS P = modelExtClass B S hS Q) : Nonempty (P ≅ Q) := by
  have := isEquivalence_siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
    (inverseImageBaseMap B S hS f) M
  obtain ⟨e⟩ := nonempty_iso_of_extClass_eq (J := smallEtaleModelTopology B S hS X.1) h
  exact ⟨((siteRestriction (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X)
    (inverseImageBaseMap B S hS f) M).asEquivalence.fullyFaithfulFunctor).preimageIso e⟩

end AlgebraicGeometry.Space

end
