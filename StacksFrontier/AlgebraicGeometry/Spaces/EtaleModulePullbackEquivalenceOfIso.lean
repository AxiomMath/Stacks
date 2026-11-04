module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange

/-!
# Pullback of modules along an isomorphism of algebraic spaces

An isomorphism `e : X ≅ Y` of algebraic spaces over `S` is étale in both directions, so the
étale pullbacks of modules along `e.hom` and `e.inv` are defined, and by the unit and
composition laws of étale pullback they are quasi-inverse to each other. This file records the
resulting equivalence `Mod(𝒪_Y) ≌ Mod(𝒪_X)` and the equivalence `D(𝒪_Y) ≌ D(𝒪_X)` it induces
on unbounded derived categories.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePullbackEquivalenceOfIso`: the equivalence
  `Mod(𝒪_Y) ≌ Mod(𝒪_X)` given by étale pullback along `e.hom`, with quasi-inverse the étale
  pullback along `e.inv`.
* `AlgebraicGeometry.Space.derivedEtaleModulePullbackEquivalenceOfIso`: the induced equivalence
  `D(𝒪_Y) ≌ D(𝒪_X)`, whose functor is the derived functor of the étale pullback along `e.hom`,
  for any models of the two derived categories.

## Main results

* `AlgebraicGeometry.Space.isEtale_hom_of_isIso`: an isomorphism of algebraic spaces is étale.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w₁ w₂ u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of algebraic spaces over `S` is étale. -/
theorem isEtale_hom_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f] :
    IsEtale B S hS f.hom :=
  have : IsIso f.hom := Functor.map_isIso (ObjectProperty.ι _) f
  isEtale_of_isIso B S hS f.hom

variable {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)

/-- **Étale pullback along an isomorphism of algebraic spaces is an equivalence.** For an
isomorphism `e : X ≅ Y`, the étale pullback of `𝒪_Y`-modules along `e.hom` is an equivalence
`Mod(𝒪_Y) ≌ Mod(𝒪_X)`, with quasi-inverse the étale pullback along `e.inv`; the unit and the
counit are the composition and unit laws of étale pullback at `e.hom ≫ e.inv = 𝟙` and
`e.inv ≫ e.hom = 𝟙`. -/
def etaleModulePullbackEquivalenceOfIso :
    Modules.{u, m} B S hS Y.1 Y.2 ≌ Modules.{u, m} B S hS X.1 X.2 :=
  CategoryTheory.Equivalence.mk
    (etaleModulePullback B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom))
    (etaleModulePullback B S hS e.inv (isEtale_hom_of_isIso B S hS e.inv))
    ((etaleModulePullbackIdIso B S hS (isEtale_hom_of_isIso B S hS (𝟙 Y))).symm ≪≫
      eqToIso (etaleModulePullback_congr B S hS _ _ e.inv_hom_id.symm) ≪≫
      (etaleModulePullbackCompIso B S hS e.inv e.hom _ _
        (isEtale_hom_of_isIso B S hS (e.inv ≫ e.hom))).symm)
    (etaleModulePullbackCompIso B S hS e.hom e.inv _ _
        (isEtale_hom_of_isIso B S hS (e.hom ≫ e.inv)) ≪≫
      eqToIso (etaleModulePullback_congr B S hS _ _ e.hom_inv_id) ≪≫
      etaleModulePullbackIdIso B S hS (isEtale_hom_of_isIso B S hS (𝟙 X)))

/-- The functor of `etaleModulePullbackEquivalenceOfIso` is the étale pullback along `e.hom`. -/
@[simp]
lemma etaleModulePullbackEquivalenceOfIso_functor :
    (etaleModulePullbackEquivalenceOfIso.{u, m} B S hS e).functor =
      etaleModulePullback B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom) :=
  rfl

/-- The inverse of `etaleModulePullbackEquivalenceOfIso` is the étale pullback along `e.inv`. -/
@[simp]
lemma etaleModulePullbackEquivalenceOfIso_inverse :
    (etaleModulePullbackEquivalenceOfIso.{u, m} B S hS e).inverse =
      etaleModulePullback B S hS e.inv (isEtale_hom_of_isIso B S hS e.inv) :=
  rfl

/-- The functor of `etaleModulePullbackEquivalenceOfIso` is additive. -/
instance additive_etaleModulePullbackEquivalenceOfIso_functor :
    (etaleModulePullbackEquivalenceOfIso.{u, m} B S hS e).functor.Additive :=
  etaleModulePullback_additive B S hS e.hom _

variable [HasDerivedCategory.{w₁} (Modules.{u, u} B S hS Y.1 Y.2)]
  [HasDerivedCategory.{w₂} (Modules.{u, u} B S hS X.1 X.2)]

/-- **Étale pullback along an isomorphism of algebraic spaces, on derived categories.** For an
isomorphism `e : X ≅ Y`, the derived functor of étale pullback along `e.hom` is an equivalence
`D(𝒪_Y) ≌ D(𝒪_X)`, with quasi-inverse the derived functor of étale pullback along `e.inv`; the
two derived categories may be any models. -/
def derivedEtaleModulePullbackEquivalenceOfIso :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ≌
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (etaleModulePullbackEquivalenceOfIso B S hS e)

/-- The functor of `derivedEtaleModulePullbackEquivalenceOfIso` is the derived functor of the
functor of `etaleModulePullbackEquivalenceOfIso`. -/
@[simp]
lemma derivedEtaleModulePullbackEquivalenceOfIso_functor :
    (derivedEtaleModulePullbackEquivalenceOfIso B S hS e).functor =
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS e).functor.mapDerivedCategory :=
  rfl

/-- The inverse of `derivedEtaleModulePullbackEquivalenceOfIso` is the derived functor of the
inverse of `etaleModulePullbackEquivalenceOfIso`. -/
@[simp]
lemma derivedEtaleModulePullbackEquivalenceOfIso_inverse :
    (derivedEtaleModulePullbackEquivalenceOfIso B S hS e).inverse =
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS e).inverse.mapDerivedCategory :=
  rfl

end AlgebraicGeometry.Space

end
