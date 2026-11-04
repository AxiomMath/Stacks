module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack

/-!
# Two-cells between scheme-valued points

A 1-morphism into the category fibred in groupoids represented by an object `V` of the big fppf
site of `S` is a scheme-valued point, and a 2-morphism between two such is a natural
transformation whose components are arrows of the slice over `V` lying over identities. Such an
arrow is unique, so two parallel 2-morphisms into a represented category fibred in groupoids are
equal. This file records that fact and the two ways of producing 2-morphisms between
1-morphisms of represented categories fibred in groupoids from equalities of the underlying
morphisms of the site.

## Main results

* `AlgebraicGeometry.Stack.subsingleton_hom₂_schemeFibredCategory`: the 2-morphisms between two
  1-morphisms into a represented category fibred in groupoids form a subsingleton.
* `AlgebraicGeometry.Stack.hom₂OfSchemeMapEq`: a 2-morphism between two 1-morphisms of
  represented categories fibred in groupoids with the same underlying morphism of the site.
* `AlgebraicGeometry.Stack.schemeMapOfFunctor_comp`: the morphism of the site underlying a
  composite is the composite of the underlying morphisms.
* `AlgebraicGeometry.Stack.schemeMapOfFunctor_eq_of_hom₂`: a 2-morphism does not change the
  underlying morphism of the site.

## Implementation notes

The subsingleton statement is what lets the compatibility condition of a dotted arrow
(**Stacks 0H18**) be discharged for free whenever the target of the square is represented by an
object of the site: both sides are 2-morphisms into a represented category fibred in groupoids.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two-cells into a represented category fibred in groupoids are unique.** Every component of
a 2-morphism into the category fibred in groupoids represented by `V` is an arrow of the slice
over `V` lying over an identity of the base, and such an arrow is determined by its endpoints. -/
theorem subsingleton_hom₂_schemeFibredCategory
    {𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {V : BigFppfOver B S hS} (F G : 𝒞 ⟶ schemeFibredCategory B S hS V) :
    Subsingleton (F ⟶ G) := by
  refine ⟨fun η θ => CatFiberedInGroupoids.hom₂_ext_app fun A => ?_⟩
  have _ : (Over.forget V).IsHomLift (𝟙 (𝒞.val.p.obj A)) (η.hom.toNatTrans.app A) :=
    η.hom.isHomLift' A
  have _ : (Over.forget V).IsHomLift (𝟙 (𝒞.val.p.obj A)) (θ.hom.toNatTrans.app A) :=
    θ.hom.isHomLift' A
  have e₁ := IsHomLift.fac' (Over.forget V) (𝟙 (𝒞.val.p.obj A)) (η.hom.toNatTrans.app A)
  have e₂ := IsHomLift.fac' (Over.forget V) (𝟙 (𝒞.val.p.obj A)) (θ.hom.toNatTrans.app A)
  exact Over.OverMorphism.ext (e₁.trans e₂.symm)

/-- **A 2-morphism between two 1-morphisms of represented categories fibred in groupoids with the
same underlying morphism of the site.** -/
def hom₂OfSchemeMapEq {W U : BigFppfOver B S hS}
    (F G : schemeFibredCategory B S hS W ⟶ schemeFibredCategory B S hS U)
    (h : schemeMapOfFunctor B S hS F.hom = schemeMapOfFunctor B S hS G.hom) : F ⟶ G :=
  Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS F.hom G.hom h)

/-- A 2-morphism does not change the morphism of the site underlying a 1-morphism of represented
categories fibred in groupoids. -/
theorem schemeMapOfFunctor_eq_of_hom₂ {W U : BigFppfOver B S hS}
    {F G : schemeFibredCategory B S hS W ⟶ schemeFibredCategory B S hS U} (η : F ⟶ G) :
    schemeMapOfFunctor B S hS F.hom = schemeMapOfFunctor B S hS G.hom :=
  schemeMapOfFunctor_eq_of_basedNatTrans B S hS η.hom

/-- The 1-morphism of represented categories fibred in groupoids induced by a morphism of the
site has that morphism as underlying morphism of the site. -/
theorem schemeMapOfFunctor_schemeFibredCategoryMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeMapOfFunctor B S hS (schemeFibredCategoryMap B S hS g).hom = g :=
  schemeMapOfFunctor_overMapBased B S hS g

/-- A 1-morphism of represented categories fibred in groupoids whose underlying functor is
`CategoryTheory.Over.map r` has `r` as underlying morphism of the site. -/
theorem schemeMapOfFunctor_eq_of_hom_toFunctor_eq {U V : BigFppfOver B S hS} (r : U ⟶ V)
    (j : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V)
    (hj : j.hom.toFunctor = Over.map r) : schemeMapOfFunctor B S hS j.hom = r := by
  have : j = schemeFibredCategoryMap B S hS r :=
    Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hj)
  subst this
  exact schemeMapOfFunctor_schemeFibredCategoryMap B S hS r

/-- **The morphism of the site underlying a composite** of 1-morphisms of represented categories
fibred in groupoids is the composite of the underlying morphisms. The first factor is
2-isomorphic to the 1-morphism induced by its underlying morphism, and precomposition with an
induced 1-morphism is computed by `AlgebraicGeometry.Stack.schemeMapOfFunctor_comp_overMapBased`.
-/
theorem schemeMapOfFunctor_comp {Q W U : BigFppfOver B S hS}
    (F : schemeFibredCategory B S hS Q ⟶ schemeFibredCategory B S hS W)
    (G : schemeFibredCategory B S hS W ⟶ schemeFibredCategory B S hS U) :
    schemeMapOfFunctor B S hS (F ≫ G).hom =
      schemeMapOfFunctor B S hS F.hom ≫ schemeMapOfFunctor B S hS G.hom := by
  let η : F ⟶ schemeFibredCategoryMap B S hS (schemeMapOfFunctor B S hS F.hom) :=
    hom₂OfSchemeMapEq B S hS _ _
      (schemeMapOfFunctor_schemeFibredCategoryMap B S hS _).symm
  exact (schemeMapOfFunctor_eq_of_hom₂ B S hS (η ▷ G)).trans
    (schemeMapOfFunctor_comp_overMapBased B S hS (schemeMapOfFunctor B S hS F.hom) G.hom)

end AlgebraicGeometry.Stack

end
