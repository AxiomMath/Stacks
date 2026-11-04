module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme

/-!
# Equivalences of algebraic stacks are gerbes

A 1-morphism of algebraic stacks over `S` whose underlying functor is an equivalence of
categories makes its source a gerbe over its target, and the 1-morphism of algebraic stacks
attached to an isomorphism of algebraic spaces is such a 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_isEquivalence`: a 1-morphism whose
  underlying functor is an equivalence is a gerbe.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_homFunctor_algebraicSpaceStackMap`:
  the 1-morphism attached to an isomorphism of algebraic spaces has underlying functor an
  equivalence.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_algebraicSpaceStackMap`: hence it is a
  gerbe.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An equivalence of algebraic stacks is a gerbe.** If the underlying functor of
`f : 𝒳 ⟶ 𝒴` is an equivalence of categories, it is an equivalence over the big fppf site
(Stacks 003Z), and an equivalence over the site makes its source a gerbe over its target. -/
theorem isGerbeOver_of_isEquivalence {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f.hom).IsEquivalence) : IsGerbeOver B S hS f := by
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_isEquivalenceOver_of_isEquivalence
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids _
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) hf
  exact CategoryTheory.isGerbeOver_of_isEquivalenceOver _
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) e 𝒴.val.isFiberedInGroupoids

/-- **The 1-morphism of algebraic stacks attached to an isomorphism of algebraic spaces has
underlying functor an equivalence.** The 1-morphisms attached to `e.hom` and `e.inv` compose,
in either order, to the 1-morphism attached to an identity (`algebraicSpaceStackMap_comp`), which
is 2-isomorphic to the identity (`AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_id`). -/
theorem isEquivalence_homFunctor_algebraicSpaceStackMap {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (e : T ≅ G) :
    (CatFiberedInGroupoids.homFunctor
      (algebraicSpaceStackMap.{u, w} B S hS hT hG e.hom).hom).IsEquivalence := by
  obtain ⟨κT⟩ := nonempty_twoIso_associatedMap_id B S hS T
  obtain ⟨κG⟩ := nonempty_twoIso_associatedMap_id B S hS G
  have h₁ : algebraicSpaceStackMap.{u, w} B S hS hT hG e.hom ≫
      algebraicSpaceStackMap.{u, w} B S hS hG hT e.inv =
      algebraicSpaceStackMap.{u, w} B S hS hT hT (𝟙 T) := by
    rw [← algebraicSpaceStackMap_comp, e.hom_inv_id]
  have h₂ : algebraicSpaceStackMap.{u, w} B S hS hG hT e.inv ≫
      algebraicSpaceStackMap.{u, w} B S hS hT hG e.hom =
      algebraicSpaceStackMap.{u, w} B S hS hG hG (𝟙 G) := by
    rw [← algebraicSpaceStackMap_comp, e.inv_hom_id]
  let iT : algebraicSpaceStackMap.{u, w} B S hS hT hT (𝟙 T) ≅ 𝟙 _ :=
    Bicategory.InducedBicategory.isoMk κT
  let iG : algebraicSpaceStackMap.{u, w} B S hS hG hG (𝟙 G) ≅ 𝟙 _ :=
    Bicategory.InducedBicategory.isoMk κG
  exact (CategoryTheory.Equivalence.mk
    (CatFiberedInGroupoids.homFunctor (algebraicSpaceStackMap.{u, w} B S hS hT hG e.hom).hom)
    (CatFiberedInGroupoids.homFunctor (algebraicSpaceStackMap.{u, w} B S hS hG hT e.inv).hom)
    (underlyingIso B S hS (eqToIso h₁ ≪≫ iT)).symm
    (underlyingIso B S hS (eqToIso h₂ ≪≫ iG))).isEquivalence_functor

/-- **The 1-morphism of algebraic stacks attached to an isomorphism of algebraic spaces is a
gerbe.** -/
theorem isGerbeOver_algebraicSpaceStackMap {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (e : T ≅ G) :
    IsGerbeOver B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG e.hom) :=
  isGerbeOver_of_isEquivalence B S hS _
    (isEquivalence_homFunctor_algebraicSpaceStackMap.{u, w} B S hS hT hG e)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
