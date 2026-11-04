module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallySmallAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsModel

/-!
# Shrinking the hom-sets of a category fibred in groupoids

A category fibred in groupoids over the big fppf site whose underlying category is locally small at
the universe of the site is equivalent over the site to the same category with its hom-sets shrunk
to that universe (`StacksRepresentableCFG.shrinkHomsEquivalenceOver`). This file packages the
shrunk category as a category fibred in groupoids, together with the induced 1-morphisms and the
inverse equivalence.

## Main definitions

* `AlgebraicGeometry.Stack.shrinkHomsCFG`: a locally small category fibred in groupoids over the
  big fppf site, with its hom-sets shrunk to the universe of the site.
* `AlgebraicGeometry.Stack.shrinkHomsHom`: the 1-morphism induced by a 1-morphism on the categories
  with shrunk hom-sets.
* `AlgebraicGeometry.Stack.shrinkHomsInverse`: the inverse of the shrinking equivalence, as a based
  functor; its underlying functor is an equivalence.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u v

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A locally small category fibred in groupoids over the big fppf site, with its hom-sets
shrunk to the universe of the site. -/
def shrinkHomsCFG (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS))
    [LocallySmall.{u} 𝒳.val.obj] :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor
      (ShrinkHoms.inverse 𝒳.val.obj ⋙ 𝒳.val.p))
    (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
      (StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} 𝒳.val.p).symm
      𝒳.isFiberedInGroupoids)

/-- The 1-morphism induced on the categories with shrunk hom-sets. -/
def shrinkHomsHom {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] [LocallySmall.{u} 𝒴.val.obj] (j : 𝒳 ⟶ 𝒴) :
    shrinkHomsCFG B S hS 𝒳 ⟶ shrinkHomsCFG B S hS 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := ShrinkHoms.inverse 𝒳.val.obj ⋙ j.hom.toFunctor ⋙
        ShrinkHoms.functor 𝒴.val.obj
      w := by
        change ShrinkHoms.inverse 𝒳.val.obj ⋙ j.hom.toFunctor ⋙
          (ShrinkHoms.functor 𝒴.val.obj ⋙ ShrinkHoms.inverse 𝒴.val.obj ⋙ 𝒴.val.p) =
            ShrinkHoms.inverse 𝒳.val.obj ⋙ 𝒳.val.p
        have h : ShrinkHoms.functor 𝒴.val.obj ⋙ ShrinkHoms.inverse 𝒴.val.obj ⋙ 𝒴.val.p =
            𝒴.val.p := (StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} 𝒴.val.p).hom.w
        rw [h, j.hom.w] }

/-- The inverse of the shrinking equivalence, as a based functor. -/
def shrinkHomsInverse (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS))
    [LocallySmall.{u} 𝒳.val.obj] : (shrinkHomsCFG B S hS 𝒳).val ⥤ᵇ 𝒳.val where
  toFunctor := ShrinkHoms.inverse 𝒳.val.obj
  w := rfl

/-- The underlying functor of `shrinkHomsInverse` is an equivalence of categories. -/
instance (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS))
    [LocallySmall.{u} 𝒳.val.obj] : (shrinkHomsInverse B S hS 𝒳).toFunctor.IsEquivalence :=
  inferInstanceAs (ShrinkHoms.inverse 𝒳.val.obj).IsEquivalence

/- Stacks 05UM for categories fibred in groupoids whose morphisms lie in an arbitrary universe is
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse`
of `StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse`. -/

end AlgebraicGeometry.Stack

end
