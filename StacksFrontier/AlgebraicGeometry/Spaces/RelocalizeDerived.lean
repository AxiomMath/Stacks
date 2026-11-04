module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobalUniverses
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# Derived categories of modules on an algebraic space viewed over a larger base

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. The equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})` of
`AlgebraicGeometry.Space.relocalizeModulesEquivalence` is exact, so it induces an equivalence of
derived categories `D(𝒪_X) ≌ D(𝒪_{Λ X})`, compatible with the localization functors and with the
complexes concentrated in one degree.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeDerivedFunctor`: the functor `D(𝒪_X) ⥤ D(𝒪_{Λ X})`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_relocalizeDerivedFunctor`: it is an equivalence.
* `AlgebraicGeometry.Space.relocalizeDerivedFunctorFactors`,
  `AlgebraicGeometry.Space.relocalizeDerivedFunctorSingleIso`: compatibility with `Q` and with
  `single n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- The functor `Mod(𝒪_X) ⥤ Mod(𝒪_{Λ X})` of the relocalization equivalence is additive. -/
instance relocalizeModulesEquivalence_functor_additive :
    (relocalizeModulesEquivalence B hT hS g X hX).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `Mod(𝒪_{Λ X}) ⥤ Mod(𝒪_X)` inverse to the relocalization equivalence is additive. -/
instance relocalizeModulesEquivalence_inverse_additive :
    (relocalizeModulesEquivalence B hT hS g X hX).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived functor of the relocalization of modules**, `D(𝒪_X) ⥤ D(𝒪_{Λ X})`. -/
abbrev relocalizeDerivedFunctor :
    DerivedCategory (Modules.{u, u} B T hT X hX) ⥤
      DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX)) :=
  (relocalizeModulesEquivalence B hT hS g X hX).functor.mapDerivedCategory

/-- **The relocalization of derived categories is an equivalence.** -/
instance isEquivalence_relocalizeDerivedFunctor :
    (relocalizeDerivedFunctor B hT hS g X hX).IsEquivalence :=
  Stacks.SheafOfModules.mapDerivedCategory_isEquivalence_general
    (relocalizeModulesEquivalence B hT hS g X hX)

/-- The relocalization of derived categories, as an equivalence. -/
abbrev relocalizeDerivedEquivalence :
    DerivedCategory (Modules.{u, u} B T hT X hX) ≌
      DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX)) :=
  (relocalizeDerivedFunctor B hT hS g X hX).asEquivalence

/-- The relocalization of derived categories on the image of a complex is the image of the
relocalized complex. -/
abbrev relocalizeDerivedFunctorFactors :
    DerivedCategory.Q ⋙ relocalizeDerivedFunctor B hT hS g X hX ≅
      (relocalizeModulesEquivalence B hT hS g X hX).functor.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (relocalizeModulesEquivalence B hT hS g X hX).functor.mapDerivedCategoryFactors

/-- The relocalization of derived categories on a module placed in degree `n` is the relocalized
module placed in degree `n`. -/
abbrev relocalizeDerivedFunctorSingleIso (n : ℤ) :
    DerivedCategory.singleFunctor _ n ⋙ relocalizeDerivedFunctor B hT hS g X hX ≅
      (relocalizeModulesEquivalence B hT hS g X hX).functor ⋙ DerivedCategory.singleFunctor _ n :=
  (relocalizeModulesEquivalence B hT hS g X hX).functor.mapDerivedCategorySingleFunctor n

end AlgebraicGeometry.Space

end
