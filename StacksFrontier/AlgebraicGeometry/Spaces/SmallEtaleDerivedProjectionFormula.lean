module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# The projection formula map of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  For `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)` there is a
canonical map

`Rf_*(E) ⊗ᴸ_{𝒪_Y} K ⟶ Rf_*(E ⊗ᴸ_{𝒪_X} Lf^*K)`,

adjoint to `Lf^*(Rf_*E ⊗ᴸ K) = Lf^*Rf_*E ⊗ᴸ Lf^*K ⟶ E ⊗ᴸ Lf^*K` (Stacks 07A4 followed by the
counit of `Lf^* ⊣ Rf_*` in the first factor).  Stacks 08IN asserts that it is an isomorphism
when `f` is quasi-compact and quasi-separated and `E`, `K` have quasi-coherent cohomology.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleProjectionFormulaMap`: the map, the instance of
  `CategoryTheory.adjunctionTensorMap` at the derived adjunction of `f` and Stacks 07A4.  Its
  naturality and defining equation are `CategoryTheory.adjunctionTensorMap_natural` and
  `CategoryTheory.map_adjunctionTensorMap_comp_counit`.

## References

* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The projection formula map** `Rf_*(E) ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` of a morphism of algebraic
spaces: the adjoint of Stacks 07A4 followed by the counit of `Lf^* ⊣ Rf_*` in the first factor. -/
def smallEtaleProjectionFormulaMap (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    ((smallEtaleDerivedTensor B S hS Y).obj
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj E)).obj K ⟶
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj K)) :=
  adjunctionTensorMap (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom E K

end AlgebraicGeometry.Space

end
