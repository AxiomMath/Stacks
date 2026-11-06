module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedExtendScalarsContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPullbackContraction

/-!
# The degreewise affine base change isomorphisms, with their instance arguments written out

The degreewise affine base change isomorphisms
`AlgebraicGeometry.Space.representedAffineComplexPullbackIso` and
`AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso` are built from
`CategoryTheory.Functor.mapHomologicalComplexCompIso`. This file states each as an equation with
that construction in which every additivity instance argument is given explicitly.

## Main results

* `AlgebraicGeometry.Space.representedAffineComplexPullbackIso_eq`: the degreewise pullback
  isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~` of complexes, with its two factors and all of their
  instance arguments written out.
* `AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso_eq`: the degreewise
  contraction `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −` of complexes, likewise.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section OneMorphism

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- **The degreewise affine base change isomorphism, with every instance argument written out.**
`AlgebraicGeometry.Space.representedAffineComplexPullbackIso` is the comparison of the induced
functors for the underived isomorphism
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`, followed by the inverse of the
comparison at an identity, which is the factor reconciling `(R' ⊗_R − ⋙ Φ_{R'})^•` with
`(R' ⊗_R −)^• ⋙ Φ_{R'}^•`. -/
theorem representedAffineComplexPullbackIso_eq :
    representedAffineComplexPullbackIso B S hS g =
      @Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
          (representedAffineAssociatedPullbackIso B S hS g)
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (additive_representedAffineAssociated B S hS U))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (additive_extendScalars_comp_representedAffineAssociated B S hS g))
          (ComplexShape.up ℤ) ≪≫
        (@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _
            (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
            (representedAffineAssociated B S hS U') _ (Iso.refl _)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (ModuleCat.extendRestrictScalarsAdj
              (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (additive_representedAffineAssociated B S hS U'))
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (additive_extendScalars_comp_representedAffineAssociated B S hS g))
            (ComplexShape.up ℤ)).symm :=
  rfl

end OneMorphism

variable {U'' U' U : BigFppfOver B S hS} (h : U'' ⟶ U') (g : U' ⟶ U)

/-- **The degreewise contraction of the extensions of scalars, with every instance argument
written out.** `AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso` is the
comparison of the induced functors for the underived contraction
`AlgebraicGeometry.Space.representedAffineExtendScalarsCompIso`; its three additivity
arguments are the three extensions of scalars, each additive because it is a left adjoint. -/
theorem representedAffineExtendScalarsComplexCompIso_eq :
    representedAffineExtendScalarsComplexCompIso B S hS h g =
      @Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (representedAffineExtendScalarsCompIso B S hS h g)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (ModuleCat.extendRestrictScalarsAdj
          (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (ModuleCat.extendRestrictScalarsAdj
          (representedAffineCommRingCatHom B S hS h).hom).left_adjoint_additive)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
            (ModuleCat.extendRestrictScalarsAdj
          (representedAffineCommRingCatHom B S hS (h ≫ g)).hom).left_adjoint_additive)
        (ComplexShape.up ℤ) :=
  rfl

end AlgebraicGeometry.Space

end
