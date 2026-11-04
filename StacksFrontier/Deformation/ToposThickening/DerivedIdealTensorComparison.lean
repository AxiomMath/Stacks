module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData
public import StacksFrontier.Deformation.ToposThickening.IdealTensorProjection

/-!
# The ideal part of a derived base change

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `I₀` be a sheaf
of `O₀`-modules, with `I = I₀|_O` its restriction. This file builds the comparison

`((K ⊗^L_O O₀) ⊗^L_{O₀} I₀)|_O ⟶ K ⊗^L_O I`

of functors on the derived category of `O`-modules, which is the second of the two
identifications a `Deformation.ComplexLift.DerivedReduction` needs: it identifies the first
vertex of the reduction triangle with the ideal part of a derived base change.

At a complex of flat `O`-modules the comparison is an isomorphism, and that is what makes it
one everywhere once both sides are known to be left derived functors. The three steps it is
composed of are the counit of derived base change, the counit of the derived tensor product with
`I₀`, and the projection formula
`Deformation.ComplexLift.idealTensorRightIso`; the first two are invertible on flat complexes
because both functors are derived by flat resolutions, and the middle one is applied to
`O₀ ⊗_O K`, which is again a complex of flat modules by Stacks 05V4.

## Main definitions

* `Deformation.ComplexLift.idealTensorComplexLeg`: the last step, an isomorphism of functors on
  the homotopy category, built on cochain complexes where the composite of two
  `CategoryTheory.Functor.mapHomologicalComplex`es is the `mapHomologicalComplex` of the
  composite on the nose.

## Implementation notes

As in `StacksFrontier/Deformation/ToposThickening/DerivedRestrictionTensorComparison.lean`, the
isomorphism of functors on the homotopy category is built after precomposing with the homotopy
quotient and then lifted by `CategoryTheory.Quotient.natIsoLift`: on cochain complexes the
degreewise functors compose on the nose, whereas
`CategoryTheory.Functor.mapHomotopyCategory` of a composite is not the composite of the
`mapHomotopyCategory`s.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- The degreewise form of the projection formula read into the derived category: extension of
scalars, then the degreewise tensor product with `I₀`, then restriction of scalars, all applied
to complexes, is the degreewise tensor product with `I`. -/
def idealTensorComplexIso :
    (extensionOfScalars f ⋙ tensorRight O₀ I₀ ⋙
          SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (tensorRight O (restrictIdeal f I₀)).mapHomologicalComplex (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomologicalComplex (idealTensorRightIso f I₀).inv (ComplexShape.up ℤ)
  inv := NatTrans.mapHomologicalComplex (idealTensorRightIso f I₀).hom (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, Iso.inv_hom_id,
      NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, Iso.hom_inv_id,
      NatTrans.mapHomologicalComplex_id]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- The three degreewise functors compose, on the nose, into the degreewise functor of the
composite: `CategoryTheory.Functor.mapHomologicalComplex` of a composite is the composite of the
`mapHomologicalComplex`es. Naming the equation keeps the elaborator from unfolding the whole
composite inside the chain of isomorphisms below. -/
theorem mapHomologicalComplex_comp_eq :
    ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) =
      (extensionOfScalars f ⋙ tensorRight O₀ I₀ ⋙
            SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  rfl

/-- The first three steps: the two degreewise functors are pulled out of the homotopy quotient
and restriction of scalars is pulled past the localization. Named separately so that the
associativity bridge below is elaborated against a small term. -/
def quotientCompIdealTensorAux :
    HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⋙
        ((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          tensorRightHomotopy.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ≅
      ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :=
  Functor.isoWhiskerRight
      ((extensionOfScalars f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (tensorRightHomotopy.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ≪≫
    Functor.isoWhiskerLeft
      ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (quotientCompTensorRightIso.{d₀} I₀)
        (restrictionOnDerived.{d, d₀} f)) ≪≫
    Functor.isoWhiskerLeft
      ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ))
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors)

/-- The remaining two steps: the three degreewise functors are read as the degreewise functor of
their composite, and the projection formula identifies that with the degreewise tensor product
with `I`. -/
def idealTensorComplexTail :
    ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ≅
      HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ) ⋙
        tensorRightHomotopy.{d} (restrictIdeal f I₀) :=
  eqToIso (mapHomologicalComplex_comp_eq f I₀) ≪≫
    Functor.isoWhiskerRight (idealTensorComplexIso f I₀) DerivedCategory.Q ≪≫
    (quotientCompTensorRightIso.{d} (restrictIdeal f I₀)).symm

/-- The last step of the comparison, read after precomposition with the homotopy quotient —
the shape in which it is built, on cochain complexes. -/
def quotientCompIdealTensorIso :
    HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⋙
        ((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          tensorRightHomotopy.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ≅
      HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ) ⋙
        tensorRightHomotopy.{d} (restrictIdeal f I₀) :=
  quotientCompIdealTensorAux.{d, d₀} f I₀ ≪≫ idealTensorComplexTail.{d} f I₀

/-- **The last step of the comparison.** Extension of scalars followed by the degreewise tensor
product with `I₀` and restriction of scalars, read on the homotopy category, is the degreewise
tensor product with `I`.

This is the projection formula `Deformation.ComplexLift.idealTensorRightIso`, which is an
isomorphism at every sheaf of modules, carried to the homotopy category: it is the step of the
comparison that needs no flatness. -/
def idealTensorComplexLeg :
    (extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        tensorRightHomotopy.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f ≅
      tensorRightHomotopy.{d} (restrictIdeal f I₀) :=
  Quotient.natIsoLift _ (quotientCompIdealTensorIso.{d, d₀} f I₀)

end Deformation.ComplexLift

end
