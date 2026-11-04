module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.PushforwardTensorDual
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRigidity
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pullback

/-!
# Base change of the relative dualizing complex at the standard model

For a cartesian square of quasi-compact quasi-separated schemes with `f : X ⟶ Y` proper, flat and
of finite presentation, `L(g')^* a(𝒪_Y) ≅ a'(𝒪_{Y'})` ([Stacks, Remark 0B6S], from
[Stacks, Tag 0AAB]). At the locally small model this is
`Stacks.Duality.twistedInverseImageStructureSheafBaseChangeIso`; here it is carried to the
standard model through the comparison of the two models.

## Main results

* `Stacks.Duality.StandardModel.pullbackRelativeDualizingComplexIso`: the isomorphism
  `L(g')^* a(𝒪_Y) ≅ a'(𝒪_{Y'})` at the standard model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.StandardModel

variable {X' X Y' Y : Scheme.{u}} [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **Base change of the relative dualizing complex** ([Stacks, Remark 0B6S], from
[Stacks, Tag 0AAB]): for a cartesian square of quasi-compact quasi-separated schemes with `f`
proper, flat and of finite presentation, `L(g')^* a(𝒪_Y) ≅ a'(𝒪_{Y'})` at the standard model. -/
def pullbackRelativeDualizingComplexIso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    (pullback g').obj (relativeDualizingComplex f).obj ≅ (relativeDualizingComplex f').obj := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  refine (Scheme.Modules.derivedModelEquiv X').fullyFaithfulFunctor.preimageIso ?_
  exact (StacksDraft.DerivedModel.schemeDerivedPullbackStandardModelEquivIso g').app _ ≪≫
    (Stacks.Duality.derivedPullback g').mapIso
      ((ObjectProperty.ι _).mapIso (relativeDualizingComplexModelIso f)) ≪≫
    (ObjectProperty.ι _).mapIso (twistedInverseImageStructureSheafBaseChangeIso sq).symm ≪≫
    (ObjectProperty.ι _).mapIso (relativeDualizingComplexModelIso f').symm

end Stacks.Duality.StandardModel

end
