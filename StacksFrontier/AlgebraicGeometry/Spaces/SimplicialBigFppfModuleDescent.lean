module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.OverSimplicialObjectModuleDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPretopology
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi

/-!
# Descent of modules along an fppf hypercovering of algebraic spaces

Let `T` be a big fppf site of algebraic spaces over `S` and `a : U → X` a hypercovering of `X`
in `(Spaces/S)_fppf`, for the chosen fppf coverings. The ringed augmentation
`a_{fppf} : (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) ⟶ (Sh((Spaces/X)_fppf), 𝒪_{big})` of
Stacks 0DHC has `a_{fppf}^*` fully faithful on sheaves of modules, with essential image the
cartesian `𝒪_{big,total}`-modules and quasi-inverse `a_{fppf,*}`. This is Stacks 0DAB for the
site `(Spaces/S)_fppf`, the input of the proof of Stacks 0DHD.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.descent_modules_bigFppfAugmentation`, with
  its four clauses also stated separately.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfAugmentationRingedHom_isFlat`:
  `a_{fppf}` is flat.

## Implementation notes

The counit clause is derived here from full faithfulness and the essential image rather than read
off the general statement: instantiating the general counit clause at `a_{fppf}` compares two
spellings of the counit's component and exhausts the kernel.

## References

* [Stacks Project, Tag 0DAB](https://stacks.math.columbia.edu/tag/0DAB)
* [Stacks Project, Tag 0DHC](https://stacks.math.columbia.edu/tag/0DHC)
* [Stacks Project, Tag 0DHD](https://stacks.math.columbia.edu/tag/0DHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.CategoryTheory.Hypercovering

universe u

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  (a : U ⟶ (SimplicialObject.const T.Spaces).obj X)

/-- The inverse image of `a_{fppf}` on sheaves of sets is restriction along `V/U_n ↦ V/X`. -/
theorem bigFppfAugmentationRingedHom_inverseImage :
    (bigFppfAugmentationRingedHom a).toToposHom.inverseImage =
      (SimplicialOver.augmentationFunctor U a).sheafPushforwardContinuous (Type (u + 1))
        (SimplicialOver.totalTopology T.topology U) (T.topology.over X) :=
  rfl

/-- The structure map of `a_{fppf}` is the identification `𝒪_{big,total} = a_{fppf}⁻¹𝒪_{big}`. -/
theorem isIso_bigFppfAugmentationRingedHom_fSharpInverseImage :
    IsIso (bigFppfAugmentationRingedHom a).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso (X := bigFppfTotalRingedTopos a)
    (Y := BigFppfSpaceSite.bigFppfRingedTopos T X) _ _

/-- **The ringed augmentation `a_{fppf}` is flat**: its structure map in inverse-image form is
the identification `a_{fppf}⁻¹𝒪_{big} ≅ 𝒪_{big,total}`, an isomorphism. Hence
`La_{fppf}^* = a_{fppf}^*` on derived categories. -/
theorem bigFppfAugmentationRingedHom_isFlat : (bigFppfAugmentationRingedHom a).IsFlat :=
  AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso _
    (isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a)

variable {a} (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h

/-- For an fppf hypercovering, `a_{fppf}^*` is fully faithful on sheaves of modules. -/
theorem nonempty_fullyFaithful_bigFppfAugmentation_pullbackModules :
    Nonempty (bigFppfAugmentationRingedHom a).toModulesHom.pullbackModules.FullyFaithful :=
  (SimplicialOver.descent_modules_augmented_overSimplicialObjectModuleDescent
    T.pretopologyBigFppfPretopology T.toGrothendieck_pretopology_bigFppfPretopology h
    (bigFppfAugmentationRingedHom a) (hf := isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a)
    (eqToIso (bigFppfAugmentationRingedHom_inverseImage a))).1

/-- For an fppf hypercovering, the essential image of `a_{fppf}^*` on sheaves of modules
consists of the cartesian `𝒪_{big,total}`-modules. -/
theorem bigFppfAugmentation_pullbackModules_essImage_iff
    (F : SheafOfModules.{u + 1} ((SimplicialOver.situation T.topology U).totalRingSheaf
      (bigFppfTotalStructureSheaf a))) :
    (bigFppfAugmentationRingedHom a).toModulesHom.pullbackModules.essImage F ↔
      (SimplicialOver.situation T.topology U).IsCartesianModule (bigFppfTotalStructureSheaf a) F :=
  (SimplicialOver.descent_modules_augmented_overSimplicialObjectModuleDescent
    T.pretopologyBigFppfPretopology T.toGrothendieck_pretopology_bigFppfPretopology h
    (bigFppfAugmentationRingedHom a) (hf := isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a)
    (eqToIso (bigFppfAugmentationRingedHom_inverseImage a))).2.1 F

/-- For an fppf hypercovering, the unit of `a_{fppf}^* ⊣ a_{fppf,*}` is invertible. -/
theorem isIso_bigFppfAugmentation_unit :
    IsIso (bigFppfAugmentationRingedHom a).pullbackAdjPushforwardModules.unit :=
  (SimplicialOver.descent_modules_augmented_overSimplicialObjectModuleDescent
    T.pretopologyBigFppfPretopology T.toGrothendieck_pretopology_bigFppfPretopology h
    (bigFppfAugmentationRingedHom a) (hf := isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a)
    (eqToIso (bigFppfAugmentationRingedHom_inverseImage a))).2.2.1

/-- For an fppf hypercovering, the counit of `a_{fppf}^* ⊣ a_{fppf,*}` is invertible at every
cartesian `𝒪_{big,total}`-module. -/
theorem isIso_bigFppfAugmentation_counit_app
    (F : SheafOfModules.{u + 1} ((SimplicialOver.situation T.topology U).totalRingSheaf
      (bigFppfTotalStructureSheaf a)))
    (hF : (SimplicialOver.situation T.topology U).IsCartesianModule
      (bigFppfTotalStructureSheaf a) F) :
    IsIso ((bigFppfAugmentationRingedHom a).pullbackAdjPushforwardModules.counit.app F) := by
  have hff := (nonempty_fullyFaithful_bigFppfAugmentation_pullbackModules h).some
  have := hff.full
  have := hff.faithful
  exact ((bigFppfAugmentationRingedHom a).pullbackAdjPushforwardModules
    |>.isIso_counit_app_iff_mem_essImage).mpr
      ((bigFppfAugmentation_pullbackModules_essImage_iff h F).mpr hF)

/-- **Descent of modules along an fppf hypercovering.** For a hypercovering `a : U → X` in
`(Spaces/S)_fppf`, the pullback `a_{fppf}^*` along the ringed augmentation of Stacks 0DHC is fully
faithful with essential image the cartesian `𝒪_{big,total}`-modules; the unit of
`a_{fppf}^* ⊣ a_{fppf,*}` is invertible, and its counit is invertible at every cartesian module. -/
theorem descent_modules_bigFppfAugmentation :
    Nonempty (bigFppfAugmentationRingedHom a).toModulesHom.pullbackModules.FullyFaithful ∧
      (∀ F : SheafOfModules.{u + 1} ((SimplicialOver.situation T.topology U).totalRingSheaf
          (bigFppfTotalStructureSheaf a)),
        (bigFppfAugmentationRingedHom a).toModulesHom.pullbackModules.essImage F ↔
          (SimplicialOver.situation T.topology U).IsCartesianModule
            (bigFppfTotalStructureSheaf a) F) ∧
      IsIso (bigFppfAugmentationRingedHom a).pullbackAdjPushforwardModules.unit ∧
      ∀ F : SheafOfModules.{u + 1} ((SimplicialOver.situation T.topology U).totalRingSheaf
          (bigFppfTotalStructureSheaf a)),
        (SimplicialOver.situation T.topology U).IsCartesianModule
            (bigFppfTotalStructureSheaf a) F →
          IsIso ((bigFppfAugmentationRingedHom a).pullbackAdjPushforwardModules.counit.app F) :=
  ⟨nonempty_fullyFaithful_bigFppfAugmentation_pullbackModules h,
    bigFppfAugmentation_pullbackModules_essImage_iff h, isIso_bigFppfAugmentation_unit h,
    isIso_bigFppfAugmentation_counit_app h⟩

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
