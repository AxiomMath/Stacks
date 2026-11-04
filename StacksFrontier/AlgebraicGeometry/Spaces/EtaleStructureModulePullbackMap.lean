module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompAbsorption

/-!
# Along an étale morphism the comparison `f^*𝒪_Y ⟶ 𝒪_X` is invertible

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The canonical comparison `AlgebraicGeometry.Space.structureModulePullbackMap`
`f^*𝒪_Y ⟶ 𝒪_X`, *defined* by its linear map of sections of [Stacks Project, Tag 03LU] —
pullback of regular functions along the vertical morphism of a diagram of étale scheme charts —
and then transposed twice, is the component at `𝒪_Y` of the identification `f^*G ≅ G|_{X_étale}`
of [Stacks Project, Equation 03LW],
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, whose target at `𝒪_Y` is `𝒪_X`
on the nose.  That identification is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStructureSheaf.lean`, made there
through the corepresentability comparison `AlgebraicGeometry.Space.modulePullbackUnitIso`.

This file concludes from it that `AlgebraicGeometry.Space.structureModulePullbackMap` is
invertible, hence injective, along an étale morphism, as a component of a natural isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_isEtale` and
  `AlgebraicGeometry.Space.mono_structureModulePullbackMap_of_isEtale`: along an étale morphism
  the comparison `f^*𝒪_Y ⟶ 𝒪_X` is invertible, hence injective — which is the hypothesis that
  `AlgebraicGeometry.Space.mono_idealSheafMap_of_mono` carries.

## Implementation notes

**No tag is placed.**  [Stacks Project, Equation 03LW] asserts the identification of the inverse
image of modules with étale restriction, which is registered where it is constructed.  Nothing in
the Stacks Project asserts the agreement of that identification with a comparison of structure
sheaves built from the chartwise universal property of the direct image: the comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean` is an artefact of this
development, and so are its invertibility and injectivity here.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-! ### The comparison of structure sheaves along an étale morphism -/

include hf in
/-- **The comparison `f^*𝒪_Y ⟶ 𝒪_X` is invertible along an étale morphism**, being a component of
the natural isomorphism of [Stacks Project, Equation 03LW] by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq`. -/
theorem isIso_structureModulePullbackMap_of_isEtale :
    IsIso (structureModulePullbackMap B S hS f) :=
  modulePullbackIsoEtaleModulePullback_hom_app_unit_eq B S hS f hf ▸
    inferInstanceAs (IsIso ((modulePullbackIsoEtaleModulePullback B S hS f hf).app
      (SheafOfModules.unit (structureRingSheaf B S hS Y))).hom)

include hf in
/-- The comparison `f^*𝒪_Y ⟶ 𝒪_X` is injective along an étale morphism.  This is the hypothesis
that `AlgebraicGeometry.Space.mono_idealSheafMap_of_mono` carries. -/
theorem mono_structureModulePullbackMap_of_isEtale :
    Mono (structureModulePullbackMap B S hS f) :=
  have := isIso_structureModulePullbackMap_of_isEtale B S hS f hf
  IsIso.mono_of_iso _

end AlgebraicGeometry.Space

end
