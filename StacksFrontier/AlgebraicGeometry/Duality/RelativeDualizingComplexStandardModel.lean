module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic

/-!
# An isomorphism `E[-k] ≅ a(𝒪_Y)` read at the standard model

For a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes the relative dualizing
complex `a(𝒪_Y)` (the twisted inverse image of [Stacks, Tag 0A9E] at `𝒪_Y`) can be formed at
either model of the derived categories of `𝒪`-modules: the standard one, where the duality API
of `Stacks.Duality.StandardModel` lives, and the locally small one,
`Scheme.Modules.hasDerivedCategory`. The comparison of models identifies the two
(`Stacks.Duality.StandardModel.relativeDualizingComplexModelIso`) and carries a sheaf placed in
degree `k` to the same sheaf placed in degree `k`
(`StacksDraft.DerivedModel.modelSingleFunctorIso`), so an isomorphism `E[-k] ≅ a(𝒪_Y)` at one
model gives one at the other.

## Main definitions

* `Stacks.Duality.StandardModel.singleFunctorIsoRelativeDualizingComplexOfModel`: an
  isomorphism `E[-k] ≅ a(𝒪_Y)` at the locally small model gives one at the standard model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Duality.StandardModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **An isomorphism `E[-k] ≅ a(𝒪_Y)` at the locally small model gives one at the standard
model.** -/
def singleFunctorIsoRelativeDualizingComplexOfModel (k : ℤ) (E : X.Modules)
    (ψ₀ : (@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
      k).obj E ≅ (@Stacks.Duality.relativeDualizingComplex X Y f
          (Scheme.Modules.hasDerivedCategory X) (Scheme.Modules.hasDerivedCategory Y)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
            f) (Stacks.Duality.DerivedPushforward.derivedStructureSheaf Y)).obj) :
    (DerivedCategory.singleFunctor X.Modules k).obj E ≅
      (Stacks.Duality.relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward f)
        (derivedStructureSheafInDegree Y 0)).obj :=
  (Scheme.Modules.derivedModelEquiv X).unitIso.app _ ≪≫
    (Scheme.Modules.derivedModelEquiv X).inverse.mapIso
      ((StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X) k).app E ≪≫ ψ₀ ≪≫
        ((ι _).mapIso (relativeDualizingComplexModelIso f)).symm) ≪≫
    (Scheme.Modules.derivedModelEquiv X).unitIso.symm.app _

end Stacks.Duality.StandardModel

end
