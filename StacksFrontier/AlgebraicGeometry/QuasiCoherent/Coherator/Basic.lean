module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Grothendieck

/-!
# The coherator, limits and injectives in quasi-coherent modules

For a scheme `X` the category `QCoh(𝒪_X)` of quasi-coherent `𝒪_X`-modules is Grothendieck
abelian (`AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian`).  This file records
the three consequences of that which [Stacks, Tag 077P] asserts: the inclusion of `QCoh(𝒪_X)`
into all `𝒪_X`-modules has a right adjoint, the *coherator*; `QCoh(𝒪_X)` has all limits; and it
has enough injectives.

## Main results

* `AlgebraicGeometry.quasicoherentInclusion_isLeftAdjoint`: the inclusion of the quasi-coherent
  modules has a right adjoint.
* `AlgebraicGeometry.quasicoherentModules_hasLimitsOfSize`: `QCoh(𝒪_X)` has all limits.
* `AlgebraicGeometry.isIso_coheratorCounit_app`: the counit of the coherator adjunction is an
  isomorphism at every quasi-coherent module.
* `AlgebraicGeometry.quasicoherentModules_enoughInjectives`: `QCoh(𝒪_X)` has enough
  injectives.

## References

* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The inclusion of quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules has a right
adjoint**, the coherator. -/
@[stacks 077P "coherator_adjoint", sga "6 II 3.2"]
theorem quasicoherentInclusion_isLeftAdjoint (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.IsLeftAdjoint :=
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    ⟨fun {_} _ ↦ preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι⟩
  isLeftAdjoint_of_preservesColimits_of_isSeparating.{u} (isSeparator_separator _) _

/-- **The category of quasi-coherent modules on a scheme has all limits.** -/
@[stacks 077P "all_limits"]
instance quasicoherentModules_hasLimitsOfSize (X : Scheme.{u}) :
    HasLimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  inferInstance

/-- **The counit of the coherator adjunction is an isomorphism at a quasi-coherent module.** -/
@[stacks 077P "coherator_counit"]
theorem isIso_coheratorCounit_app (X : Scheme.{u}) (M : X.Modules) [M.IsQuasicoherent] :
    letI := quasicoherentInclusion_isLeftAdjoint X
    IsIso ((Adjunction.ofIsLeftAdjoint
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).counit.app M) :=
  let := quasicoherentInclusion_isLeftAdjoint X
  (Adjunction.isIso_counit_app_iff_mem_essImage _).mpr
    ⟨⟨M, inferInstance⟩, ⟨Iso.refl _⟩⟩

/-- **The category of quasi-coherent modules on a scheme has enough injectives.** -/
@[stacks 077P "enough_injectives", sga "6 II 3.1" "more general"]
instance quasicoherentModules_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  inferInstance

end AlgebraicGeometry

end
