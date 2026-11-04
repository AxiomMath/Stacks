module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.DerivedPushforwardCommutation
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardArbitraryTarget
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image commutes with the coherator, for a qcqs morphism

`Stacks.Duality.coheratorDerivedPushforwardIso` identifies `Rf_* ∘ DQ_X` with `DQ_Y ∘ Rf_*` for a
morphism along which `Rf_*` preserves quasi-coherence of cohomology, taken as the argument
`hpush`. For a quasi-compact and quasi-separated morphism that preservation is part (1) of
[Stacks, Tag 08D5], available at the locally small model as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward`, and discharging it gives
[Stacks, Tag 0CR1] under the tag's own hypotheses.

## Main definitions

* `Stacks.Duality.coheratorDerivedPushforwardIsoOfQcqs`: the canonical natural isomorphism
  `Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*` for a quasi-compact and quasi-separated morphism
  ([Stacks, Tag 0CR1]).

## References

* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (DQX : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
  (DQY : DerivedCategory Y.Modules ⥤ quasiCoherentDerivedCategory Y)
  (adjX : (DerivedCategoryB.derivedCategoryB
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⊣ DQX)
  (adjY : (DerivedCategoryB.derivedCategoryB
    (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⊣ DQY)

/-- Derived direct image commutes with the coherator. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes and suppose the inclusions `D_QCoh ⥤ D` admit right adjoints
`DQ_X` and `DQ_Y` on `X` and on `Y`. Then

`Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*`

as functors `D(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

This is `Stacks.Duality.coheratorDerivedPushforwardIso` with its preservation hypothesis
discharged: for a quasi-compact and quasi-separated morphism `Rf_*` sends `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)`, which is part (1) of [Stacks, Tag 08D5] in the form
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward`. -/
@[stacks 0CR1]
def coheratorDerivedPushforwardIsoOfQcqs :
    DQX ⋙ quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward f) ≅
      derivedPushforward f ⋙ DQY :=
  coheratorDerivedPushforwardIso f (isQuasicoherent_homology_derivedPushforward f)
    DQX DQY adjX adjY

end Stacks.Duality

end
