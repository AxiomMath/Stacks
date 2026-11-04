module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentDual
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation

/-!
# Coherence and reflexivity of the reflexive hull

On a locally Noetherian scheme `X`, the dual `F^∨` and the reflexive hull `F^∨∨` of a coherent
`𝒪_X`-module `F` are coherent, and if `X` is moreover integral, the reflexive hull is reflexive.
These are the internal-Hom clause of [Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
at `𝒢 = 𝒪_X` and the hull clause of [Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH).
The instances are stated both for `F : X.Modules` and for
`F : SheafOfModules.{u} (structureSheaf X.sheaf)`, the latter with the suffix `_structureSheaf`.

## Main results

* `isCoherent_dualSheaf`: the dual of a coherent module is coherent.
* `isCoherent_reflexiveHull`: the reflexive hull of a coherent module is coherent.
* `isIso_toDoubleDual_reflexiveHull`, `isIso_toReflexiveHull_reflexiveHull` and
  `isReflexive_reflexiveHull`: the reflexive hull of a coherent module is reflexive.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-! ### Coherence and finite presentation of the dual -/

/-- **The internal-Hom clause of Stacks, Tag 01Y2, at `𝒢 = 𝒪_X`**: the dual of a coherent module
on a locally Noetherian scheme is coherent. -/
public instance isCoherent_dualSheaf (F : X.Modules) [F.IsCoherent] :
    (dualSheaf F).IsCoherent :=
  isCoherent_dualSheaf_of_hasLocalKernelPresentation' X
    (hasLocalKernelPresentationDual X) F inferInstance

/-- The dual of a coherent module on a locally Noetherian scheme is coherent, for modules over
`structureSheaf X.sheaf`. -/
public instance isCoherent_dualSheaf_structureSheaf
    (F : SheafOfModules.{u} (structureSheaf X.sheaf)) [F.IsCoherent] :
    (dualSheaf F).IsCoherent :=
  isCoherent_dualSheaf_of_hasLocalKernelPresentation' X
    (hasLocalKernelPresentationDual X) F inferInstance

/-- The dual of a coherent module on a locally Noetherian scheme is of finite presentation, for
modules over `structureSheaf X.sheaf`. -/
public instance isFinitePresentation_dualSheaf_structureSheaf
    (F : SheafOfModules.{u} (structureSheaf X.sheaf)) [F.IsCoherent] :
    (dualSheaf F).IsFinitePresentation :=
  _root_.isFinitePresentation_of_isCoherent (dualSheaf F)

/-! ### Coherence of the reflexive hull -/

/-- **The coherence half of the hull clause of Stacks, Tag 0EBH**: the reflexive hull of a
coherent module on a locally Noetherian scheme is coherent. -/
public instance isCoherent_reflexiveHull (F : X.Modules) [F.IsCoherent] :
    (reflexiveHull F).IsCoherent :=
  inferInstance

/-- The reflexive hull of a coherent module on a locally Noetherian scheme is coherent, for
modules over `structureSheaf X.sheaf`. -/
public instance isCoherent_reflexiveHull_structureSheaf
    (F : SheafOfModules.{u} (structureSheaf X.sheaf)) [F.IsCoherent] :
    (reflexiveHull F).IsCoherent :=
  inferInstance

/-! ### Reflexivity of the reflexive hull -/

variable [IsIntegral X]

/-- **The reflexivity half of the hull clause of Stacks, Tag 0EBH**: the canonical map of the
reflexive hull of a coherent module on an integral locally Noetherian scheme to its double dual is
an isomorphism. -/
public instance isIso_toDoubleDual_reflexiveHull (F : X.Modules) [F.IsCoherent] :
    IsIso (toDoubleDual (reflexiveHull F)) :=
  isReflexive_dualSheaf_dualSheaf_of_hasLocalKernelPresentation X
    (hasLocalKernelPresentationDual X) F inferInstance

/-- The canonical map of the reflexive hull of a coherent module on an integral locally Noetherian
scheme to its double dual is an isomorphism, for modules over `structureSheaf X.sheaf`. -/
public instance isIso_toDoubleDual_reflexiveHull_structureSheaf
    (F : SheafOfModules.{u} (structureSheaf X.sheaf)) [F.IsCoherent] :
    IsIso (toDoubleDual (reflexiveHull F)) :=
  isReflexive_dualSheaf_dualSheaf_of_hasLocalKernelPresentation X
    (hasLocalKernelPresentationDual X) F inferInstance

/-- The bundled canonical map `toReflexiveHull` of the reflexive hull of a coherent module on an
integral locally Noetherian scheme is an isomorphism. -/
public instance isIso_toReflexiveHull_reflexiveHull (F : X.Modules) [F.IsCoherent] :
    IsIso (toReflexiveHull (reflexiveHull F)).1 :=
  isIso_toDoubleDual_reflexiveHull X F

/-- The bundled canonical map `toReflexiveHull` of the reflexive hull of a coherent module on an
integral locally Noetherian scheme is an isomorphism, for modules over `structureSheaf X.sheaf`. -/
public instance isIso_toReflexiveHull_reflexiveHull_structureSheaf
    (F : SheafOfModules.{u} (structureSheaf X.sheaf)) [F.IsCoherent] :
    IsIso (toReflexiveHull (reflexiveHull F)).1 :=
  isIso_toDoubleDual_reflexiveHull_structureSheaf X F

/-- **The reflexivity half of the hull clause of Stacks, Tag 0EBH**: the reflexive hull of a
coherent module on an integral locally Noetherian scheme is reflexive. -/
public theorem isReflexive_reflexiveHull (F : X.Modules) [F.IsCoherent] :
    IsReflexive (reflexiveHull F) :=
  isIso_toDoubleDual_reflexiveHull X F

end Stacks.AlgebraicGeometry.ReflexiveModules

end
