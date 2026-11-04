/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Bridge
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.SubobjectPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback

/-!
# The readings of `F_{T'}` and of `F_T` on projective spaces

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame and `h : T' ⟶ T` a morphism
of test schemes over `B`.  The reading of `F_{T'}` on `ℙⁿ_{T'}` is the inverse image along
`ℙⁿ_{T'} ⟶ ℙⁿ_T` of the reading of `F_T`: compare `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` and apply
`AlgebraicGeometry.ProjectiveQuotOverSpace.readingPullbackIso`.  This is the identification
through which base change of quotients
(`AlgebraicGeometry.ProjectiveQuotOverSpace.subobjectPullback`) is compared with the pullback of
quotients of Stacks 082M.

The file also records that the inverse images of modules along
`AlgebraicGeometry.Space.representedSpaceMap` and `AlgebraicGeometry.schemeSpaceMap` agree, on
morphisms as well as objects.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseChangeReadingIso`: the reading of `F_{T'}` is the
  inverse image of the reading of `F_T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.heq_map_modulePullback_representedSpaceMap`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- See `StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuotOverSpace/Bridge.lean`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### Two spellings of the inverse image along a morphism of represented spaces -/

section Spelling

variable {W' W : BigFppfOver B integerBase B.contains_integerBase} (g : W' ⟶ W)

/-- The inverse images along `AlgebraicGeometry.Space.representedSpaceMap` and along
`AlgebraicGeometry.schemeSpaceMap` are the same functor. -/
theorem modulePullback_representedSpaceMap_eq :
    (@Space.modulePullback B integerBase B.contains_integerBase
        (schemeSpace W')
        (schemeSpace W)
        (schemeSpaceMap g) :
      Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W).1
          (schemeSpace W).2 ⥤
        Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W').1
          (schemeSpace W').2) =
      Space.modulePullback B integerBase B.contains_integerBase (schemeSpaceMap g) :=
  rfl

/-- The inverse images along `AlgebraicGeometry.Space.representedSpaceMap` and along
`AlgebraicGeometry.schemeSpaceMap` agree on morphisms.  (Comparing the two directly by
unification unfolds the inverse image of modules and does not terminate in reasonable time; the
comparison goes through the equality of the functors instead.) -/
theorem heq_map_modulePullback_representedSpaceMap
    {M N : Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W).1
      (schemeSpace W).2} (ψ : M ⟶ N) :
    HEq ((Space.modulePullback B integerBase B.contains_integerBase
        (schemeSpaceMap g)).map ψ)
      ((Space.modulePullback B integerBase B.contains_integerBase (schemeSpaceMap g)).map ψ) :=
  (HEq.rfl : HEq (@CategoryTheory.Functor.map
      (Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W).1
        (schemeSpace W).2) _
      (Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W').1
        (schemeSpace W').2) _
      (@Space.modulePullback B integerBase B.contains_integerBase
        (schemeSpace W')
        (schemeSpace W)
        (schemeSpaceMap g)) M N ψ)
    ((Space.modulePullback B integerBase B.contains_integerBase
        (schemeSpaceMap g)).map ψ)).symm.trans
    (congr_arg_heq (fun F : Space.Modules.{u, u} B integerBase B.contains_integerBase
        (schemeSpace W).1 (schemeSpace W).2 ⥤
          Space.Modules.{u, u} B integerBase B.contains_integerBase (schemeSpace W').1
            (schemeSpace W').2 => F.map ψ)
      (modulePullback_representedSpaceMap_eq g))

end Spelling

section BaseChange

variable {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T)

/-- **The reading of `F_{T'}` is the inverse image of the reading of `F_T`** along
`ℙⁿ_{T'} ⟶ ℙⁿ_T`: `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` read on `ℙⁿ_{T'}`, followed by
`AlgebraicGeometry.ProjectiveQuotOverSpace.readingPullbackIso`. -/
def baseChangeReadingIso :
    (reading E T').obj (D.baseChangeModule T') ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n ((𝒯).map h.left))).obj
        ((reading E T).obj (D.baseChangeModule T)) :=
  (reading E T').mapIso ((D.baseChangeComparison h).app D.F) ≪≫
    readingPullbackIso E h _ (isQuasicoherentOnSite_baseChangeModule T)

end BaseChange

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
