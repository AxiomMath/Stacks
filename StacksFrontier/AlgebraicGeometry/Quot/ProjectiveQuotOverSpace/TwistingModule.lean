/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Situation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic

/-!
# The pullback of `𝒪(1)` to `B × ℙⁿ_ℤ`

Stacks 0DPB measures Hilbert polynomials on `X = B × ℙⁿ_ℤ` against the pullback `𝓛` of
`𝒪_{ℙⁿ}(1)` along the projection `X ⟶ ℙⁿ_ℤ`.  This file builds `𝓛` on the small étale site of
the algebraic space `X` and shows that it is invertible.

On `ℙⁿ_ℤ`, the scheme of the object `AlgebraicGeometry.ProjectiveQuot.projectiveSiteBase` of the
big fppf site over `Spec ℤ`, the twisting sheaf `𝒪(1)`
(`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`) is carried to the algebraic space
`h_{ℙⁿ_ℤ}` by the associated module on the small étale site followed by the identification of that
site with the small étale site of `h_{ℙⁿ_ℤ}` (the functor of Stacks 03DX); this preserves
invertibility
(`Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule`). For a
Quot situation with a projective frame `X ⟶ ℙⁿ_ℤ`, `𝓛` is the inverse image of that module,
invertible by Stacks 0B8P.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistingModuleBase`: `𝒪(1)` on `h_{ℙⁿ_ℤ}`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistingModule`: its pullback `𝓛` to `X` along the
  projection of a projective frame; at `AlgebraicGeometry.ProjectiveQuotOverSpace.situationFrame`
  this is the module `𝓛` of Stacks 0DPB.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable (B : BigFppfSite.{u}) (n : ℕ)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **`𝒪(1)` on the algebraic space `h_{ℙⁿ_ℤ}`**: the twisting sheaf of `ℙⁿ_ℤ`, carried to the
small étale site of the algebraic space it represents. -/
def twistingModuleBase : Space.Modules.{u, u} B integerBase B.contains_integerBase
    (quotSituation B n 0).X.1 (quotSituation B n 0).X.2 :=
  (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSiteBase B n)).functor.obj
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSiteBase B n)) (projectiveSiteBase B n).left.property).obj
        (_root_.Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
          ((𝒯).obj (siteBase B))))

/-- **`𝒪(1)` on `h_{ℙⁿ_ℤ}` is invertible**: the twisting sheaf of `ℙⁿ_ℤ` is
(`Stacks.TwistInvertibleOverBase.isInvertibleModule_projectiveSpaceTwistingSheaf`), and the
functor of Stacks 03DX preserves invertible modules. -/
instance isInvertible_twistingModuleBase :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase (quotSituation B n 0).X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (quotSituation B n 0).X.1 (quotSituation B n 0).X.2).O)).property
      (twistingModuleBase B n) :=
  Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule B
    integerBase B.contains_integerBase (projectiveSiteBase B n) _
    (_root_.Stacks.TwistInvertibleOverBase.isInvertibleModule_projectiveSpaceTwistingSheaf n
      ((𝒯).obj (siteBase B)))

variable {B n} {D : Space.QuotSituation B integerBase B.contains_integerBase}

/-- **The pullback `𝓛` of `𝒪(1)` to `X`** along the projection `X ⟶ ℙⁿ_ℤ` of a projective frame
`X = B × ℙⁿ_ℤ`. -/
def twistingModule (E : ProjectiveFrame B n D) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2 :=
  (Space.modulePullback B integerBase B.contains_integerBase E.toProjective).obj
    (twistingModuleBase B n)

/-- **`𝓛` is invertible** (Stacks 0B8P). -/
instance isInvertible_twistingModule (E : ProjectiveFrame B n D) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase D.X.1 D.X.2).O)).property
      (twistingModule E) :=
  Space.stacksIsInvertible_modulePullback_obj B integerBase B.contains_integerBase
    E.toProjective (twistingModuleBase B n)

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
