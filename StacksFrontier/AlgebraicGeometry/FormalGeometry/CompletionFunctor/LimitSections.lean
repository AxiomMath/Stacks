module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.RingTheory.AdicCompletion.CategoricalLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Affine sections of the limit of the completion of a coherent module

Let `X` be a locally Noetherian scheme, `I` a quasi-coherent ideal sheaf and `F` a coherent
`𝒪_X`-module. The completion functor sends `F` to the inverse system
`n ↦ F / I ^ (n+1) F`, and `Stacks.Algebraization.completionToLimit` is the canonical map from `F`
to the limit of that system. This file computes the sections of the limit over an affine open `U`:
they are the `I(U)`-adic completion of `Γ(F, U)`, compatibly with the projections onto the terms of
the system and with the canonical map from `F`.

## Main definitions

* `Stacks.Algebraization.affineSectionFunctor` — evaluation of an `𝒪_X`-module at an affine open,
  valued in `Γ(X, U)`-modules.
* `Stacks.Algebraization.completionSectionsEquiv` — the sections over an affine open `U` of the
  limit of the completion of `F`, identified with the `I(U)`-adic completion of `Γ(F, U)`.

## Main results

* `Stacks.Algebraization.affineSectionFunctor_preservesLimit` — evaluation at an affine open
  preserves the limit of an inverse system indexed by `ℕᵒᵖ`.
* `Stacks.Algebraization.completionSectionsEquiv_projection` and
  `Stacks.Algebraization.completionSectionsEquiv_of` — the two characterisations of that
  identification: its component at the `n`-th term of the system is the level-`n + 1` evaluation of
  the adic completion read through `completionQuotientSectionsEquiv`, and it carries the image of a
  section of `F` to the value of `completionToLimit` on that section.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so an instance found for one is not found for
the other. Every categorical construction is therefore given its category explicitly as
`(C := X.Modules)`, and a `congrArg` against a stated equality of morphisms replaces a `rw` whose
motive would mix the two presentations.

The target of `affineSectionFunctor` is `ModuleCat Γ(X, U)` rather than
`ModuleCat (X.ringCatSheaf.obj.obj (op U))`, which is the target of the bare
`SheafOfModules.evaluation`. The two rings are definitionally equal but not syntactically so, and
the adic completion of `Γ(F, U)` is a module over the former; postcomposing with restriction of
scalars along `RingHom.id` moves the functor to that spelling without changing its value, and
`ModuleCat.restrictScalarsId` identifies the composite with the bare evaluation, which is how its
limit-preservation is inherited.

The identification itself is `AdicCompletion.quotientSystemLimitEquiv` for the system of affine
sections, whose comparison equivalences are `completionQuotientSectionsEquiv` and whose
intertwining hypothesis is `completionQuotientSectionsEquiv_naturality`: that system is a shifted
tower of adic quotients of `Γ(F, U)`, so its limit is the adic completion. The two limit cones are
compared by `IsLimit.conePointUniqueUpToIso`, so that both characterisations are instances of
`IsLimit.conePointUniqueUpToIso_hom_comp`.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### The scalar action on sections -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

/-! ### Evaluation at an affine open -/

/-- Evaluation of an `𝒪_X`-module at an affine open `U`, valued in `Γ(X, U)`-modules.

The bare `SheafOfModules.evaluation` lands in modules over `X.ringCatSheaf.obj.obj (op U)`;
restricting scalars along `RingHom.id Γ(X, U)` moves it to the `Γ(X, U)` spelling of that ring
without changing its value. -/
public noncomputable def affineSectionFunctor {X : Scheme.{u}} (U : X.affineOpens) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, U.1) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U.1) ⋙
    ModuleCat.restrictScalars (RingHom.id Γ(X, U.1))

/-- Evaluation at an affine open preserves the limit of an inverse system of `𝒪_X`-modules indexed
by `ℕᵒᵖ`. -/
public theorem affineSectionFunctor_preservesLimit {X : Scheme.{u}} (U : X.affineOpens)
    (S : ℕᵒᵖ ⥤ X.Modules) : PreservesLimit S (affineSectionFunctor U) :=
  (preservesLimit_iff_of_natIso S (Functor.isoWhiskerLeft
    (SheafOfModules.evaluation X.ringCatSheaf (op U.1))
    (ModuleCat.restrictScalarsId Γ(X, U.1)).symm)).mp
    (SheafOfModules.evaluationPreservesLimit S (op U.1))

/-! ### The sections of the limit of the completion -/

/-- The affine sections of the completion of `F`, as an inverse system of `Γ(X, U)`-modules. -/
private noncomputable abbrev completionSectionsSystem (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens) :
    ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U.1) :=
  ((completionFunctor X I).obj F).obj ⋙ affineSectionFunctor U

/-- The adic completion of `Γ(F, U)` is the limit of the affine sections of the completion of
`F`. -/
private noncomputable def adicCompletionSectionsIsLimit (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens) :
    IsLimit (AdicCompletion.quotientSystemCone (I.ideal U) Γ(F.obj, U)
      (completionSectionsSystem X I F U) (fun n => completionQuotientSectionsEquiv X I F n U)
      (fun h x => completionQuotientSectionsEquiv_naturality X I F U h x)) :=
  AdicCompletion.quotientSystemConeIsLimit _ _ _ _ _

/-- The affine sections of a limit cone of the completion of `F` form a limit cone. -/
private noncomputable def mapConeCompletionIsLimit (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens) :
    IsLimit ((affineSectionFunctor U).mapCone
      (limit.cone (C := X.Modules) ((completionFunctor X I).obj F).obj)) :=
  haveI := affineSectionFunctor_preservesLimit U ((completionFunctor X I).obj F).obj
  isLimitOfPreserves _ (limit.isLimit _)

/-- The sections over an affine open `U` of the limit of the completion of `F`, identified with
the `I(U)`-adic completion of `Γ(F, U)`. -/
@[no_expose] public noncomputable def completionSectionsEquiv (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens) :
    AdicCompletion (I.ideal U) Γ(F.obj, U) ≃ₗ[Γ(X, U)]
      (affineSectionFunctor U).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) :=
  ((adicCompletionSectionsIsLimit X I F U).conePointUniqueUpToIso
    (mapConeCompletionIsLimit X I F U)).toLinearEquiv

/-- The components of `Stacks.Algebraization.completionSectionsEquiv`: projecting to the sections
of the `n`-th term of the completion recovers the level-`n + 1` evaluation of the adic completion,
read through `Stacks.Algebraization.completionQuotientSectionsEquiv`. -/
public theorem completionSectionsEquiv_projection (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens)
    (n : ℕ) (x : AdicCompletion (I.ideal U) Γ(F.obj, U)) :
    (limit.π (C := X.Modules) ((completionFunctor X I).obj F).obj (op n)).val.app (op U.1)
        (completionSectionsEquiv X I F U x) =
      completionQuotientSectionsEquiv X I F n U
        (AdicCompletion.eval (I.ideal U) Γ(F.obj, U) (n + 1) x) :=
  congrArg (fun f : ModuleCat.of Γ(X, U) (AdicCompletion (I.ideal U) Γ(F.obj, U)) ⟶
      (affineSectionFunctor U).obj (((completionFunctor X I).obj F).obj.obj (op n)) => f x)
    ((adicCompletionSectionsIsLimit X I F U).conePointUniqueUpToIso_hom_comp
      (mapConeCompletionIsLimit X I F U) (op n))

/-- `Stacks.Algebraization.completionSectionsEquiv` is compatible with the canonical map from `F`
to the limit of its completion: it carries the image in the adic completion of a section of `F`
over `U` to the value of `Stacks.Algebraization.completionToLimit` on that section. -/
public theorem completionSectionsEquiv_of (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens)
    (s : Γ(F.obj, U)) :
    completionSectionsEquiv X I F U (AdicCompletion.of (I.ideal U) Γ(F.obj, U) s) =
      (completionToLimit X I F).val.app (op U.1) s := by
  refine Concrete.isLimit_ext _ (mapConeCompletionIsLimit X I F U) _ _ fun n => ?_
  change (limit.π (C := X.Modules) ((completionFunctor X I).obj F).obj n).val.app (op U.1) _ =
    (limit.π (C := X.Modules) ((completionFunctor X I).obj F).obj n).val.app (op U.1) _
  rw [completionSectionsEquiv_projection, AdicCompletion.eval_of]
  change completionQuotientSectionsEquiv X I F n.unop U (Submodule.Quotient.mk s) = _
  rw [completionQuotientSectionsEquiv_mk]
  exact (congrArg (fun f : F.obj ⟶ ((completionFunctor X I).obj F).obj.obj n =>
    f.val.app (op U.1) s) (completionToLimit_projection X I F n)).symm

end Stacks.Algebraization

end
