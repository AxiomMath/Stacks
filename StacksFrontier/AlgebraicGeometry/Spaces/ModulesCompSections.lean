module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# Evaluating a composite of morphisms of `𝒪_F`-modules on a local section

Composition of morphisms of `𝒪_F`-modules is composition of the maps they induce on sections.
The fact is `rfl`, and it is stated here, at the algebraic-space spelling
`AlgebraicGeometry.Space.Modules`, rather than used from the general form for sheaves of modules
on a site.

## Main results

* `AlgebraicGeometry.Space.Modules.comp_val_app`: evaluating `a ≫ b` on a section is evaluating
  `a` and then `b`.

## Implementation notes

The general statement exists, as `Stacks.Sheaves.RingedToposModules.comp_val_app_apply` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean`, for an arbitrary
`SheafOfModules.{w} R` over a sheaf of rings on a site.  Substituting it for a space-level use is
measurably expensive: matching `{R : Sheaf J RingCat.{w}}` against
`AlgebraicGeometry.Space.Modules` obliges the elaborator to recover the site, the topology and the
ring sheaf from the small étale ringed site, which unfolds that site; in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean` the substitution exceeded
the heartbeat budget inside `homEquiv_structureModulePullbackMap_comp`, while an attribution
control — keeping a local copy and adding the general module's import anyway — built green, so the
cost is the substitution and not the import.

This module therefore states the same `rfl` at the space-level type, where nothing has to be
recovered, and lives on `StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean` alone so that any
space-level consumer can import it for no closure cost at all.
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **Evaluating a composite of morphisms of `𝒪_F`-modules on a local section is evaluating the
two factors in turn.** -/
public theorem Modules.comp_val_app {M N P : Modules.{u, m} B S hS F hF} (a : M ⟶ N) (b : N ⟶ P)
    (U : (SmallEtale B S hS F)ᵒᵖ) (s : M.val.obj U) :
    (a ≫ b).val.app U s = b.val.app U (a.val.app U s) :=
  rfl

end AlgebraicGeometry.Space

end
