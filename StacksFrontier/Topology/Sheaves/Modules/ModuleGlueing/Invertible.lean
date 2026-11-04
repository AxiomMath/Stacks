module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# A sheaf of modules glued from invertible charts is invertible

Stacks 00AM glues a family of sheaves of modules on the charts `f i : Y i ⟶ S` of a cover of a
scheme by open immersions into a single sheaf of modules on `S`, and records the comparison with
the charts as the isomorphisms `Stacks.SheafOfModules.ModulesGlueData.chartIso`. Invertibility of
the result is not part of that statement, and this file supplies it: a glued sheaf of modules is
invertible as soon as each chart's sheaf is, provided the charts cover. It is the companion of
`Stacks.SheafOfModules.ModulesGlueData.isQuasicoherent_glued`.

Invertibility is local by `isInvertibleModule_of_forall_exists_isoUnit_openImmersion` (in
`Stacks.AlgebraicGeometry.TwistMapsInvertible`), which asks for a trivialization of the module
along an open immersion through a neighbourhood of each point. A trivialization of the restriction
to the `i`-th chart is one over an open `U` of `Y i`
(`Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over`), and `U.ι ≫ f i` is again an open
immersion, so no cover has to be refined and no open of `S` has to be named.

## Main results

* `Stacks.SheafOfModules.isInvertibleModule_of_restrict_openImmersions`: **invertibility is local
  along a cover by open immersions.**
* `Stacks.SheafOfModules.ModulesGlueData.isInvertibleModule_glued`: **a sheaf of modules glued
  from invertible charts is invertible.**
* `Stacks.SheafOfModules.ModulesDirectedGlueData.isInvertibleModule_glued`: the same for a locally
  directed glueing datum.

## Implementation notes

The transport of invertibility across the chart comparison is
`Stacks.SheafOfModules.isInvertible_of_iso`; `Stacks.Ample.IsInvertibleModule` is an `abbrev` for
`Stacks.SheafOfModules.IsInvertible` with the sheaf condition supplied, so that transport applies
with no bridge.

The covering hypothesis cannot be dropped: a glueing datum records nothing about the sections of
the glued sheaf over an open meeting no chart.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.TwistMapsInvertible (
  isInvertibleModule_of_forall_exists_isoUnit_openImmersion restrictIsoUnitOfOverIsoUnit)

universe w u

namespace Stacks.SheafOfModules

/-- **Invertibility is local along a cover by open immersions.** If the open ranges of a family of
open immersions `f i : Y i ⟶ S` cover `S` and the restriction of a sheaf of modules `M` on `S`
along each `f i` is invertible, then `M` is invertible.

A trivializing neighbourhood of a point of `S` is produced on the chart containing it and pushed
to `S` as the open immersion `U.ι ≫ f i`. -/
public theorem isInvertibleModule_of_restrict_openImmersions {S : Scheme.{u}} {ι : Type w}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] (M : S.Modules)
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, Stacks.Ample.IsInvertibleModule (Y i) (M.restrict (f i))) :
    Stacks.Ample.IsInvertibleModule S M := by
  refine isInvertibleModule_of_forall_exists_isoUnit_openImmersion M fun x => ?_
  have hx : x ∈ ⨆ i, (f i).opensRange := hf ▸ Opens.mem_top x
  obtain ⟨i, y, hy⟩ := Opens.mem_iSup.mp hx
  have := h i
  obtain ⟨U, hU, ⟨eo⟩⟩ := Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over (Y i)
    (M.restrict (f i)) y
  refine ⟨U.toScheme, U.ι ≫ f i, inferInstance, ⟨⟨y, hU⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp U.ι (f i)).app M ≪≫
    restrictIsoUnitOfOverIsoUnit (M.restrict (f i)) U eo

section Scheme

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)]

/-- **A sheaf of modules glued from invertible charts is invertible.** If the charts of a glueing
datum cover the scheme and the sheaf of modules on each chart is invertible, then so is the sheaf
of modules glued from the datum. -/
public theorem ModulesGlueData.isInvertibleModule_glued (D : ModulesGlueData S f)
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, Stacks.Ample.IsInvertibleModule (Y i) (D.mod i)) :
    Stacks.Ample.IsInvertibleModule S D.glued :=
  isInvertibleModule_of_restrict_openImmersions f D.glued hf fun i => by
    have := h i
    exact _root_.Stacks.SheafOfModules.isInvertible_of_iso (Y i).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (Y i)) (D.chartIso i).symm

/-- **A sheaf of modules glued from invertible charts along a locally directed cover is
invertible.** -/
public theorem ModulesDirectedGlueData.isInvertibleModule_glued [Preorder ι]
    (D : ModulesDirectedGlueData S f) (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, Stacks.Ample.IsInvertibleModule (Y i) (D.mod i)) :
    Stacks.Ample.IsInvertibleModule S D.glued :=
  D.toModulesGlueData.isInvertibleModule_glued hf h

end Scheme

end Stacks.SheafOfModules

end
