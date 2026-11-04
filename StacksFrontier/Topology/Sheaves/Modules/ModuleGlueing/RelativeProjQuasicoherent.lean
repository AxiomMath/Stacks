module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheaf
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent

/-!
# The sheaves on a relative projective spectrum are quasi-coherent

The sheaf `ℳ̃` attached to a graded module on a relative projective spectrum, and the twisting
sheaves `𝒪(n)` of that spectrum, are glued from the sheaves attached to graded modules on the
charts. On a chart the sheaf attached to a graded module is quasi-coherent, Tag 01MB, and
quasi-coherence is local on the base, so both glued sheaves are quasi-coherent.

## Main results

* `Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart`: the charts cover the relative
  projective spectrum.
* `Stacks.RelativeProj.Situation.isQuasicoherent_moduleChart` and
  `Stacks.RelativeProj.Situation.isQuasicoherent_twistChart`: the chart sheaves are
  quasi-coherent.
* `Stacks.RelativeProj.Situation.isQuasicoherent_moduleSheaf`: **`ℳ̃` is quasi-coherent.**
* `Stacks.RelativeProj.Situation.isQuasicoherent_twistSheaf`: **`𝒪_{Proj(s)}(n)` is
  quasi-coherent.**

## Implementation notes

The decomposition of the module of sections of a graded module over an affine open of the base is
a definition rather than an instance, so it is installed as a local instance here, exactly as in
the construction of `ℳ̃` itself; without it the sheaf attached to the graded module of sections
does not elaborate.

Quasi-coherence of a chart sheaf is named rather than synthesized: Tag 01MB is an instance, but
its subject is the sheaf attached to a graded module and the two chart sheaves are that sheaf only
after unfolding an abbreviation whose own instance arguments — the decomposition of the grading
and the compatibility of the action with it — are not the ones instance search reconstructs.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)

## Not done here

No Stacks tag is carried. Quasi-coherence of `ℳ̃` is not one of the eight enumerated assertions of
Tag 01O7 — it is what their statements rest on — and none of those eight is proved here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.SheafOfModules
open scoped Stacks.GradedLocalization

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

/-- **The charts of a relative projective spectrum cover it**: a point lies in the chart over any
affine open of the base containing its image, and the affine opens of the base cover it. -/
public theorem iSup_opensRange_relativeProjChart (s : Situation.{u}) :
    ⨆ W : s.base.affineOpens, (relativeProjChart s W).opensRange = ⊤ :=
  (chartData s).iSup_opensRange_chartι

section Twist

variable (s : Situation.{u}) (n : ℤ)

/-- The absolute twisting sheaf `𝒪(n)` on a chart of a relative projective spectrum is
quasi-coherent, by Tag 01MB for the `n`-th regrading of the graded ring of sections. -/
public instance isQuasicoherent_twistChart (W : s.base.affineOpens) :
    (twistChart s n W).IsQuasicoherent :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_isQuasicoherent
    (s.sectionRingGrading W.1)
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (s.sectionRingGrading W.1) n)

/-- **`𝒪_{Proj(s)}(n)` is quasi-coherent.** It is glued from the absolute twisting sheaves of the
charts, each of which is quasi-coherent, and the charts cover the relative projective
spectrum. -/
public instance isQuasicoherent_twistSheaf : (twistSheaf s n).IsQuasicoherent :=
  (twistGlueData (twistTransition s n)).isQuasicoherent_glued
    (iSup_opensRange_relativeProjChart s) fun W => isQuasicoherent_twistChart s n W

end Twist

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- The sheaf attached to `ℳ` on a chart of a relative projective spectrum is quasi-coherent, by
Tag 01MB for the graded module of sections of `ℳ` over the affine open. -/
public instance isQuasicoherent_moduleChart (W : s.base.affineOpens) :
    (moduleChart ℳ W).IsQuasicoherent :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_isQuasicoherent
    (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)

/-- **`ℳ̃` is quasi-coherent.** It is glued from the sheaves attached to the graded modules of
sections of `ℳ` over the affine opens of the base, each of which is quasi-coherent on its chart,
and the charts cover the relative projective spectrum. -/
public instance isQuasicoherent_moduleSheaf : (moduleSheaf ℳ).IsQuasicoherent :=
  (modulesDirectedGlueData ℳ).isQuasicoherent_glued
    (iSup_opensRange_relativeProjChart s) fun W => isQuasicoherent_moduleChart ℳ W

end Stacks.RelativeProj.Situation

end
