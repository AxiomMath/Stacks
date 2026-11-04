module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafFunctorial
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Stalk

/-!
# Exactness of the sheaf attached to a graded module on a relative projective spectrum

Let `s` be a relative `Proj` situation and let `ℳ ⟶ 𝒩 ⟶ 𝒬` be homomorphisms of graded modules
over its graded algebra with quasi-coherent homogeneous pieces, so that the sheaves `ℳ̃`, `𝒩̃`,
`𝒬̃` of `StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheaf.lean` and the
induced morphisms of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafFunctorial.lean` are
defined. This file shows that `ℳ̃ ⟶ 𝒩̃ ⟶ 𝒬̃` is a short exact sequence of sheaves of modules on
the relative projective spectrum as soon as the graded modules of local sections over the affine
opens of the base form short exact sequences.

The argument is the one the source indicates: exactness is local, on the chart over an affine
open `W` of the base the sheaf `ℳ̃` is the sheaf attached to the graded module of sections of `ℳ`
over `W`, and the associated-sheaf construction on an absolute projective spectrum is exact,
which is [Stacks, Tag 01M7]. The two halves of "local" are
`Stacks.SheafOfModules.ModulesDirectedGlueData.shortExact_glued` — short exactness of a complex
of glued sheaves of modules follows from short exactness of its complexes of chart sheaves, via
the comparison of stalks — and
`Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart`, that the charts cover.

## Main definitions

* `Stacks.RelativeProj.Situation.sectionGradedModule`: the graded module of local sections over an
  affine open of the base, as an object of the category of graded modules over the graded ring of
  sections there.
* `Stacks.RelativeProj.Situation.sectionGradedModuleMap`: the induced morphism of those graded
  modules.

## Main results

* `Stacks.RelativeProj.Situation.exists_relativeProjChart_eq`: every point of the relative
  projective spectrum lies in a chart.
* `Stacks.RelativeProj.Situation.moduleChartMap_comp_eq_zero` and
  `Stacks.RelativeProj.Situation.moduleSheafMap_comp_eq_zero`: a composable pair of homomorphisms
  whose composite vanishes on the sections over each affine open of the base induces a complex of
  chart sheaves, respectively of glued sheaves.
* `Stacks.RelativeProj.Situation.shortExact_moduleChartMap`: the complex of chart sheaves over an
  affine open is short exact when the complex of graded modules of sections there is.
* `Stacks.RelativeProj.Situation.shortExact_moduleSheafMap`: **the complex `ℳ̃ ⟶ 𝒩̃ ⟶ 𝒬̃` is short
  exact when the complexes of graded modules of local sections over the affine opens of the base
  are.**

## Implementation notes

The boundary between `(AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Modules`, in which the
chart sheaves live, and the category of sheaves of modules over the composed structure sheaf, in
which Tag 01M7's exactness is stated, is crossed once per statement by a single `exact` with
every argument explicit. Rewriting across it instead re-pays an expensive unification at each
step.

`Stacks.RelativeProj.Situation.sectionGradedModule` packages the graded module of sections as an
object of `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat`; the two instances it
needs are `Stacks.RelativeProj.Situation.sectionModuleDecomposition`, installed as a local
instance here as it is in the construction of `ℳ̃`, and
`Stacks.RelativeProj.Situation.sectionModuleGradedSMul`. With that packaging the morphism of
chart sheaves `Stacks.RelativeProj.Situation.moduleChartMap` *is* the associated-sheaf functor
applied to the morphism of graded modules, by `rfl`.

**The universes are forced, not chosen.** Everything is at the diagonal: the base scheme, the
graded algebra, the graded module and its sections all live in one universe `u`. That is
inherited from the stalkwise criterion. Mathlib's `TopCat.Presheaf.stalkFunctor C x` ties the
universe of the space to the hom universe of `C`, so the criterion that short exactness of a
complex of sheaves of modules is measured on stalks exists only when the modules live in the
universe of the space; the same constraint is recorded in
`StacksFrontier/AlgebraicGeometry/ProjStalkGlobalSections/Stalk.lean` and
`StacksFrontier/AlgebraicGeometry/ProjSheafFunctoriality/Exactness.lean`. The graded modules of
`Stacks.SheafOfModules.LeftGradedModule` over a situation are already taken at the diagonal in
the construction of `ℳ̃`, so nothing is narrowed here.

The hypotheses are injectivity, exactness and surjectivity of the induced maps of the graded
modules of local sections over each affine open of the base, rather than short exactness of
`ℳ ⟶ 𝒩 ⟶ 𝒬` itself. See the final section.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)

## Not done here

No Stacks tag is carried. Property (5) of Tag 01O7 asserts that `ℳ ↦ ℳ̃` carries a short exact
sequence of quasi-coherent graded `𝒜`-modules to a short exact sequence of sheaves of modules.
What is proved here takes short exactness of the sequences of graded modules of local sections
over the affine opens of the base, and the step from the former to the latter — exactness of
`Γ(W, -)` on quasi-coherent modules over an affine open `W`, applied in each degree, followed by
the passage from the degrees to their direct sum — is not proved here. Its inputs are
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` and
`Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel`, neither of which is used in this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}}
  {ℳ 𝒩 𝒬 : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}

/-! ### The graded module of sections as an object of the category of graded modules -/

/-- The graded module of local sections of `ℳ` over an affine open `W` of the base, as an object
of the category of graded modules over the graded ring of sections of the algebra over `W`. -/
public def sectionGradedModule
    (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
    (W : s.base.affineOpens) : GradedModuleCat.{u, u, u} (s.sectionRingGrading W.1) where
  carrier := sectionModule ℳ W.1
  grade := sectionModuleGrading ℳ W.1

/-- **The morphism of graded modules of local sections** induced by a homomorphism of graded
modules, as a morphism in the category of graded modules. -/
public def sectionGradedModuleMap (f : ℳ ⟶ 𝒩) (W : s.base.affineOpens) :
    sectionGradedModule ℳ W ⟶ sectionGradedModule 𝒩 W :=
  ⟨sectionModuleMapₗ f W.1, sectionModuleMapₗ_mem_grading f W.1⟩

/-- The sheaf attached to `ℳ` on the chart over `W` is the sheaf the associated-sheaf functor of
Tag 01M7 attaches to the graded module of sections of `ℳ` over `W`. -/
public theorem associatedModuleSheafFunctor_obj_sectionGradedModule
    (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
    (W : s.base.affineOpens) :
    (associatedModuleSheafFunctor (s.sectionRingGrading W.1)).obj (sectionGradedModule ℳ W) =
      moduleChart ℳ W := rfl

/-- The morphism of the chart sheaves over `W` is the morphism the associated-sheaf functor of
Tag 01M7 attaches to the morphism of the graded modules of sections over `W`. -/
public theorem associatedModuleSheafFunctor_map_sectionGradedModuleMap (f : ℳ ⟶ 𝒩)
    (W : s.base.affineOpens) :
    (associatedModuleSheafFunctor (s.sectionRingGrading W.1)).map (sectionGradedModuleMap f W) =
      moduleChartMap f W := rfl

/-! ### The charts cover -/

/-- **Every point of a relative projective spectrum lies in the chart over some affine open of the
base.** This is `Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart` read at a
point. -/
public theorem exists_relativeProjChart_eq (s : Situation.{u}) (x : relativeProj s) :
    ∃ (W : s.base.affineOpens) (y : AlgebraicGeometry.Proj (s.sectionRingGrading W.1)),
      (relativeProjChart s W) y = x := by
  have hx : x ∈ (⨆ W : s.base.affineOpens, (relativeProjChart s W).opensRange) := by
    rw [iSup_opensRange_relativeProjChart s]; trivial
  obtain ⟨W, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨W, y, hy⟩

/-! ### Complexes of chart sheaves and of glued sheaves -/

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]
  [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]
  [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] in
/-- **A composable pair of homomorphisms of graded modules whose composite vanishes on the graded
module of sections over an affine open `W` of the base induces a complex of the chart sheaves over
`W`.** This is Tag 01M7's statement that the associated-sheaf construction carries a vanishing
composite to a complex. -/
public theorem moduleChartMap_comp_eq_zero (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬) (W : s.base.affineOpens)
    (hz : ∀ z : sectionModule ℳ W.1,
      sectionModuleMapₗ g W.1 (sectionModuleMapₗ f W.1 z) = 0) :
    moduleChartMap f W ≫ moduleChartMap g W = 0 :=
  associatedModuleSheafFunctor_map_comp_eq_zero (sectionGradedModuleMap f W)
    (sectionGradedModuleMap g W) hz

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]
  [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] in
/-- **The complex of the chart sheaves over `W` is short exact** when the complex of graded
modules of sections over `W` is. This is the exactness of the associated-sheaf construction on an
absolute projective spectrum, [Stacks, Tag 01M7]. -/
public theorem shortExact_moduleChartMap (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬) (W : s.base.affineOpens)
    (hinj : Function.Injective (sectionModuleMapₗ f W.1))
    (hsurj : Function.Surjective (sectionModuleMapₗ g W.1))
    (hexact : Function.Exact (sectionModuleMapₗ f W.1) (sectionModuleMapₗ g W.1))
    (hcomp : moduleChartMap f W ≫ moduleChartMap g W = 0) :
    (ShortComplex.mk (moduleChartMap f W) (moduleChartMap g W) hcomp).ShortExact :=
  associatedModuleSheafFunctor_shortExact (sectionGradedModuleMap f W)
    (sectionGradedModuleMap g W) hinj hsurj hexact

/-- **A composable pair of homomorphisms of graded modules whose composite vanishes on the graded
module of sections over every affine open of the base induces a complex of the attached
sheaves.** -/
public theorem moduleSheafMap_comp_eq_zero (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬)
    (hz : ∀ (W : s.base.affineOpens) (z : sectionModule ℳ W.1),
      sectionModuleMapₗ g W.1 (sectionModuleMapₗ f W.1 z) = 0) :
    moduleSheafMap f ≫ moduleSheafMap g = 0 :=
  ((modulesDirectedGlueHom f).glued_comp (modulesDirectedGlueHom g)).symm.trans
    (((modulesDirectedGlueHom f).comp (modulesDirectedGlueHom g)).glued_eq_zero
      fun W => moduleChartMap_comp_eq_zero f g W (hz W))

/-- **A step towards Tag 01O7, property (5).** **The complex `ℳ̃ ⟶ 𝒩̃ ⟶ 𝒬̃` of sheaves of
modules on the relative projective spectrum is short exact** when the complexes of graded modules
of local sections over the affine opens of the base are short exact.

Short exactness of a complex of glued sheaves of modules is short exactness of its complexes of
chart sheaves, by `Stacks.SheafOfModules.ModulesDirectedGlueData.shortExact_glued`, and on the
chart over an affine open `W` the complex is the one the associated-sheaf construction of Tag
01M7 attaches to the complex of graded modules of sections over `W`. -/
public theorem shortExact_moduleSheafMap (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬)
    (hinj : ∀ W : s.base.affineOpens, Function.Injective (sectionModuleMapₗ f W.1))
    (hsurj : ∀ W : s.base.affineOpens, Function.Surjective (sectionModuleMapₗ g W.1))
    (hexact : ∀ W : s.base.affineOpens,
      Function.Exact (sectionModuleMapₗ f W.1) (sectionModuleMapₗ g W.1))
    (hz : ∀ (W : s.base.affineOpens) (z : sectionModule ℳ W.1),
      sectionModuleMapₗ g W.1 (sectionModuleMapₗ f W.1 z) = 0) :
    (ShortComplex.mk (moduleSheafMap f) (moduleSheafMap g)
      (moduleSheafMap_comp_eq_zero f g hz)).ShortExact :=
  ModulesDirectedGlueData.shortExact_glued (modulesDirectedGlueHom f) (modulesDirectedGlueHom g)
    (fun W => moduleChartMap_comp_eq_zero f g W (hz W))
    (fun x => by
      obtain ⟨W, y, hy⟩ := exists_relativeProjChart_eq s x
      exact ⟨W, y, hy⟩)
    fun W => shortExact_moduleChartMap f g W (hinj W) (hsurj W) (hexact W)
      (moduleChartMap_comp_eq_zero f g W (hz W))

end Stacks.RelativeProj.Situation

end
