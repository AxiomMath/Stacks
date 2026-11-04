module

public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheaf

/-!
# The unit-fraction chart sections of the sheaf attached to a graded module on a relative `Proj`

Let `s` be a relative `Proj` situation and let `ℳ` be a graded module over its graded algebra
with quasi-coherent homogeneous pieces, so that the sheaf `ℳ̃` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheaf.lean` is defined. On
the chart over an affine open `W` of the base, a degree-zero element `m` of the graded module of
local sections over `W` names the global section `m / 1` of the chart sheaf, by
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections`.

This file proves that those sections are compatible with the comparisons of the chart sheaves
attached to an inclusion `W ≤ W'` of affine opens of the base: the comparison carries `m / 1` to
`(m|_W) / 1`. That is the glue square for the family of unit-fraction sections.

Both sides of the square are pointwise in the module fibres — the comparison by
`Stacks.RelativeProj.Situation.modulePushforwardMap_val`, the restriction in the chart sheaf by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_restrict_apply` and the
unit-fraction section by
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_apply`, all three by
`rfl` — so the square is one identity about the module fibre comparison: that it carries a
fraction with denominator `1` to a fraction with denominator `1`. That is `fibreMap_mk_one`
below.

## Main results

* `Stacks.ProjModuleComparison.fibreMap_mk_one`: the module fibre comparison of a graded ring
  homomorphism carries a unit fraction to a unit fraction.
* `Stacks.RelativeProj.Situation.modulePushforwardMap_degreeZeroToGlobalSections`: **the glue
  square** — the comparison of the chart sheaves carries the unit-fraction section of a
  degree-zero element to the unit-fraction section of its restriction.

## Implementation notes

The square is proved by `refine Subtype.ext (funext fun x => ?_)` followed by a single `exact` on
`fibreMap_mk_one`, with every argument explicit, and not by rewriting across the square: a
rewrite has to re-unify the boundary between `(AlgebraicGeometry.Proj _).Modules` and the sheaf
of modules over the composed structure sheaf at every step. This is the method that proved the
glue square of property (4) in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafFunctorial.lean`.

`fibreMap_mk_one` is stated in its own context over abstract graded rings, with `y` an arbitrary
point of `ProjectiveSpectrum ℬ` and `ProjectiveSpectrum.isPrime` a local instance, rather than at
the chart coercion. Instantiating `y := x.1` at the use site then needs no instance search, the
goal's instance being identified with the supplied one by proof irrelevance.

`Stacks.RelativeProj.Situation.sectionModuleDecomposition` is a `def`, so it is installed as a
local instance here as it is in the construction of `ℳ̃`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 0AG1](https://stacks.math.columbia.edu/tag/0AG1)

## Not done here

No Stacks tag is carried, because neither result below states a clause of one.

Property (3) of Tag 01O7 is the morphism `π^*ℳ_0 ⟶ ℳ̃` of sheaves of modules on the relative
projective spectrum, for `π` the structure morphism
`Stacks.RelativeProj.Situation.relativeProjToBase`. It is
`Stacks.RelativeProj.Situation.degreeZeroSheafMap`, in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafDegreeZeroMap.lean`,
constructed through the adjoint `ℳ_0 ⟶ π_*ℳ̃` from its sections over the affine opens of the base;
the square below is the compatibility of those sections with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjModuleComparison Stacks.SheafOfModules Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.ProjModuleComparison

variable {A B M N : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The module fibre comparison of a graded ring homomorphism carries a unit fraction to a unit
fraction**: `m / 1` goes to `f m / 1`.

This is the whole content of the glue square for the unit-fraction chart sections of the sheaf
attached to a graded module on a relative projective spectrum: both sides of that square are
pointwise in the module fibres, and at a point they are the two sides here. -/
public theorem fibreMap_mk_one (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (f : M →ₛₗ[φ.toRingHom] N) (y : ProjectiveSpectrum ℬ) (m : M) :
    fibreMap φ hφ f y
        (LocalizedModule.mk m
          (1 : (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl))
      = LocalizedModule.mk (f m) (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) := by
  rw [fibreMap_mk]
  exact congrArg (LocalizedModule.mk (f m)) (Subtype.ext (by simp))

end Stacks.ProjModuleComparison

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} {ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The comparison of the chart sheaves carries a unit-fraction section to a unit-fraction
section.** For an inclusion `W ≤ W'` of affine opens of the base and a degree-zero element `m` of
the graded module of sections of `ℳ` over `W'`, the comparison attached to `W ≤ W'` carries the
section `m / 1` of the chart sheaf over `W'` to the section `(m|_W) / 1` of the chart sheaf over
`W`, both read on sections over an open `V` of the relative projective spectrum.

At a point of the chart over `W` the comparison is a module-fibre comparison and both sides are
fractions with denominator `1`, all by `rfl`, so the square is the one fibre identity of
`Stacks.ProjModuleComparison.fibreMap_mk_one`. -/
public theorem modulePushforwardMap_degreeZeroToGlobalSections
    {W W' : s.base.affineOpens} (h : W ≤ W') {V : (relativeProj s).Opens}
    (m : sectionModuleGrading ℳ W'.1 0) :
    ((modulePushforwardMap ℳ h).val.app (op V)).hom
        ((moduleChart ℳ W').val.map (homOfLE (le_top)).op
          (degreeZeroToGlobalSections (s.sectionRingGrading W'.1)
            (sectionModuleGrading ℳ W'.1) m))
      = (moduleChart ℳ W).val.map (homOfLE (le_top)).op
          (degreeZeroToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)
            ⟨sectionModuleRestrictₛₗ ℳ h m.1,
              sectionModuleRestrictₛₗ_mem_grading ℳ h 0 m.2⟩) := by
  refine Subtype.ext (funext fun x => ?_)
  exact fibreMap_mk_one (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (sectionModuleRestrictₛₗ ℳ h) x.1 m.1

end Stacks.RelativeProj.Situation

end
