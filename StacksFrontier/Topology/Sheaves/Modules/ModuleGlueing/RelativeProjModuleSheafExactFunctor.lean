module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DirectSum.MapExact
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafExact

/-!
# The construction of the sheaf attached to a graded module on a relative Proj is exact

Let `s` be a relative `Proj` situation and let `ℳ ⟶ 𝒩 ⟶ 𝒬` be a short exact sequence of graded
modules over its graded algebra, that is, a composable pair whose homogeneous pieces form short
exact sequences of sheaves of modules on the base, with those pieces quasi-coherent. This file
shows that the attached sheaves form a short exact sequence
`ℳ̃ ⟶ 𝒩̃ ⟶ 𝒬̃` of sheaves of modules on the relative projective spectrum, from which property (5)
of [Stacks, Tag 01O7] is deduced.

`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafExact.lean` reduces
that to short exactness of the sequences of *graded modules of local sections* over the affine
opens of the base. This file supplies those, in two steps. Over an affine open `W` the functor
`Γ(W, -)` is exact on quasi-coherent modules — left exactness holds over any open and is
`Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor`, while surjectivity on sections needs `W`
affine and is `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, the vanishing of the
first Čech cohomology of a quasi-coherent module on an affine — so each homogeneous degree gives
a short exact sequence of sections. The graded module of sections is the direct sum of those
degrees, and a direct sum of short exact sequences is short exact.

## Main results

* `Stacks.AlgebraicGeometry.QcohLimits.shortExact_app_of_isAffineOpen`: **a short exact sequence
  of quasi-coherent modules is short exact on sections over an affine open.**
* `Stacks.RelativeProj.Situation.sectionModuleMap_eq_directSumMap`: the induced map of the graded
  modules of local sections is the coordinatewise map of its degrees.
* `Stacks.RelativeProj.Situation.shortExact_sectionModuleMapₗ`: the induced maps of the graded
  modules of local sections over an affine open of the base form a short exact sequence.
* `Stacks.RelativeProj.Situation.shortExact_moduleSheafMap_of_shortExact`: **`ℳ ↦ ℳ̃` carries a
  short exact sequence of graded modules with quasi-coherent homogeneous pieces to a short exact
  sequence of sheaves of modules on the relative projective spectrum.**

## Implementation notes

Exactness of `Γ(W, -)` is assembled from the two halves that are available rather than from a
single statement, because they have different hypotheses: left exactness is
`PreservesFiniteLimits (Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor X W)`, which holds
for every open `W` and every sheaf of modules, read through Mathlib's
`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`; the right half is
surjectivity on sections, which is false for a general open and holds over an affine open by
Čech vanishing. `Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor` carries no
`CategoryTheory.Functor.Additive` instance, which that criterion needs; it is supplied here, and
holds by `rfl` because addition of morphisms of sheaves of modules is computed on sections.

The direct-sum step is `DirectSum.map_injective` and `DirectSum.map_surjective` from Mathlib
together with `DirectSum.exact_map` from
`StacksFrontier/Algebra/DirectSum/MapExact.lean`. To reach them the induced map of the graded
modules
of sections, which is built as `DirectSum.toAddMonoid` of the inclusions of the summands composed
with the degreewise maps, is identified with `DirectSum.map` of the degreewise maps; the two agree
on each summand, which is enough by `DirectSum.addHom_ext`.

The vanishing of the composite `ℳ̃ ⟶ 𝒩̃ ⟶ 𝒬̃` is not a separate hypothesis: it is read off the
exactness of the sections by `Function.Exact.apply_apply_eq_zero`.

**The universes are forced, not chosen.** Everything is at the diagonal, as in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafExact.lean`: Mathlib's
`TopCat.Presheaf.stalkFunctor C x` ties the universe of the space to the hom universe of `C`, so
the criterion that short exactness of a complex of sheaves of modules is measured on stalks — and
with it every form of Tag 01AG — exists only when the modules live in the universe of the space.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)

## Not done here

Exactness is stated here for a composable pair with its degreewise short exactness. The
statement for the functor between abelian categories — additive, preserving finite limits and
finite colimits — is property (5) of Tag 01O7 and is
`Stacks.RelativeProj.Situation.moduleSheafFunctor_exact` in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafExactAbelian.lean`,
where the quasi-coherent graded modules are given their abelian structure. Property (4), the
functoriality, is in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafFunctorial.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.QcohLimits

/-- Sections over an open are additive in the module, so the sections functor is additive. -/
instance instAdditiveSectionsFunctor {X : Scheme.{u}} (W : X.Opens) :
    (sectionsFunctor X W).Additive where
  map_add := rfl

/-- **A short exact sequence of quasi-coherent modules is short exact on sections over an affine
open.** Left exactness of `Γ(W, -)` holds over any open; surjectivity on sections is where the
affineness and the quasi-coherence are used, through the vanishing of the first Čech cohomology
of a quasi-coherent module on an affine. -/
theorem shortExact_app_of_isAffineOpen {X : Scheme.{u}} (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Injective (C.f.val.app (op W)) ∧
      Function.Exact (C.f.val.app (op W)) (C.g.val.app (op W)) ∧
        Function.Surjective (C.g.val.app (op W)) := by
  obtain ⟨hex, hmono⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sectionsFunctor X W)).1 inferInstance C hC
  have hepi : Epi C.g := hC.epi_g
  exact ⟨(AddCommGrpCat.mono_iff_injective _).1 hmono,
    (ShortComplex.ab_exact_iff_function_exact _).1 hex,
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X C.g W hW⟩

end Stacks.AlgebraicGeometry.QcohLimits

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}}
  {ℳ 𝒩 𝒬 : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}

/-! ### The graded module of sections is the direct sum of its degrees -/

/-- **The induced map of the graded modules of local sections is the direct sum of its degrees.**
It is built as the sum of the degreewise maps followed by the inclusions of the summands, and
that agrees on each summand with the coordinatewise map. -/
public theorem sectionModuleMap_eq_directSumMap (f : ℳ ⟶ 𝒩) (U : s.base.Opens) :
    sectionModuleMap f U = DirectSum.map (sectionModuleMapPiece f U) :=
  DirectSum.addHom_ext fun n x =>
    (sectionModuleMap_of f U x).trans (DirectSum.map_of _ n x).symm

/-- The linear form of the induced map of the graded modules of local sections, as a function, is
the coordinatewise map of the degrees. -/
public theorem sectionModuleMapₗ_coe_eq (f : ℳ ⟶ 𝒩) (U : s.base.Opens) :
    ⇑(sectionModuleMapₗ f U) = ⇑(DirectSum.map (sectionModuleMapPiece f U)) :=
  funext fun z => congrFun (congrArg DFunLike.coe (sectionModuleMap_eq_directSumMap f U)) z

/-! ### Short exactness of the sections over an affine open -/

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]
  [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent]

/-- **A short exact sequence of graded modules induces a short exact sequence of the graded
modules of local sections over an affine open of the base.** In each degree this is exactness of
`Γ(W, -)` on quasi-coherent modules over an affine open; the graded module of sections is the
direct sum of the degrees, and a direct sum of short exact sequences of additive groups is short
exact. -/
public theorem shortExact_sectionModuleMapₗ (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬)
    (hfg : ∀ n : ℤ, f.app n ≫ g.app n = 0)
    (hSE : SheafOfModules.LeftGradedModule.ShortExact f g hfg) (W : s.base.affineOpens) :
    Function.Injective (sectionModuleMapₗ f W.1) ∧
      Function.Exact (sectionModuleMapₗ f W.1) (sectionModuleMapₗ g W.1) ∧
        Function.Surjective (sectionModuleMapₗ g W.1) := by
  have hdeg := fun n : ℤ =>
    Stacks.AlgebraicGeometry.QcohLimits.shortExact_app_of_isAffineOpen _ (hSE n) W.2
  refine ⟨?_, ?_, ?_⟩
  · rw [sectionModuleMapₗ_coe_eq f W.1]
    exact (DirectSum.map_injective _).2 fun n => (hdeg n).1
  · rw [sectionModuleMapₗ_coe_eq f W.1, sectionModuleMapₗ_coe_eq g W.1]
    exact DirectSum.exact_map _ _ fun n => (hdeg n).2.1
  · rw [sectionModuleMapₗ_coe_eq g W.1]
    exact (DirectSum.map_surjective _).2 fun n => (hdeg n).2.2

/-! ### Exactness of the construction -/

/-- **The construction taking a graded module on a relative projective spectrum to its attached
sheaf carries short exact sequences to short exact sequences**: a degreewise short exact sequence
of graded modules with quasi-coherent homogeneous pieces goes to a short exact sequence of sheaves
of modules on the relative projective spectrum. The morphisms are those of the functor
`Stacks.RelativeProj.Situation.moduleSheafFunctor` of property (4). Property (5) of Tag 01O7, the
exactness of that functor between abelian categories, is
`Stacks.RelativeProj.Situation.moduleSheafFunctor_exact`, which is deduced from this.

Short exactness of the glued sheaves is short exactness of their complexes of chart sheaves, and
on the chart over an affine open `W` of the base the complex is the one attached by Tag 01M7 to
the sequence of graded modules of local sections over `W`, which is short exact because `Γ(W, -)`
is exact on quasi-coherent modules over an affine open. -/
public theorem shortExact_moduleSheafMap_of_shortExact (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬)
    (hfg : ∀ n : ℤ, f.app n ≫ g.app n = 0)
    (hSE : SheafOfModules.LeftGradedModule.ShortExact f g hfg) :
    (ShortComplex.mk (moduleSheafMap f) (moduleSheafMap g)
      (moduleSheafMap_comp_eq_zero f g fun W z =>
        (shortExact_sectionModuleMapₗ f g hfg hSE W).2.1.apply_apply_eq_zero z)).ShortExact := by
  have h := shortExact_sectionModuleMapₗ f g hfg hSE
  exact shortExact_moduleSheafMap f g (fun W => (h W).1) (fun W => (h W).2.2)
    (fun W => (h W).2.1) fun W z => (h W).2.1.apply_apply_eq_zero z

end Stacks.RelativeProj.Situation

end
