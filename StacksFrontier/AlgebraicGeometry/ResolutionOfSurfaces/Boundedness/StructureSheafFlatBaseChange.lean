module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# Flat base change for the vanishing of `H¹(X, 𝒪_X)` over an affine base

Let

```
Y --p--> X
|        |
kY       iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, `q` flat and `iX` separated and
quasi-compact. If `H¹(X, 𝒪_X) = 0` then `H¹(Y, 𝒪_Y) = 0`.

This is the degree-one instance of flat base change that the vanishing arguments of the
resolution of surfaces need, in the spelling
`AlgebraicGeometry.FirstStructureSheafCohomologyVanishes` in which
`AlgebraicGeometry.DefinesRationalSingularity` asserts the vanishing.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `firstStructureSheafCohomologyVanishes_iff_isZero_rightDerivedEvaluation`: the two spellings of
  `H¹(X, 𝒪_X) = 0` — Mathlib's `CategoryTheory.Sheaf.H` of the abelian sheaf underlying `𝒪_X`,
  and the first right derived functor of module-valued global sections — agree.
* `firstStructureSheafCohomologyVanishes_of_isPullback`: the base change of the vanishing.

## Implementation notes

The change of model is the one assembled for
`AlgebraicGeometry.RationalSingularitySituation.isZero_firstCohomologyStructureSheaf`, which is
[Stacks, Tag 03FD]; there it is run in one direction at a fixed situation, and here it is run as
an equivalence at an arbitrary scheme, because the base change consumes the vanishing downstairs
and produces it upstairs. All three links of the chain are isomorphisms or
equivalences already, so nothing new is proved: `subsingleton_H_iff_subsingleton_H'_top`
replaces the global `Sheaf.H` by the value of Mathlib's cohomology presheaf at the terminal open,
`isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf` replaces that by the derived sections
of the module sheaf, and `rightDerivedEvaluationForgetIso` moves from the abelian-group-valued
model to the module-valued one. `IsZero` crosses the last step on carriers, through
`ModuleCat.isZero_iff_subsingleton` and `AddCommGrpCat.isZero_iff_subsingleton`.

The base change itself is `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso`, which holds in
every degree, applied to the structure sheaf. Three steps surround it. The left-hand side,
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} H¹(X, 𝒪_X)`, is zero because the two change-of-rings functors are additive
and so carry the zero object to the zero object. The right-hand side is read through restriction
of scalars along `Γ(T, ⊤) ⟶ Γ(Y, ⊤)`, which does not change the carrier, so its vanishing is the
vanishing of `H¹(Y, p^*𝒪_X)` — again on carriers, since `IsZero` in two different module
categories is two different statements. Finally `p^*𝒪_X ≅ 𝒪_Y`, which is
`Stacks.PullbackAlgebra.pullbackUnitIso`.

**No `@[stacks 02KH]` attribute is attached, and this file does not prove that tag.** The
hypothesis on `iX` is separatedness rather than quasi-separatedness, and the isomorphism supplied
by `nonempty_cohomologyBaseChangeIso` is not identified with the canonical base-change map of
[Stacks, Tag 02N7]; both points are recorded in the "What is not proved" section of the module
`FlatBaseChangeCohomology.AffinePositiveDegree`. What is below is the consequence of that
comparison for the structure sheaf in degree one, which is all the vanishing arguments use, and
it carries no hypothesis the comparison does not already have.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars)
open Stacks.Cohomology.ModuleComparison (rightDerivedEvaluationForgetIso
  isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf)
open Stacks.Cohomology.TerminalCohomology (subsingleton_H_iff_subsingleton_H'_top)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of the vanishing -/

/-- **The two models of `H¹(X, 𝒪_X) = 0` agree.** On the left is the spelling
`AlgebraicGeometry.DefinesRationalSingularity` uses, Mathlib's `CategoryTheory.Sheaf.H` of the
abelian sheaf underlying `𝒪_X`; on the right is the first right derived functor of module-valued
global sections, the spelling the Čech comparison and the flat base change are stated against.

This is [Stacks, Tag 03FD] together with the identification of the global `Sheaf.H` with the
value of the cohomology presheaf at the terminal open; both are available as equivalences, so
this is their composition. -/
public theorem firstStructureSheafCohomologyVanishes_iff_isZero_rightDerivedEvaluation
    (X : Scheme.{u}) :
    FirstStructureSheafCohomologyVanishes X ↔
      IsZero (((SheafOfModules.evaluation.{u} X.ringCatSheaf
        (op (⊤ : Opens X))).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  let _ : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have hiso := (rightDerivedEvaluationForgetIso
    X.ringCatSheaf (⊤ : Opens X) 1).app (SheafOfModules.unit X.ringCatSheaf)
  have hcomp := isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (Opens.grothendieckTopology X) X.ringCatSheaf (⊤ : Opens X) 1
    (SheafOfModules.unit X.ringCatSheaf)
  have hterm := subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) 1
  -- forgetting the module structure does not change the carrier, so `IsZero` crosses both ways
  exact hterm.trans (AddCommGrpCat.isZero_iff_subsingleton.symm.trans (hcomp.symm.trans
    (hiso.symm.isZero_iff.trans (AddCommGrpCat.isZero_iff_subsingleton.trans
      ModuleCat.isZero_iff_subsingleton.symm))))

/-! ### The base change -/

/-- **Flat base change for the vanishing of the first cohomology of the structure sheaf, over an
affine base.** For a cartesian square with `S` and `T` affine, `q` flat and `iX` separated and
quasi-compact, `H¹(X, 𝒪_X) = 0` implies `H¹(Y, 𝒪_Y) = 0`.

The comparison `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} H¹(X, 𝒪_X) ≅ H¹(Y, p^*𝒪_X)` is
`AlgebraicGeometry.nonempty_cohomologyBaseChangeIso`; its left-hand side is zero because the two
change-of-rings functors are additive, and its right-hand side is `H¹(Y, 𝒪_Y)` because
`p^*𝒪_X ≅ 𝒪_Y`. See the module docstring for why no `@[stacks 02KH]` attribute is attached. -/
public theorem firstStructureSheafCohomologyVanishes_of_isPullback {S T X Y : Scheme.{u}}
    [IsAffine S] [IsAffine T] {q : T ⟶ S} [Flat q] {iX : X ⟶ S} [IsSeparated iX]
    [QuasiCompact iX] {p : Y ⟶ X} {kY : Y ⟶ T} (H : IsPullback p kY iX q)
    (h : FirstStructureSheafCohomologyVanishes X) :
    FirstStructureSheafCohomologyVanishes Y := by
  have hX := (firstStructureSheafCohomologyVanishes_iff_isZero_rightDerivedEvaluation X).1 h
  obtain ⟨e⟩ := nonempty_cohomologyBaseChangeIso H (SheafOfModules.unit X.ringCatSheaf) 1
  have hR := ModuleCat.isZero_iff_subsingleton.1
    (((baseRestrictScalars iX ⋙ baseExtendScalars q).map_isZero hX).of_iso e.symm)
  have hY' : IsZero (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
      (op (⊤ : Opens Y))).rightDerived 1).obj
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    ModuleCat.isZero_iff_subsingleton.2 hR
  exact (firstStructureSheafCohomologyVanishes_iff_isZero_rightDerivedEvaluation Y).2
    (hY'.of_iso (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
      (op (⊤ : Opens Y))).rightDerived 1).mapIso
        (Stacks.PullbackAlgebra.pullbackUnitIso p.toLRSHom.toShHom)).symm)

end AlgebraicGeometry

end
