module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.IntegralHomCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.ModuleCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compactly supported cohomology through the closure in a compactification

Let `f : X ⟶ Spec k` be separated of finite type over a field and `j : X ⟶ X̄` a
compactification of `X` over `k`. This file supplies the reduction in the proof of
[Stacks, Tag 0GKR]: `H^q_c(X, F) = H^q(X̄, j_!F)`, and after replacing `X̄` by the
scheme-theoretic closure `Z̄` of `X` in it, `H^q_c(X, F) = H^q(Z̄, t_!F)` for the open immersion
`t : X ⟶ Z̄`, where `Z̄` is proper over `k`, has the dimension of `X`, and `t_!F` is constructible
and torsion whenever `F` is.

## Main results

* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupClosureIso`: for `n : ℕ`,
  `H^n_c(X, F) ≅ H^n(Z̄, t_!F)`, `Z̄` the scheme-theoretic closure of `X` in `X̄`.
* `Stacks.EtaleCohomology.topologicalKrullDim_closedSpace_le`: `dim Z̄ ≤ dim X`.

## Implementation notes

The first isomorphism `H^n_c(X, F) ≅ H^n(X̄, j_!F)` is the base's
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIso`. The second uses
`j_! = ι_* ∘ t_!` for the cartesian square of `AlgebraicGeometry.CompactificationOf.restrictClosed`
at the identity of `X`, and the collapse of cohomology across the closed immersion `ι : Z̄ ⟶ X̄`
(`Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso`).

## References

* [Stacks Project, Tag 0GKR](https://stacks.math.columbia.edu/tag/0GKR)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/- `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` is defined on the standard model
`HasDerivedCategory.standard` of the derived categories involved, so the complex `F[0]` it is
applied to below lives in that model: the instance is passed explicitly at each use. -/

-- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the module universe `u + 1`; its
-- unification against `ModuleCat.{max (u + 1) r}` fails with a universe error instead of
-- backtracking, so it is switched off here.
attribute [-instance] hasSheafifyEtale

/-! ### Passing to the closure of `X` in the compactification -/

section Closure

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

/-- The closure `Z̄` of `X` in a compactification `X̄` is proper over `k`. -/
instance isProper_closedSpaceι_comp_toBase :
    IsProper (j.closedSpaceι (𝟙 X) ≫ j.toBase) :=
  inferInstanceAs (IsProper (j.restrictClosed (𝟙 X)).toBase)

omit [IsSeparated f] in
/-- **The closure of `X` in a compactification has the dimension of `X` at most.** The open
immersion `t : X ⟶ Z̄` has dense image, the scheme-theoretic image being the closure of the image
of the quasi-compact morphism `j`, and a scheme of finite type over a field has dimension at
most that of a dense open subscheme. -/
@[ega "IV 10.6.2" "special case"]
theorem topologicalKrullDim_closedSpace_le :
    topologicalKrullDim (j.closedSpace (𝟙 X)) ≤ topologicalKrullDim X := by
  let t := (j.closedImmersion (𝟙 X)).toImage
  let q := j.closedSpaceι (𝟙 X) ≫ j.toBase
  have : IsLocallyNoetherian (j.closedSpace (𝟙 X)) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace (j.closedSpace (𝟙 X)) := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian (j.closedSpace (𝟙 X)) := ⟨⟩
  refine Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion
    k t f q ?_ ?_
  · simp [t, q]
  · exact IsDominant.denseRange (f := t)

variable (Λ : Type r) [CommRing Λ]

/-- **`j_! F = ι_* t_! F`** for the closure `ι : Z̄ ⟶ X̄` of `X` in the compactification and the
open immersion `t : X ⟶ Z̄`: the square of `𝟙 X`, `t`, `j` and `ι` is cartesian. -/
def etaleModuleExtensionByZeroClosureIso (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F ≅
      (etaleModuleDirectImage.{u, r} Λ (j.closedSpaceι (𝟙 X))).obj
        ((etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion (𝟙 X)).toImage).obj F) :=
  (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapIso
      ((etaleModuleDirectImageIdIso.{u, r} Λ X).app F).symm ≪≫
    (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ (𝟙 X) (j.closedImmersion (𝟙 X)).toImage
      j.immersion (j.closedSpaceι (𝟙 X)) (j.isPullback_restrictClosed (𝟙 X))).app F

/-- **`H^n_c(X, F) = H^n(Z̄, t_!F)`** for the scheme-theoretic closure `Z̄` of `X` in a
compactification `X̄` and the open immersion `t : X ⟶ Z̄`: by
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIso`, `j_! = ι_* ∘ t_!`, and the
collapse of étale cohomology across the closed immersion `ι : Z̄ ⟶ X̄`. -/
def compactlySupportedCohomologyGroupClosureIso (n : ℕ) (F : EtaleModules.{u, r} Λ X) :
    (compactlySupportedCohomologyGroup.{u, r} k f j Λ n).obj
        ((@DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) _ _
          (HasDerivedCategory.standard _) 0).obj F) ≅
      ((etaleModuleGlobalSections.{u, r} Λ (j.closedSpace (𝟙 X))).rightDerived n).obj
        ((etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion (𝟙 X)).toImage).obj F) :=
  compactlySupportedCohomologyGroupSingleIso Λ k f j n F ≪≫
    ((etaleModuleGlobalSections.{u, r} Λ j.space).rightDerived n).mapIso
      (etaleModuleExtensionByZeroClosureIso j Λ F) ≪≫
    (TorsionModules.moduleEtaleCohomology_isIntegralHom_iso Λ (j.closedSpaceι (𝟙 X)) n _).symm

end Closure

end Stacks.EtaleCohomology

end
