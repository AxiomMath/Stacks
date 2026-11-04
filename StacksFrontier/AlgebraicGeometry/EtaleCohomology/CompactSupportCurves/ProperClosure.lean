module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.DenseOpenDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.DerivedGlobalSectionsDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compactly supported cohomology through the closure in a compactification

Let `f : X ⟶ Spec k` be separated of finite type and `j : X ⟶ X̄` a compactification of `X` over
`k`. Let `Z ⊆ X̄` be the scheme-theoretic closure of `X`, with open immersion `ι : X ⟶ Z`. Then
`Z` is proper over `k`, and for every sheaf `ℱ` of `Λ`-modules on `X_étale`

`H^q_c(X, ℱ) ≅ H^q(Z, ι_! ℱ)`,

where the left-hand side is computed with `j` on the unbounded derived category. No comparison
between compactifications is needed: `Z ⟶ X̄` is a closed immersion, `j_! = (Z ⟶ X̄)_* ∘ ι_!`, and
the direct image along a closed immersion is exact.

When `X` is moreover of dimension at most one over an algebraically closed field, `Z` is a proper
curve: `dim Z = dim X` because `X` is a dense open of `Z`. This is the reduction of the finiteness
of `H^q_c` on a curve ([Stacks, Tag 0GKR]) to the finiteness of the cohomology of a proper curve
([Stacks, Tag 0GJI]).

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupUnboundedClosureIso`: the
  isomorphism `H^q_c(X, ℱ) ≅ H^q(Z, ι_! ℱ)`.

## Main results

* `Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleExtensionByZero`: extension by zero
  along an open immersion preserves torsion sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.exists_proper_compactlySupportedCohomology_iso`: for a curve `X` over
  an algebraically closed field and a compactification of it, the closure `Z` of `X` is a proper
  curve, `ι_!` preserves constructibility and torsion, and `H^q_c(X, ℱ) ≅ H^q(Z, ι_! ℱ)`.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
* [Stacks Project, Tag 0GKR](https://stacks.math.columbia.edu/tag/0GKR)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp in
/-- **Extension by zero along an open immersion preserves torsion sheaves of `Λ`-modules.**
Forgetting the module structure commutes with extension by zero, and the abelian extension by
zero of a torsion sheaf is torsion. -/
theorem isTorsionEtaleModule_etaleModuleExtensionByZero (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (F : EtaleModules.{u, r} Λ U)
    (hF : IsTorsionEtaleModule Λ U F) :
    IsTorsionEtaleModule Λ X ((etaleModuleExtensionByZero.{u, r} Λ j).obj F) :=
  Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
    (asIso ((etaleModuleExtensionByZeroForget.{u, r} Λ j).natTrans.app F))
    (torsionSheafProperty_extensionByZero.{u, r} j _ hF)

section Closure

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]

/-- **`H^q_c(X, ℱ) ≅ H^q(Z, ι_! ℱ)`** for the scheme-theoretic closure `Z` of `X` in the
compactification `j`, with `ι : X ⟶ Z` the induced open immersion. The derived lower shriek
through `j` restricted along the identity of `X` is the one through the compactification `ι`
of `X` by its closure (`derivedLowerShriekUnboundedRestrictClosedIso`); the derived global
sections over `k` of the derived direct image to `Spec k` are the derived global sections over
`Z`, and `Rι_!` is `ι_!`, which is exact. -/
@[sga "4½ Arcata 4.5.1" "H^q_c(X"]
def compactlySupportedCohomologyGroupUnboundedClosureIso (F : EtaleModules.{u, r} Λ X) (q : ℕ) :
    (compactlySupportedCohomologyGroupUnbounded.{u, r} k f j Λ q).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) ≅
      ((etaleModuleGlobalSections.{u, r} Λ (j.closedSpace (𝟙 X))).rightDerived q).obj
        ((etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion (𝟙 X)).toImage).obj F) :=
  let K := (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F
  let t := (j.closedImmersion (𝟙 X)).toImage
  let e₀ : ((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapDerivedCategory).obj K ≅ K :=
    ((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).mapIso
        ((etaleModuleDirectImageIdIso.{u, r} Λ X).app F)
  let e₁ : (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (j.closedSpaceι (𝟙 X) ≫ j.toBase)).obj
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ t).obj K) :=
    (derivedLowerShriekUnbounded.{u, r} f j Λ).mapIso e₀.symm ≪≫
      ((derivedLowerShriekUnboundedRestrictClosedIso.{u, r} Λ j (𝟙 X)).app K).symm
  let e₂ : (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ t).obj K ≅
      (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ (j.closedSpace (𝟙 X))) 0).obj
        ((etaleModuleExtensionByZero.{u, r} Λ t).obj F) :=
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ t).app K ≪≫
      ((etaleModuleExtensionByZero.{u, r} Λ t).mapDerivedCategorySingleFunctor 0).app F
  (DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) (q : ℤ)).mapIso
      ((etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k))).mapIso e₁ ≪≫
        ((etaleModuleDerivedGlobalSectionsUnboundedDirectImageIso.{u, r} Λ
          (j.closedSpaceι (𝟙 X) ≫ j.toBase)).app _).symm ≪≫
        (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (j.closedSpace (𝟙 X))).mapIso e₂) ≪≫
    (etaleModuleDerivedGlobalSectionsUnboundedSingleIso.{u, r} Λ (j.closedSpace (𝟙 X)) q).app
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj F)

end Closure

/-- **The compactly supported cohomology of a curve is the cohomology of a proper curve.** Let `X`
be separated of finite type and of dimension at most one over an algebraically closed field `k`,
and let `j` be a compactification of `X` over `k`. Let `Z` be the scheme-theoretic closure of `X`
in `j`, with open immersion `ι : X ⟶ Z`. Then `Z` is proper over `k` of dimension at most one,
extension by zero `ι_!` preserves constructibility and torsion, and for every sheaf `ℱ` of
`Λ`-modules on `X_étale`, `H^q_c(X, ℱ) ≅ H^q(Z, ι_! ℱ)` for all `q`. -/
theorem exists_proper_compactlySupportedCohomology_iso (Λ : Type r) [CommRing Λ]
    [IsNoetherianRing Λ] :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f],
      topologicalKrullDim X ≤ 1 → ∀ j : CompactificationOf (Over.mk f),
      ∃ (Z : Scheme.{u}) (πZ : Z ⟶ Spec (.of k)) (ι : X ⟶ Z) (_ : IsOpenImmersion ι),
        IsProper πZ ∧ topologicalKrullDim Z ≤ 1 ∧ ∀ F : EtaleModules.{u, r} Λ X,
          (IsConstructibleEtaleModule Λ F →
            IsConstructibleEtaleModule Λ ((etaleModuleExtensionByZero Λ ι).obj F)) ∧
          (IsTorsionEtaleModule Λ X F →
            IsTorsionEtaleModule Λ Z ((etaleModuleExtensionByZero Λ ι).obj F)) ∧
          ∀ q : ℕ, Nonempty ((compactlySupportedCohomologyGroupUnbounded.{u, r} k f j Λ q).obj
              ((DerivedCategory.singleFunctor (EtaleModules Λ X) 0).obj F) ≅
            ((etaleModuleGlobalSections Λ Z).rightDerived q).obj
              ((etaleModuleExtensionByZero Λ ι).obj F)) := by
  intro k _ _ X f _ _ _ hX j
  let ι := (j.closedImmersion (𝟙 X)).toImage
  let πZ := j.closedSpaceι (𝟙 X) ≫ j.toBase
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace (j.closedSpace (𝟙 X)) := QuasiCompact.compactSpace_of_compactSpace πZ
  have : QuasiSeparatedSpace (j.closedSpace (𝟙 X)) := quasiSeparatedSpace_of_quasiSeparated πZ
  refine ⟨j.closedSpace (𝟙 X), πZ, ι, inferInstance, inferInstance,
    (topologicalKrullDim_le_of_isOpenImmersion_of_denseRange k πZ ι
      (IsDominant.denseRange (f := ι))).trans hX, fun F ↦ ⟨fun hF ↦ ?_, fun hF ↦ ?_,
        fun q ↦ ⟨compactlySupportedCohomologyGroupUnboundedClosureIso k f j Λ F q⟩⟩⟩
  · exact isConstructibleEtaleModule_etaleModuleExtensionByZero Λ ι F hF
  · exact isTorsionEtaleModule_etaleModuleExtensionByZero Λ ι F hF

end Stacks.EtaleCohomology

end
