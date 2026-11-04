module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of cohomology with compact support over an algebraically closed field

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` and `Λ`
a Noetherian ring. If `K ∈ D⁺_{tors,c}(X_étale, Λ)`, or `K ∈ D_c(X_étale, Λ)` with `Λ` torsion,
then every `Hⁱ_c(X, K)` is a finite `Λ`-module.

Here `Hⁱ_c(X, K) = Hⁱ(RΓ(Spec k, Rf_! K))` for the structure morphism `f : X ⟶ Spec k` and a
compactification of it (`Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` and
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupUnbounded`). The scheme `X` is a scheme
of a big étale site `B`, constructibility being defined on the small étale site of Stacks 021B
inside `B`.

## Main results

* `Stacks.EtaleCohomology.module_finite_compactlySupportedCohomologyGroup_of_isConstructible`:
  `Hⁱ_c(X, K)` is a finite `Λ`-module for `K` with constructible (torsion) cohomology sheaves.

## References

* [Stacks Project, Tag 0GLH](https://stacks.math.columbia.edu/tag/0GLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [-instance] hasSheafifyEtale

/-- Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` (a
scheme of a big étale site `B`, with structure morphism `f`), `j` a compactification of `X` over
`k`, through which `Hⁱ_c(X, -)` is formed, and `Λ` a Noetherian ring.
1. If `K ∈ D⁺(X_étale, Λ)` has constructible torsion cohomology sheaves, every `Hⁱ_c(X, K)` is a
   finite `Λ`-module.
2. If `Λ` is torsion and `K ∈ D(X_étale, Λ)` has constructible cohomology sheaves, every
   `Hⁱ_c(X, K)` is a finite `Λ`-module. -/
@[stacks 0GLH "both cases: K in D+_{tors,c}(X, Λ), and K in D_c(X, Λ) when Λ is torsion \
(m = 0 in Λ for some m > 0; H^i_c on D(X, Λ) is compactlySupportedCohomologyGroupUnbounded); \
H^i_c through any compactification j of X over k", sga "4 XVII 5.3.8" "special case"]
theorem module_finite_compactlySupportedCohomologyGroup_of_isConstructible
    {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj),
      (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
        IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ i : ℤ, Module.Finite Λ ((compactlySupportedCohomologyGroup.{u, 0} k f j Λ i).obj K)) ∧
    ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) →
      ∀ K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.homologyFunctor _ q).obj K)) →
        ∀ i : ℤ, Module.Finite Λ
          ((compactlySupportedCohomologyGroupUnbounded.{u, 0} k f j Λ i).obj K)) := by
  rcases isEmpty_or_nonempty X.obj with hX | ⟨⟨x⟩⟩
  · refine ⟨fun K _ i => ?_, fun _ K _ i => ?_⟩
    · have := ModuleCat.isZero_iff_subsingleton.1
        (isZero_compactlySupportedCohomologyGroup_of_isEmpty k f j Λ K i)
      infer_instance
    · have := ModuleCat.isZero_iff_subsingleton.1
        (isZero_compactlySupportedCohomologyGroupUnbounded_of_isEmpty k f j Λ K i)
      infer_instance
  · have hk : B.Contains (Spec (.of k)) := contains_spec_field_of_nonempty k f B X.property x
    have h := isConstructibleTorsion_homology_derivedLowerShriek_of_isConstructible B
      (Y := B.obj (Spec (.of k)) hk) f j Λ
    refine ⟨fun K hK i =>
        module_finite_homology_etaleModuleDerivedGlobalSections_of_isConstructibleModuleSheaf B k hk
          Λ _ (fun q => (h.1 K hK q).1) i, fun hΛ K hK i => ?_⟩
    exact
      module_finite_homology_etaleModuleDerivedGlobalSectionsUnbounded_of_isConstructibleModuleSheaf
        B k hk Λ _ (fun q => h.2 hΛ K hK q) i

end Stacks.EtaleCohomology

end
