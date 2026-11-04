module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension

/-!
# Extension by zero, and `Rf_!` through a finite compactification, preserve constructibility

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_extensionByZero`: **Stacks 03S8** on
  Mathlib's small étale site for a quasi-compact open immersion `j : U ⟶ X` into a quasi-compact
  and quasi-separated scheme: `j_! G` is constructible when `G` is. Constructibility is checked on
  the stratification `X = U ⊔ Z` (Stacks 09YR): `j⁻¹ j_! G ≅ G` and `i⁻¹ j_! G = 0`.
* `isConstructibleEtaleModule_rightDerived_directImage_extensionByZero_of_isFinite`:
  for a compactification `j : X ⟶ X̄` of `f` whose structure morphism `f̄` is finite and of
  finite presentation, every `R^p f̄_*(j_! F)` is constructible for `F` constructible: `f̄_*` is
  exact (so `R^p f̄_* = 0` for `p > 0`) and `f̄_* j_! F` is constructible by Stacks 095R. This is
  the sheaf-level core of Stacks 0GK3 for the derived lower shriek, through a compactification of
  the shape Zariski's main theorem provides for a quasi-finite separated morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section ExtensionByZero

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- A zero sheaf is constructible, on Mathlib's small étale site. -/
theorem isConstructibleEtaleModule_of_isZero (X : B.Scheme) {G : EtaleModules.{u, r} Λ X.obj}
    (hG : IsZero G) : IsBigSiteConstructibleEtaleModule B X Λ G :=
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  (IsBigSiteConstructibleEtaleModule B X Λ).prop_of_isZero hG

variable {X U Z : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [CompactSpace U.obj]
  (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
  [IsClosedImmersion (B.inclusion.map i)]
  (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)

include hij

/-- **Stacks 03S8 on Mathlib's small étale site, for a quasi-compact open immersion.** -/
theorem isConstructibleEtaleModule_extensionByZero {G : EtaleModules.{u, r} Λ U.obj}
    (hG : IsBigSiteConstructibleEtaleModule B U Λ G) :
    IsBigSiteConstructibleEtaleModule B X Λ
      ((etaleModuleExtensionByZero.{u, r} Λ (B.inclusion.map j)).obj G) := by
  have hjc := isConstructible_range_of_compactSpace B (Z := Z) j i hij
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B X Λ _ (I := Bool)
    (fun b => match b with | true => U | false => Z)
    (fun b => match b with | true => j | false => i) ?_ ?_ ?_ ?_
  · intro b
    cases b
    · exact inferInstanceAs (IsImmersion (B.inclusion.map i))
    · exact inferInstanceAs (IsImmersion (B.inclusion.map j))
  · intro b
    cases b
    · show Topology.IsConstructible (Set.range (B.inclusion.map i).base)
      rw [← compl_compl (Set.range (B.inclusion.map i).base), ← hij]
      exact hjc.compl
    · exact hjc
  · refine (Set.eq_univ_of_forall fun x => ?_).symm
    by_cases hx : x ∈ Set.range (B.inclusion.map j).base
    · exact Set.mem_iUnion.2 ⟨true, hx⟩
    · rw [hij, Set.mem_compl_iff, not_not] at hx
      exact Set.mem_iUnion.2 ⟨false, hx⟩
  · intro b
    cases b
    · refine isConstructibleModuleSheaf_congr B Λ _
        (etaleModulesToSmallEtalePullbackIso B Λ i _) ?_
      exact isConstructibleEtaleModule_of_isZero B Λ Z
        (isZero_etaleModuleInverseImage_extensionByZero Λ _ _ hij G)
    · refine isConstructibleModuleSheaf_congr B Λ _
        (etaleModulesToSmallEtalePullbackIso B Λ j _) ?_
      refine IsBigSiteConstructibleEtaleModule.of_iso B Λ ?_ hG
      exact (asIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ (B.inclusion.map j)).unit.app G)) ≪≫
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (B.inclusion.map j)).app _).symm

end ExtensionByZero

section FiniteCompactification

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The sheaf-level core of Stacks 0GK3 through a finite compactification.** Let `j : U ⟶ X̄` be
a quasi-compact open immersion with closed complement `i : Z ⟶ X̄` and `f̄ : X̄ ⟶ Y` finite and
of finite presentation, all in `B`, with `X̄` quasi-compact and quasi-separated. Then for every
constructible `F` on `U` and every `p`, `R^p f̄_*(j_! F)` is constructible. -/
theorem isConstructibleEtaleModule_rightDerived_directImage_extensionByZero_of_isFinite
    {X U Z Y : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [CompactSpace U.obj]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    [IsClosedImmersion (B.inclusion.map i)]
    (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)
    (fbar : X ⟶ Y) [IsFinite (B.inclusion.map fbar)]
    [LocallyOfFinitePresentation (B.inclusion.map fbar)]
    {F : EtaleModules.{u, 0} Λ U.obj} (hF : IsBigSiteConstructibleEtaleModule B U Λ F) (p : ℕ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      (((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map fbar)).rightDerived p).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (B.inclusion.map j)).obj F)) := by
  rcases p with _ | p
  · refine IsBigSiteConstructibleEtaleModule.of_iso B Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map fbar)).rightDerivedZeroIsoSelf.app
        _).symm ?_
    exact isConstructibleEtaleModule_directImage_of_isFinite B Λ fbar
      (isConstructibleEtaleModule_extensionByZero B Λ j i hij hF)
  · exact isConstructibleEtaleModule_of_isZero B Λ Y
      (isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom Λ (B.inclusion.map fbar) _
        (p + 1) (by omega))

end FiniteCompactification

end Stacks.EtaleCohomology

end
