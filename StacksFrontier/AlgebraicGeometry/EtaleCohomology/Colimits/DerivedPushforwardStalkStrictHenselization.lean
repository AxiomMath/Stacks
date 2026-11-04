module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationStalkDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# Stacks 03Q9: stalks of higher direct images and the strict henselization

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S` and
`p : X ×_S Spec 𝒪^{sh}_{S,s} ⟶ X` the projection. [Stacks, Tag 03Q9] asserts

* `(R^n f_* F)_s = H^n_ét(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹F)` for an abelian sheaf `F` on `X_étale`;
* `(R^n f_* K)_s = H^n_ét(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)` for `K ∈ D⁺(X_étale)` and `n ∈ ℤ`;
* `(Rf_* K)_s = RΓ_ét(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)` in `D⁺(Ab)`.

The comparison is the canonical map of [Stacks, Tag 0GIX],
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`. It is an isomorphism on
`D⁺` by `Stacks.EtaleCohomology.LimitExt.isIso_derivedPushforwardStalk_of_isGE_of_injective`, whose
two inputs are degree zero on injective sheaves
(`Stacks.EtaleCohomology.LimitExt.isIso_pushforwardStalkToStrictHenselizationSectionsAb_app`) and
the acyclicity of `p⁻¹I` for `I` injective
(`Stacks.EtaleCohomology.LimitExt.rightAcyclic_strictHenselizationPullback_of_injective`); both
come from [Stacks, Tag 09YQ] (in degree zero and in positive degrees) along the limit
`X ×_S Spec 𝒪^{sh}_{S,s} = lim X ×_S V` over the affine étale neighbourhoods `V` of `s`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE` —
  the third assertion.
* `Stacks.EtaleCohomology.stalkDerivedPushforwardHomologyIsoStrictHenselization` — the second.
* `Stacks.EtaleCohomology.stalkHigherDirectImageIsoStrictHenselization` — the first.
* `Stacks.EtaleCohomology.isIso_derivedPushforwardStalkToStrictHenselizationSections_single` — the
  canonical map at an abelian sheaf placed in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] (s : GeometricPoint S)

/-- **Stacks 03Q9, third assertion.** For `f : X ⟶ S` quasi-compact and quasi-separated, `s` a
geometric point of `S` and `p : X ×_S Spec 𝒪^{sh}_{S,s} ⟶ X` the projection, the canonical map
`(Rf_*K)_s ⟶ RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)` is an isomorphism for every bounded below complex
`K` of abelian sheaves on `X_étale`. -/
theorem isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app K) :=
  LimitExt.isIso_derivedPushforwardStalk_of_isGE_of_injective B hS f s
    (fun I hI => have := hI;
      LimitExt.rightAcyclic_strictHenselizationPullback_of_injective B hS f s I)
    (fun I _ => LimitExt.isIso_pushforwardStalkToStrictHenselizationSectionsAb_app B hS f s I) K n

/-- **Stacks 03Q9 at an abelian sheaf.** The canonical map
`(Rf_*G)_s ⟶ RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹G)` is an isomorphism for every abelian sheaf `G` on
`X_étale`, placed in degree zero. -/
theorem isIso_derivedPushforwardStalkToStrictHenselizationSections_single
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
      ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE B hS f s _ 0

/-- **Stacks 03Q9, second assertion.** For `K ∈ D⁺(X_étale)` and `n ∈ ℤ`,
`(R^n f_* K)_s ≅ H^n(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)`: the stalk at `s` of the `n`-th cohomology
sheaf of `Rf_*K` is the `n`-th cohomology of `RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)`, through the
canonical map. -/
def stalkDerivedPushforwardHomologyIsoStrictHenselization
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (m : ℤ) [K.IsGE m] (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj ((DerivedCategory.homologyFunctor _ n).obj
        ((smallEtaleDerivedPushforwardAb f).obj K)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K)) :=
  haveI := isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE B hS f s K m
  (((smallEtaleStalkAb s.hom).mapDerivedCategoryHomologyFunctorIso n).app
      ((smallEtaleDerivedPushforwardAb f).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
      (asIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app K))

/-- **Stacks 03Q9, first assertion.** For an abelian sheaf `F` on `X_étale` and `n ≥ 0`,
`(R^n f_* F)_s ≅ H^n_ét(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹F)`, the right side being the `n`-th right
derived functor of global sections on the small étale site of the base change. -/
@[sga "4 IX 4.1.1" "more general"]
def stalkHigherDirectImageIsoStrictHenselization (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (n : ℕ) :
    (smallEtaleStalkAb s.hom).obj ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
        ((smallEtaleDerivedPushforwardAb f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).rightDerived n).obj
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  haveI := isIso_derivedPushforwardStalkToStrictHenselizationSections_single B hS f s F
  haveI :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (strictHenselizationBaseChange B hS f s)
  (((smallEtaleStalkAb s.hom).mapDerivedCategoryHomologyFunctorIso (n : ℤ)).app
      ((smallEtaleDerivedPushforwardAb f).obj ((DerivedCategory.singleFunctor _ 0).obj F))).symm ≪≫
    (DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)).mapIso
      (asIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
        ((DerivedCategory.singleFunctor _ 0).obj F)) ≪≫
      (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).mapIso
        (((smallEtalePullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategorySingleFunctor
          0).app F)) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
      (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
      (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2})
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) n

end Stacks.EtaleCohomology
