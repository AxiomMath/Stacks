module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GL0: `Rf_!` preserves `D⁺_{tors,c}` and, for torsion `Λ`, `D_c`

Let `f : X ⟶ Y` be a separated morphism of finite presentation of quasi-compact and
quasi-separated schemes and `Λ` a Noetherian ring. The constructibility of the cohomology sheaves
of `Rf_! K` is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible`.
That `Rf_!` keeps torsion cohomology sheaves torsion is
`Stacks.EtaleCohomology.isTorsionPlus_derivedLowerShriek_obj`: `j_!` does, and so does the derived
direct image along the proper morphism `X̄ ⟶ Y`. Together they give the statement of the source:
`Rf_! K ∈ D⁺_{tors,c}(Y_étale, Λ)` for `K ∈ D⁺_{tors,c}(X_étale, Λ)`, and
`Rf_! K ∈ D_c(Y_étale, Λ)` for `K ∈ D_c(X_étale, Λ)` when `Λ` is torsion.

## Main results

* `Stacks.EtaleCohomology.isConstructibleTorsion_homology_derivedLowerShriek_of_isConstructible`:
  Stacks 0GL0.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring

variable (B : BigEtaleSite.{u})

/-- **Stacks 0GL0.** Let `f : X ⟶ Y` be a separated morphism of finite presentation of schemes of
`B`, with `Y` quasi-compact and quasi-separated (hence so is `X`), `j` a compactification of `f`
(through which `Rf_! = Rf̄_* ∘ j_!`), and `Λ` a Noetherian ring.
1. If `K ∈ D⁺(X_étale, Λ)` has constructible torsion cohomology sheaves, then so has `Rf_! K`,
   i.e. `Rf_! K ∈ D⁺_{tors,c}(Y_étale, Λ)`.
2. If `Λ` is torsion and `K ∈ D(X_étale, Λ)` has constructible cohomology sheaves, so has
   `Rf_! K`, i.e. `Rf_! K ∈ D_c(Y_étale, Λ)`. -/
@[stacks 0GL0 "both cases: K in D+_{tors,c}(X, Λ), and K in D_c(X, Λ) when Λ is torsion \
(m = 0 in Λ for some m > 0; Rf_! on D(X, Λ) is derivedLowerShriekUnbounded); Rf_! through any \
compactification j of f"]
theorem isConstructibleTorsion_homology_derivedLowerShriek_of_isConstructible
    {X Y : B.Scheme} [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (f : X.obj ⟶ Y.obj)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj),
      (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
        IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ n : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((derivedLowerShriek.{u, 0} f j Λ).obj K)) ∧
        IsTorsionEtaleModule Λ Y.obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((derivedLowerShriek.{u, 0} f j Λ).obj K))) ∧
    ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) →
      ∀ K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.homologyFunctor _ q).obj K)) →
        ∀ n : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.homologyFunctor _ n).obj
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K))) := by
  have h := isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible B f j Λ
  refine ⟨fun K hK n => ⟨h.1 K hK n, ?_⟩, h.2⟩
  exact isTorsionPlus_derivedLowerShriek_obj Λ f j K (fun q => (hK q).2) n

end Stacks.EtaleCohomology

end
