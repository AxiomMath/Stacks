module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicCompleteComparisonBijective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineSectionsCompletionUnit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CompletionUnitDenseAnyDegree

/-!
# The canonical comparison `lim H^q(U, K)/IⁿH^q(U, K) ⟶ H^q(U, K^∧)` over an affine open

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals, `K` a
pseudo-coherent object of `D(𝒪_X)` and `U ⊂ X` an affine open, with `A = Γ(X, U)` and `I = ℐ(U)`.
Write `M = H^q(U, K)` and `T = H^q(U, K^∧)`, and let

`a = H^q(RΓ(U, η_K)) : M ⟶ T`

be `H^q` of the derived completion unit over `U`. This file proves that there is **exactly one**
`A`-linear map

`c : lim M/IⁿM ⟶ T`

restricting along the completion map to `a`, and that it is **bijective**. That is part (2) of
[Stacks, Tag 0A0K] over an affine open, read through a canonical map rather than an abstract
isomorphism.

## Why the canonical map, and why this direction

[Stacks, Tag 0A0L] is formalized as `Nonempty (T ≅ lim M/IⁿM)`, separately for each `U` and with
no compatibility with anything. A family of non-canonical isomorphisms is of no use to part (2),
which is a statement about *sheaves*: sheafification consumes a morphism of presheaves and
gluing on a basis consumes a compatible family. The canonical `c` is natural in `U` precisely
because it is unique, and that is what this file establishes.

The direction is forced. There is no canonical map `T ⟶ lim M/IⁿM`: on a derived tensor the
natural map runs `H^q(N) ⊗ A/Iⁿ ⟶ H^q(N ⊗^𝐋 A/Iⁿ)`, and it is only injective. The canonical map
runs *out of* the completion, by `Stacks.Algebraization.adicCompletionExtend`, which exists
because `T` is `I`-adically complete — a *property*, so it transports across the non-canonical
identification of [Stacks, Tag 0A0L] where a map would not.

## The two inputs

* **Density.** `a` is surjective modulo `I`. On the module side this is
  `Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree`, and
  carrying it to `a` needs the identification `RΓ(U, K^∧) ≅ RΓ(U, K)^∧` of [Stacks, Tag 0CQI]
  *compatibly with the units* — a statement about the image of a map cannot be transported
  otherwise. That is
  `Stacks.Algebraization.exists_iso_derivedSections_derivedCompletion_affine_unit`.
* **The abstract identification `θ`.** [Stacks, Tag 0A0L], used only for the two properties it
  transports: that `T` is `I`-adically complete, and that `T ⧸ Iⁿ • ⊤` is Noetherian. No map is
  transported across it.

## Main results

* `Stacks.Algebraization.range_homologyMap_derivedSections_derivedCompletionUnit_sup_smul_eq_top`
  — the density of `a` modulo `I`.
* `Stacks.Algebraization.existsUnique_bijective_adicComparison_homology_derivedSections` — the
  unique extension of `a` over the completion, and its bijectivity.

## Implementation notes

* Part (2) of [Stacks, Tag 0A0K] is a statement about sheaves. The canonical morphism
  `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor : K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` of `D(𝒪_X)`
  gives, after taking derived sections and `H^q`, a morphism of presheaves of modules on every
  open. The cohomology sheaves of `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` are quasi-coherent
  (`Stacks.Duality.isQuasicoherent_homology_derivedTensor`, [Stacks, Tag 08DX]), so their
  sections over an affine open are computed by
  `Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen`;
  the analogous identification `H^q(U, K^∧) ≅ Γ(U, H^q(K^∧))` is a consequence of part (2).
* The affine-local comparison for the adic reduction tower is
  `exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isPseudoCoherent`, and the
  passage between `lim_n` and sheafification is `PresheafOfModules.sheafificationLimitComparison`.
* On the module side, [Stacks, Tag 0CQI] and [Stacks, Tag 0EGV] give
  `H^q(U, K^∧) ≅ lim_n H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)`
  (`nonempty_iso_homology_derivedSections_derivedCompletion_limit_derivedReduction`) and the
  Mittag-Leffler property of that tower
  (`isMittagLefflerCategorical_derivedReduction_derivedSections_of_isAffineOpen`). These
  isomorphisms carry no compatibility with the projections or the completion map; any `A`-linear
  map out of the completion is determined by its restriction along `AdicCompletion.of`
  (`Stacks.Algebraization.eq_adicCompletionExtend`).

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0A0L](https://stacks.math.columbia.edu/tag/0A0L)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (opensRingedSite)
open Stacks.Cohomology.HypercohomologyEdge (derivedSections)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
  (K : DerivedCategory X.Modules) (U : X.affineOpens)

/-- **`H^q` of the derived completion unit over an affine open is surjective modulo `ℐ(U)`.**

The module-side statement
`Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree` applies to
`RΓ(U, K)`, whose cohomology modules are finite because `K` is pseudo-coherent and `X` is locally
Noetherian; and
`Stacks.Algebraization.exists_iso_derivedSections_derivedCompletion_affine_unit` carries it to
`H^q(RΓ(U, η_K))`, being an identification `RΓ(U, K)^∧ ≅ RΓ(U, K^∧)` that commutes with the two
units. -/
public theorem range_homologyMap_derivedSections_derivedCompletionUnit_sup_smul_eq_top
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).map
          ((derivedSections (structureSheafRing X.toRingedSpace) U.1).map
            ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).app K))).hom ⊔
        𝓘.ideal U • (⊤ : Submodule Γ(X, U.1)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
            ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj
              ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
                (idealSheafSiteSubmodule 𝓘)).obj K)))) = ⊤ := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hI : (𝓘.ideal U).FG := (𝓘.ideal U).fg_of_isNoetherianRing
  obtain ⟨ε, hε⟩ := exists_iso_derivedSections_derivedCompletion_affine_unit 𝓘 U K
    (Dualizing.derivedCompletion Γ(X, U.1) (𝓘.ideal U) hI)
    (adicCompletionAdjunction Γ(X, U.1) (𝓘.ideal U) hI)
  refine range_sup_smul_eq_top_of_linearEquiv (𝓘.ideal U) _ _ (LinearEquiv.refl _ _)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).mapIso ε).toLinearEquiv
    (fun m => ?_)
    (range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree Γ(X, U.1) (𝓘.ideal U) hI
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)
      (fun n => finite_homology_derivedSections_of_isPseudoCoherent X K hK U n) q)
  have hmap : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).map
        ((adicCompletionUnit Γ(X, U.1) (𝓘.ideal U) hI).app
          ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).mapIso ε).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).map
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).map
          ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).app K)) := by
    rw [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg _ hε
  exact congrArg (fun t : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K)) => t.hom m) hmap

/-- **The canonical comparison over an affine open, and its invertibility.** With `A = Γ(X, U)`,
`I = ℐ(U)`, `M = H^q(U, K)` and `T = H^q(U, K^∧)`, and `a = H^q(RΓ(U, η_K))`, there is exactly
one `A`-linear map

`c : lim M/IⁿM ⟶ T`

with `c ∘ (M ⟶ lim M/IⁿM) = a`, and it is bijective.

This is part (2) of [Stacks, Tag 0A0K] over an affine open, read through a canonical map. `c` is
`Stacks.Algebraization.adicCompletionExtend`, available because `T` is `I`-adically complete;
its uniqueness is `Stacks.Algebraization.eq_adicCompletionExtend`, which is what makes it natural
in `U`; and its bijectivity is
`Stacks.Algebraization.bijective_adicCompletionExtend`, whose two inputs are the density of `a`
and the abstract identification of [Stacks, Tag 0A0L], the latter used only for the properties it
transports. -/
public theorem existsUnique_bijective_adicComparison_homology_derivedSections
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    let Hq := fun (L : DerivedCategory X.Modules) ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj L)
    let Kc := (AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule 𝓘)).obj K
    let a : Hq K →ₗ[Γ(X, U.1)] Hq Kc :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).map
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).map
        ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule 𝓘)).app K))).hom
    ∃ c : AdicCompletion (𝓘.ideal U) (Hq K) →ₗ[Γ(X, U.1)] Hq Kc,
      (∀ m, c (AdicCompletion.of (𝓘.ideal U) (Hq K) m) = a m) ∧ Function.Bijective c ∧
        ∀ c' : AdicCompletion (𝓘.ideal U) (Hq K) →ₗ[Γ(X, U.1)] Hq Kc,
          (∀ m, c' (AdicCompletion.of (𝓘.ideal U) (Hq K) m) = a m) → c' = c := by
  intro Hq Kc a
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hI : (𝓘.ideal U).FG := (𝓘.ideal U).fg_of_isNoetherianRing
  have : Module.Finite Γ(X, U.1) (Hq K) :=
    finite_homology_derivedSections_of_isPseudoCoherent X K hK U q
  -- the abstract identification of [Stacks, Tag 0A0L], used only for the properties it transports
  obtain ⟨-, hw⟩ := exists_iso_homology_derivedSections_derivedCompletion_whole 𝓘 K U hK q
  obtain ⟨θ₀⟩ := (hw (Dualizing.derivedCompletion Γ(X, U.1) (𝓘.ideal U) hI)
    (adicCompletionAdjunction Γ(X, U.1) (𝓘.ideal U) hI)).1
  have θ : Hq Kc ≃ₗ[Γ(X, U.1)] AdicCompletion (𝓘.ideal U) (Hq K) := θ₀.toLinearEquiv
  have : IsAdicComplete (𝓘.ideal U) (Hq Kc) :=
    Stacks.Coherent.isAdicComplete_of_linearEquiv (𝓘.ideal U) θ
      (AdicCompletion.isAdicComplete hI)
  exact ⟨adicCompletionExtend (𝓘.ideal U) a, adicCompletionExtend_of (𝓘.ideal U) a,
    bijective_adicCompletionExtend (𝓘.ideal U) θ a
      (range_homologyMap_derivedSections_derivedCompletionUnit_sup_smul_eq_top 𝓘 K U hK q),
    fun c' hc' => eq_adicCompletionExtend (𝓘.ideal U) a c' hc'⟩

end Stacks.Algebraization

end
