module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FullConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleRingEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TorsionCompactSupportFiniteness

/-!
# Stacks 0GKY, 0GKZ and 0GL0, and the constructibility of `Rf_!`

The results of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FullConstructible` with their
two hypotheses discharged: Stacks 0GKV over a Noetherian base
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`) and
Stacks 09YU, essential surjectivity
(`AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv`, along
`ULift Λ ≃ Λ`).

The statements are made in the standard model of the derived category
(`HasDerivedCategory.standard`), in which `Rf_!` and
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` are stated.

## Main results

* `Stacks.EtaleCohomology.lowerShriekConstructibilityInput`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible`
  : Stacks 0GL0.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine`:
  Stacks 0GKZ.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_openAffineLine`:
  Stacks 0GKY.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionCompactSupportFinitenessInput`: finiteness of
  `Hⁱ_c(X_k̄, F)` for constructible `ℓ`-power torsion `F`, any dimension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [-instance] hasSheafifyEtale

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- Stacks 0GKV over a Noetherian base
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`), in
the form of the hypothesis `h0GKV` of the constructibility results. -/
local macro "h0GKV%" : term =>
  `(fun _ _ f _ _ _ hdim _ ℓ _ q =>
    isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian _ f hdim ℓ q)


/-- Stacks 09YU (essential surjectivity,
`AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv` along
`ULift Λ ≃ Λ`), in the form of the hypothesis `h09YU` of the constructibility results. -/
local macro "h09YU%" : term =>
  `(fun Λ _ _ _ _ _ _ Dg c hX hc haff hqc hqs => by
    have := Stacks.ULiftTransport.isNoetherianRing_ulift (R := Λ)
    exact smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv _ Λ ULift.ringEquiv Dg c
      hX hc haff hqc hqs)

/-! ### Stacks 0GKY, 0GKZ, 0GL0 and the constructibility input -/

section Unconditional

variable (B : BigEtaleSite.{u})

/-- **`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` holds** (Stacks 0GL0 for sheaves
over a Noetherian base): for `f : X ⟶ Y` separated of finite type with `Y` Noetherian, a
Noetherian ring `Λ` and a constructible torsion sheaf `F` of `Λ`-modules on `X`, every cohomology
sheaf of `Rf_! F` is constructible. -/
theorem lowerShriekConstructibilityInput : LowerShriekConstructibilityInput B :=
  lowerShriekConstructibilityInput_of_stages B h0GKV% h09YU%

/-- **Stacks 0GL0.** Let `f : X ⟶ Y` be a separated morphism of finite presentation of schemes of
`B`, with `Y` quasi-compact and quasi-separated (hence so is `X`), `j` a compactification of `f`
(through which `Rf_! = Rf̄_* ∘ j_!`), and `Λ` a Noetherian ring.
1. If `K ∈ D⁺(X_étale, Λ)` has constructible torsion cohomology sheaves, so has `Rf_! K`.
2. If `Λ` is torsion and `K ∈ D(X_étale, Λ)` has constructible cohomology sheaves, so has
   `Rf_! K`. -/
@[stacks 0GL0 "both cases: K in D+_{tors,c}(X, Λ), and K in D_c(X, Λ) when Λ is torsion \
(m = 0 in Λ for some m > 0; Rf_! on D(X, Λ) is derivedLowerShriekUnbounded); Rf_! through any \
compactification j of f"]
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible
    {X Y : B.Scheme} [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (f : X.obj ⟶ Y.obj)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj),
      (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
        IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ n : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
        ((DerivedCategory.Plus.homologyFunctor _ n).obj ((derivedLowerShriek.{u, 0} f j Λ).obj
            K))) ∧
    ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) →
      ∀ K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.homologyFunctor _ q).obj K)) →
        ∀ n : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.homologyFunctor _ n).obj
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K))) :=
  ⟨fun K hK n => isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages B
      h0GKV% h09YU% f j Λ K hK n,
    fun ⟨m, hm, hΛ⟩ K hK n =>
      isConstructibleEtaleModule_homology_derivedLowerShriekUnbounded_of_stages B
        h0GKV% h09YU% f j Λ m hm hΛ K hK n⟩

/-- **Stacks 0GKZ.** Let `Y` be an affine scheme of `B`, `Λ` a Noetherian ring, `ι : X ≅ 𝔸¹_Y`,
`f = ι ≫ (𝔸¹_Y ⟶ Y)` the structure morphism, `j` a compactification of `f`, and `F` a
constructible sheaf of `Λ`-modules on `X = 𝔸¹_Y` which is torsion. Then every cohomology sheaf of
`Rf_! F` is constructible. -/
@[stacks 0GKZ "A¹_Y given as X with an isomorphism ι : X ≅ A¹_Y; Rf_! through any \
compactification j of f"]
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine
    (Y : B.Scheme) [IsAffine Y.obj] (X : B.Scheme)
    (ι : X.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.obj) [IsIso ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (ht : IsTorsionEtaleModule Λ X.obj F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} _ j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_stages B
    h0GKV% h09YU% Y X ι j Λ F hF ht k

/-- **Stacks 0GKY.** Let `Y` be a Noetherian affine scheme of `B`, `Λ` a Noetherian ring which is
torsion (`m = 0` in `Λ` for some `m > 0`), `ι : U ⟶ 𝔸¹_Y` an open immersion,
`f = ι ≫ (𝔸¹_Y ⟶ Y)` the structure morphism of `U`, `j` a compactification of `f`, and `F` a
finite type locally constant sheaf of `Λ`-modules on `U`. Then every cohomology sheaf of `Rf_! F`
is constructible. The source also assumes `Y` of finite dimension, which is not needed. -/
@[stacks 0GKY "Y Noetherian affine (finite dimension not needed); U given with an open immersion \
ι : U ⟶ A¹_Y; Λ torsion as m = 0 in Λ for some m > 0; Rf_! through any compactification j of f"]
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_openAffineLine
    (Y : B.Scheme) [IsNoetherian Y.obj] [IsAffine Y.obj] (U : B.Scheme)
    (ι : U.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.obj) [IsOpenImmersion ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (F : EtaleModules.{u, 0} Λ U.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.obj.smallEtaleTopology F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} _ j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_openAffineLine_of_stages B
    h0GKV% h09YU% Y U ι j Λ m hm hΛ F hF k

/-- **`Stacks.EtaleCohomology.LAdicSheaf.TorsionCompactSupportFinitenessInput` holds**: for `X`
separated of finite type over a finite field `k`, `k̄` an algebraic closure of `k` and `F` a
constructible sheaf of `ℤ_ℓ`-modules on `X` killed by a power of `ℓ`, every `H^a_c(X_k̄, F)` is
finite. -/
theorem LAdicSheaf.torsionCompactSupportFinitenessInput (ℓ : ℕ) [Fact ℓ.Prime] :
    LAdicSheaf.TorsionCompactSupportFinitenessInput B ℓ :=
  LAdicSheaf.torsionCompactSupportFinitenessInput_of_0GKV B ℓ h0GKV%

end Unconditional

end Stacks.EtaleCohomology

end
