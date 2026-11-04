module

public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityNatural

/-!
# Local duality over a complete Noetherian local ring, natural in the source

Let `(S, 𝔪)` be a complete Noetherian local ring and `ω` a dualizing complex over `S`. Every
shift `ω⟦j⟧` is derived `𝔪`-complete (its cohomology modules are finite over a complete ring),
and `RΓ_𝔪(ω⟦j⟧)` is an injective hull `E` of the residue field placed in a single degree `d`
(Stacks 0A82 after the normalizing shift). So
`Dualizing.bijective_homology_map_localCohomology_map` applies and gives

`Hom_{D(S)}(K, ω⟦j⟧) ≃ Hom_S(H^d_𝔪(K), E)`,

natural in `K`: the local duality theorem of Stacks 0AAK over a complete ring, with no
completion on the left and with naturality in `K`.

## Main results

* `Dualizing.isDerivedCompleteModule_of_finite` — a finite module over a complete Noetherian ring
  is derived complete.
* `Dualizing.exists_localCohomology_iso_single_injectiveHull` — the injective-hull realization of
  `RΓ_𝔪(ω⟦j⟧)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing

variable {S : Type u} [CommRing S] [IsNoetherianRing S]

/-- **A finite module over an `I`-adically complete Noetherian ring is derived `I`-complete.** It
is the cokernel of a map of finite free modules, and those are derived complete because the ring
is (Stacks 091R/091T). -/
theorem isDerivedCompleteModule_of_finite (I : Ideal S) [IsAdicComplete I S]
    (M : ModuleCat.{u} S) [Module.Finite S M] : IsDerivedCompleteModule I M := by
  have hS : IsDerivedCompleteModule I (ModuleCat.of S S) :=
    ((isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot S I
      (Ideal.fg_of_isNoetherianRing I) S).mp inferInstance).1
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' S M
  let F₀ := ModuleCat.of S (Fin n → S)
  let K := LinearMap.ker π
  have : Module.Finite S K := Module.Finite.of_injective K.subtype Subtype.val_injective
  obtain ⟨n₁, π₁, hπ₁⟩ := Module.Finite.exists_fin' S K
  let φ : ModuleCat.of S (Fin n₁ → S) ⟶ F₀ := ModuleCat.ofHom (K.subtype ∘ₗ π₁)
  have hrange : LinearMap.range φ.hom = K := by
    change LinearMap.range (K.subtype ∘ₗ π₁) = K
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hπ₁, Submodule.map_top,
      Submodule.range_subtype]
  let e : (F₀ ⧸ LinearMap.range φ.hom) ≃ₗ[S] M :=
    (Submodule.quotEquivOfEq _ _ hrange).trans (π.quotKerEquivOfSurjective hπ)
  exact (IsDerivedCompleteModule.cokernel φ (.of_finite_free hS _) (.of_finite_free hS F₀)).of_iso
    (ModuleCat.cokernelIsoRangeQuotient φ ≪≫ e.toModuleIso)

/-- **A complex with finite cohomology over an `I`-adically complete Noetherian ring is derived
`I`-complete.** -/
theorem isDerivedComplete_of_finite_homology (I : Ideal S) [IsAdicComplete I S]
    (X : DerivedCategory (ModuleCat.{u} S))
    (hX : ∀ n : ℤ, Module.Finite S ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj X)) :
    IsDerivedComplete I X :=
  (isDerivedComplete_iff_forall_isDerivedCompleteModule_homology I X).mpr fun n ↦
    have := hX n
    isDerivedCompleteModule_of_finite I _

/-- **`RΓ_𝔪` of a shifted dualizing complex is an injective hull in one degree.** Over a
Noetherian local ring with a dualizing complex `ω`, there are an injective module `E` containing
the residue field and an integer `d` such that `RΓ_𝔪(ω⟦j⟧) ≅ E[-(d - j)]` for every `j`. This is
Stacks 0A82 for the normalized shift `ω⟦-k⟧` of `ω`, moved along the shift functor, which
`RΓ_𝔪` commutes with. -/
theorem exists_localCohomology_iso_single_injectiveHull [IsLocalRing S]
    (ω : DerivedCategory (ModuleCat.{u} S)) (hω : IsDualizingComplex ω) :
    ∃ (E : ModuleCat.{u} S) (_ : Injective E) (ι : ResidueField S →ₗ[S] E)
      (_ : Function.Injective ι) (d : ℤ), ∀ j : ℤ,
      Nonempty ((derivedPowerTorsionProperty S (maximalIdeal S)
          (IsNoetherian.noetherian _)).ι.obj
        ((localCohomologyFunctor S (maximalIdeal S) (IsNoetherian.noetherian _)).obj
          (ω⟦j⟧)) ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) (d - j)).obj E) := by
  obtain ⟨k, hk, -⟩ := exists_isNormalizedDualizingComplex_shift_set_eq_singleton.{u, u} ω hω
  let N := ω⟦-k⟧
  have hm : (maximalIdeal S).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨eL⟩ := LocalDuality.nonempty_localCohomology_iso_single_homology_zero.{u, u} S N hk
  obtain ⟨i₀, hi₀, hull⟩ :=
    LocalDuality.exists_isInjectiveHull_homology_zero_localCohomology.{u, u} S N hk
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0).obj
    ((derivedPowerTorsionProperty S (maximalIdeal S) hm).ι.obj
      ((localCohomologyFunctor S (maximalIdeal S) hm).obj N))
  let ι : ResidueField S →ₗ[S] E := i₀.hom ∘ₗ (ULift.moduleEquiv (R := S)).symm.toLinearMap
  refine ⟨E, hull.1, ι, ((ModuleCat.mono_iff_injective i₀).mp hi₀).comp
    (ULift.moduleEquiv (R := S)).symm.injective, -k, fun j ↦ ?_⟩
  let P := derivedPowerTorsionProperty S (maximalIdeal S) hm
  let G := localCohomologyFunctor S (maximalIdeal S) hm
  let : G.CommShift ℤ := (localCohomologyAdjunction S (maximalIdeal S) hm).rightAdjointCommShift ℤ
  let a : ℤ := k + j
  refine ⟨P.ι.mapIso (G.mapIso
    ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} S)) (-k) a j (by omega)).app ω)) ≪≫ ?_⟩
  refine (P.ι.mapIso ((G.commShiftIso a).app N)) ≪≫ (P.ι.commShiftIso a).app (G.obj N) ≪≫
    (shiftFunctor _ a).mapIso eL ≪≫ ?_
  exact ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso a (-k - j) 0
    (by omega)).app E

end Dualizing
