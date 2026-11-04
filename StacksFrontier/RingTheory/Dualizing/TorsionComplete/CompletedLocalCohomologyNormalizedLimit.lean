module

public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.AdicQuotientComparison
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.TensorModelNormalizedLimit
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Basic

/-!
# The derived limit of Stacks 0EEW with its projections normalized against the completion unit

Tag 0EEW part (1) says that `RΓ_Z(M)^∧` is a derived limit of the tower `n ↦ RΓ_Z(M/IⁿM)`. Being
a derived limit is a property of the object, so that statement does not say *which* cone it holds
for: the projections of a derived limit may be altered by any automorphism of it. What pins the
cone down is the completion unit, and this file produces the derived limit together with
projections whose composites with the unit are the maps induced by `M ↠ M/IⁿM`.

## Main results

* `Dualizing.exists_isDerivedLimitWithProjections_of_uliftAdicQuotientIso` — a reflection onto the
  derived `I`-complete objects, together with a unit-normalized derived-limit cone on the tower of
  Tag 0EEW, granted the universe-lift comparison of the adic quotient towers.

## Implementation notes

The proof is `Dualizing.exists_isDerivedLimitWithProjections_of_tensorIso`, the same argument
for any functor given by a derived tensor product, applied to local cohomology through the Čech
formula `Stacks.LocalCohomology.CechFormula.localCohomologyCechIso`. What that argument does is
recorded here.

The normalized form of Stacks 0922 — derived completion is `R lim (K ⊗ᴸ A/Iⁿ)`, with the
adjunction unit inducing the reduction maps — is available only with the tower expressed over
`ULift A`, because the derived tensor product used there is the one of `ULift A`. Descending the
reduction maps themselves would need the universe-lift tensor comparison to be compatible with
the right unitor, which is not available. So the whole comparison of towers is carried out on the
`ULift A` side, and the universe boundary is crossed only by natural isomorphisms in the module
variable: those respect the legs `C ⊗ᴸ (M ↠ M/IⁿM)` automatically, because the legs are the
functor applied to the quotient maps, and naturality is exactly the statement that they do.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

/-- **Stacks 0EEW part (1) with a unit-normalized cone**, granted the universe-lift comparison
`lam` of the adic quotient towers and its compatibility `hlam` with the quotient maps.

The reflection produced is the one of Stacks 0922; `Dualizing.exists_iso_of_reflections` then
identifies it with any other model of derived completion, compatibly with the units, so nothing
here depends on which model of derived completion one starts from. -/
theorem exists_isDerivedLimitWithProjections_of_uliftAdicQuotientIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsNoetherianRing (ULift.{u} A)]
    [Module.Finite (ULift.{u} A) ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M)]
    (hJB : (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom).FG)
    (lam : AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M))
    (hlam : ∀ n : ℕ, (AdicKoszul.moduleUniverseLift.{u, u} A).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) ≫ lam.hom.app ⟨n⟩ =
        ModuleCat.ofHom ((I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
          (⊤ : Submodule (ULift.{u} A)
            (((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)))).mkQ) :
    ∃ (Gfun : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
      (η : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶ Gfun),
      (∀ Y, IsDerivedComplete I (Gfun.obj Y)) ∧
      (∀ Y E, IsDerivedComplete I E →
        Function.Bijective (fun g : Gfun.obj Y ⟶ E ↦ η.app Y ≫ g)) ∧
      ∃ q : ∀ n : ℕ, Gfun.obj ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⟶
        (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩,
        NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (adicQuotientLocalCohomologySystem A I J hJ M)
          (Gfun.obj ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) q ∧
        ∀ n : ℕ, η.app ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≫ q n =
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
              Stacks.LocalCohomology.localCohomologyDerived A J hJ).map
                (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) := by
  obtain ⟨s, fJ, hfJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  change Ideal.span (Set.range fJ) = J at hfJ
  obtain ⟨L₀, adj, q, hq, hqnorm⟩ := exists_isDerivedLimitWithProjections_of_tensorIso A I
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      Stacks.LocalCohomology.localCohomologyDerived A J hJ)
    (Stacks.LocalCohomology.CechFormula.cechRegularObject.{u, u} fJ)
    (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (Stacks.LocalCohomology.CechFormula.localCohomologyCechIso A J hJ fJ hfJ))
    M hJB lam hlam
  refine ⟨L₀ ⋙ (derivedCompleteProperty.{u, u} A I).ι, adj.unit, fun Y ↦ (L₀.obj Y).property,
    fun Y E hE ↦ by
      have h : (fun g : (L₀ ⋙ (derivedCompleteProperty.{u, u} A I).ι).obj Y ⟶ E ↦
            adj.unit.app Y ≫ g) =
          (adj.homEquiv Y ⟨E, hE⟩) ∘
            ((derivedCompleteProperty.{u, u} A I).fullyFaithfulι.homEquiv (X := L₀.obj Y)
              (Y := ⟨E, hE⟩)).symm := by
        funext g
        simp only [Function.comp_apply, Adjunction.homEquiv_unit]
        rfl
      rw [h]
      exact (adj.homEquiv Y ⟨E, hE⟩).bijective.comp (Equiv.bijective _),
    q, hq, hqnorm⟩

end Dualizing

end
