module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Reflexivity of a finite module is a local property

Let `R` be a Noetherian ring and `M` a finite `R`-module. The module `M` is reflexive, i.e.
the evaluation map `M → Hom_R(Hom_R(M, R), R)` is bijective, if and only if `M_𝔭` is a
reflexive `R_𝔭`-module for every prime `𝔭`, if and only if `M_𝔪` is a reflexive `R_𝔪`-module
for every maximal ideal `𝔪`.

## Main results

* `reflexive_localized_iff_map_bijective`: for a prime `p`, the localization `M_p` is a
  reflexive `R_p`-module if and only if the localization at `p` of the evaluation map
  `M → Hom_R(Hom_R(M, R), R)` is bijective.
* `reflexive_tfae`: `M` is reflexive, iff all localizations at primes are reflexive, iff all
  localizations at maximal ideals are reflexive.

## References

* [Stacks: Tag 0AV1](https://stacks.math.columbia.edu/tag/0AV1)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Module

/-- For a finite module `M` over a Noetherian ring `R` and a prime `p` of `R`, the localization
`M_p` is a reflexive `R_p`-module if and only if the localization at `p` of the evaluation map
`M → Hom_R(Hom_R(M, R), R)` is bijective. -/
theorem reflexive_localized_iff_map_bijective
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] :
    Module.IsReflexive (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ↔
      Function.Bijective
        (IsLocalizedModule.map p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M)
          (LocalizedModule.mkLinearMap p.primeCompl (Module.Dual R (Module.Dual R M)))
          (Module.Dual.eval R M)) := by
  set S := p.primeCompl
  set Rₚ := Localization.AtPrime p
  set Mₚ := LocalizedModule S M
  set e := IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S M)
            (LocalizedModule.mkLinearMap S (Module.Dual R (Module.Dual R M)))
            (Module.Dual.eval R M)
  obtain ⟨ι, hιbij, hnat⟩ :
      ∃ ι : LocalizedModule S (Module.Dual R (Module.Dual R M)) →
              Module.Dual Rₚ (Module.Dual Rₚ Mₚ),
        Function.Bijective ι ∧ (ι ∘ e = Module.Dual.eval Rₚ Mₚ) := by
    classical
    have hFP : FinitePresentation R M := Module.finitePresentation_of_finite R M
    have hFPd : FinitePresentation R (Module.Dual R M) := Module.finitePresentation_of_finite R _
    have hf1 : IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S
                (LocalizedModule.mkLinearMap S M) (Algebra.linearMap R Rₚ) Rₚ) :=
      Module.FinitePresentation.isLocalizedModule_mapExtendScalars S
        (LocalizedModule.mkLinearMap S M) (Algebra.linearMap R Rₚ) Rₚ
    have hf2 : IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S
        (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
          LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
        (Algebra.linearMap R Rₚ) Rₚ) :=
      Module.FinitePresentation.isLocalizedModule_mapExtendScalars
        (R := R) (M := Module.Dual R M) (N := R) S
        (f := @LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
                LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
        (g := Algebra.linearMap R Rₚ) (Rₛ := Rₚ)
    let iso1 := (IsLocalizedModule.iso S (IsLocalizedModule.mapExtendScalars S
                (LocalizedModule.mkLinearMap S M)
                (Algebra.linearMap R Rₚ) Rₚ)).extendScalarsOfIsLocalization S Rₚ
    let iso2 := (IsLocalizedModule.iso S (IsLocalizedModule.mapExtendScalars S
                (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
                  LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
                (Algebra.linearMap R Rₚ) Rₚ)).extendScalarsOfIsLocalization S Rₚ
    set ι₀ : LocalizedModule S (Module.Dual R (Module.Dual R M)) ≃ₗ[Rₚ]
              Module.Dual Rₚ (Module.Dual Rₚ Mₚ) := iso2.trans iso1.dualMap.symm
    have hiso1 : ∀ (ξ : Module.Dual R M) (m : M),
        (iso1 (LocalizedModule.mk ξ 1)) (LocalizedModule.mk m 1) = algebraMap R Rₚ (ξ m) := by
      intro ξ m
      have h := IsLocalizedModule.iso_symm_apply S
        (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
          (Algebra.linearMap R Rₚ) Rₚ) ξ
      have h2 := congrArg (IsLocalizedModule.iso S (IsLocalizedModule.mapExtendScalars S
          (LocalizedModule.mkLinearMap S M) (Algebra.linearMap R Rₚ) Rₚ)) h
      simp only [LinearEquiv.apply_symm_apply] at h2
      change (iso1 (LocalizedModule.mk ξ 1)) (LocalizedModule.mk m 1) = _
      have hiso1eq : iso1 (LocalizedModule.mk ξ 1) =
          (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
            (Algebra.linearMap R Rₚ) Rₚ) ξ := by
        change (LinearEquiv.extendScalarsOfIsLocalization S Rₚ _) _ = _
        rw [LinearEquiv.extendScalarsOfIsLocalization_apply, ← h2]
      rw [hiso1eq, IsLocalizedModule.mapExtendScalars_apply_apply,
        show (LocalizedModule.mk m 1 : Mₚ) = LocalizedModule.mkLinearMap S M m from rfl,
        IsLocalizedModule.map_apply]
      simp [Algebra.linearMap_apply]
    have hinner : ∀ (m : M) (ψ : LocalizedModule S (Module.Dual R M)),
        (IsLocalizedModule.map S
            (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
              LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
            (Algebra.linearMap R Rₚ) (Module.Dual.eval R M m)) ψ
          = (iso1 ψ) (LocalizedModule.mk m 1) := by
      intro m
      have huR : ∀ (x : S), IsUnit ((algebraMap R (Module.End R Rₚ)) ↑x) :=
        have := isLocalizedModule_id S Rₚ Rₚ
        IsLocalizedModule.map_units (S := S) (LinearMap.id : Rₚ →ₗ[R] Rₚ)
      have key2 : (IsLocalizedModule.map S
            (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
              LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
            (Algebra.linearMap R Rₚ) (Module.Dual.eval R M m))
          = (LinearMap.applyₗ (LocalizedModule.mk m 1) : (Mₚ →ₗ[Rₚ] Rₚ) →ₗ[Rₚ] Rₚ).restrictScalars R
              ∘ₗ iso1.toLinearMap.restrictScalars R := by
        refine IsLocalizedModule.ext S
          (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
            LinearMap.addCommGroup.toAddCommMonoid LinearMap.module) huR (LinearMap.ext fun ξ => ?_)
        change (IsLocalizedModule.map S _ (Algebra.linearMap R Rₚ) (Module.Dual.eval R M m))
              ((@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
                LinearMap.addCommGroup.toAddCommMonoid LinearMap.module) ξ)
            = (iso1 ((@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
                LinearMap.addCommGroup.toAddCommMonoid LinearMap.module) ξ)) (LocalizedModule.mk m
                    1)
        rw [IsLocalizedModule.map_apply,
          show ((@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
                LinearMap.addCommGroup.toAddCommMonoid LinearMap.module) ξ)
              = LocalizedModule.mk ξ 1 from rfl, hiso1 ξ m]
        simp [Algebra.linearMap_apply, Module.Dual.eval_apply]
      exact LinearMap.congr_fun key2
    have hnat0 : ∀ m : M, ι₀ (e (LocalizedModule.mk m
        1)) = Module.Dual.eval Rₚ Mₚ (LocalizedModule.mk m 1) := by
      intro m
      refine LinearMap.ext fun φ => ?_
      rw [Module.Dual.eval_apply]
      have he1 : e (LocalizedModule.mk m 1) =
          LocalizedModule.mk (Module.Dual.eval R M m) 1 := by
        change (IsLocalizedModule.map S _ _ (Module.Dual.eval R M)) (LocalizedModule.mk m 1) = _
        rw [show (LocalizedModule.mk m 1 : Mₚ) = LocalizedModule.mkLinearMap S M m from rfl,
          IsLocalizedModule.map_apply]
        rfl
      rw [he1]
      change (iso1.dualMap.symm (iso2 (LocalizedModule.mk (Module.Dual.eval R M m) 1))) φ = _
      rw [LinearEquiv.dualMap_symm]
      change (iso2 (LocalizedModule.mk (Module.Dual.eval R M m) 1)) (iso1.symm φ) = _
      have hiso2 : iso2 (LocalizedModule.mk (Module.Dual.eval R M m) 1) =
          (IsLocalizedModule.mapExtendScalars S
            (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
              LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
            (Algebra.linearMap R Rₚ) Rₚ) (Module.Dual.eval R M m) := by
        have h := IsLocalizedModule.iso_symm_apply S
          (IsLocalizedModule.mapExtendScalars S
            (@LocalizedModule.mkLinearMap R _ S (Module.Dual R M)
              LinearMap.addCommGroup.toAddCommMonoid LinearMap.module)
            (Algebra.linearMap R Rₚ) Rₚ) (Module.Dual.eval R M m)
        change (LinearEquiv.extendScalarsOfIsLocalization S Rₚ _) _ = _
        rw [LinearEquiv.extendScalarsOfIsLocalization_apply,
          show (LocalizedModule.mk (Module.Dual.eval R M m) 1) = _ from h.symm,
          LinearEquiv.apply_symm_apply]
      rw [hiso2, IsLocalizedModule.mapExtendScalars_apply_apply, hinner m (iso1.symm φ),
        LinearEquiv.apply_symm_apply]
    have huDD : ∀ (x : S), IsUnit ((algebraMap R
        (Module.End R (Module.Dual Rₚ (Module.Dual Rₚ Mₚ)))) ↑x) :=
      have := isLocalizedModule_id S (Module.Dual Rₚ (Module.Dual Rₚ Mₚ)) Rₚ
      IsLocalizedModule.map_units (S := S)
        (LinearMap.id : Module.Dual Rₚ (Module.Dual Rₚ Mₚ) →ₗ[R] _)
    have key : (ι₀.toLinearMap.restrictScalars R ∘ₗ e)
        = (Module.Dual.eval Rₚ Mₚ).restrictScalars R :=
      IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M) huDD (LinearMap.ext hnat0)
    refine ⟨⇑ι₀, ι₀.bijective, ?_⟩
    have hfun := congrArg DFunLike.coe key
    simpa only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] using hfun
  have hbij_eq : Function.Bijective (Module.Dual.eval Rₚ Mₚ) ↔ Function.Bijective ⇑e := by
    rw [← hnat, hιbij.of_comp_iff' e]
  rw [hbij_eq.symm]
  exact ⟨fun _ => Module.bijective_dual_eval Rₚ Mₚ, fun h => ⟨h⟩⟩

/-- **Stacks 0AV1**.
Let `R` be a Noetherian ring and `M` a finite `R`-module. The following are equivalent: `M` is
reflexive; `M_p` is a reflexive `R_p`-module for every prime `p`; `M_m` is a reflexive
`R_m`-module for every maximal ideal `m`. -/
@[stacks 0AV1]
theorem reflexive_tfae
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    [ Module.IsReflexive R M,
      ∀ (p : Ideal R) [p.IsPrime],
        Module.IsReflexive (Localization.AtPrime p) (LocalizedModule p.primeCompl M),
      ∀ (m : Ideal R) [m.IsMaximal],
        Module.IsReflexive (Localization.AtPrime m) (LocalizedModule m.primeCompl M)
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro hM p _
    obtain ⟨hinj, hsurj⟩ := Module.bijective_dual_eval R M
    rw [reflexive_localized_iff_map_bijective R M p]
    exact ⟨IsLocalizedModule.map_injective _ _ _ _ hinj,
      IsLocalizedModule.map_surjective _ _ _ _ hsurj⟩
  tfae_have 2 → 3 := fun h m _ => h m
  tfae_have 3 → 1 := by
    intro h
    refine ⟨?_⟩
    refine bijective_of_isLocalized_maximal
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      (fun P _ => LocalizedModule P.primeCompl (Module.Dual R (Module.Dual R M)))
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (Module.Dual R (Module.Dual R M)))
      (Module.Dual.eval R M) ?_
    intro P _
    rw [← reflexive_localized_iff_map_bijective R M P]
    exact h P
  tfae_finish
