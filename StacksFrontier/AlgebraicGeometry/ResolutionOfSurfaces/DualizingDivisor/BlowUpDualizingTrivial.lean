module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleTorsionFree
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingAffine
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingQuotientBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingConstruction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingProjective

/-!
# The dualizing complex of the blowup of a Gorenstein rational surface singularity

Let `A` be a Gorenstein local normal Nagata domain of dimension two defining a rational
singularity which is not regular, and let `f : X ⟶ Spec(A)` be the blowup in the maximal ideal.
Normalizing with respect to the dualizing module `ω_A = A`, the canonical map
`f^*ω_A ⟶ ω_X` is surjective by [Stacks, Tag 0B64] (3). Its source is `𝒪_X`, and a surjection
from `𝒪_X` onto a dualizing module of an integral scheme is an isomorphism, the stalks of a
dualizing module being torsion free and nonzero. Hence `f^!(A) ≅ 𝒪_X` in degree zero.

This is the local step of the proof of the second sentence of [Stacks, Tag 0EA2].

## Main results

* `Stacks.Duality.isIso_of_epi_of_isDualizingModule`: an epimorphism `𝒪_X ⟶ ω` onto a dualizing
  module is an isomorphism when the local rings of `X` are domains.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Duality

/-- **A surjection from `𝒪_X` onto a dualizing module is an isomorphism** on a locally
Noetherian scheme whose local rings are domains. On stalks the map is `a ↦ a • σ` for the germ
`σ` of the image of `1`; it is surjective, so `σ ≠ 0` (the stalks of a dualizing module are
nonzero), hence injective, the stalks of a dualizing module being torsion free. -/
theorem isIso_of_epi_of_isDualizingModule {X : Scheme.{u}} [IsLocallyNoetherian X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] {ω : X.Modules} (hω : IsDualizingModule ω)
    (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ ω) [Epi ψ] : IsIso ψ := by
  have : Mono ψ := by
    let t : Γ(ω, ⊤) := Scheme.Modules.Hom.app ψ ⊤ (1 : Γ(X, ⊤))
    -- the germ of `ψ r` is the germ of `r` times the germ of `t`
    have hgerm : ∀ (x : X), letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
        ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)), ω.presheaf.germ U x hx
          (Scheme.Modules.Hom.app ψ U r) =
            X.presheaf.germ U x hx r • ω.presheaf.germ ⊤ x trivial t := by
      intro x U hx r
      let := Stacks.ModuleStalkSpecialization.stalkModule ω x
      -- `ψ` on sections over `U` is multiplication by the restriction of `t`
      have h1 : Scheme.Modules.Hom.app ψ U r =
          r • Scheme.Modules.Hom.app ψ U (1 : Γ(X, U)) :=
        (congrArg _ (mul_one r).symm).trans ((ψ.val.app (op U)).hom.map_smul r (1 : Γ(X, U)))
      have h2 : Scheme.Modules.Hom.app ψ U (1 : Γ(X, U)) =
          ω.presheaf.map (homOfLE le_top).op t :=
        ((ω.unitHomEquiv ψ).property (homOfLE (le_top (a := U))).op).symm
      rw [h1, h2, Stacks.ModuleStalkSpecialization.germ_smul ω hx r _,
        TopCat.Presheaf.germ_res_apply]
    have hσ : ∀ x : X, ω.presheaf.germ ⊤ x trivial t ≠ 0 := by
      intro x h0
      let := Stacks.ModuleStalkSpecialization.stalkModule ω x
      have : Nontrivial (ω.presheaf.stalk x) :=
        IsDualizingRingModule.nontrivial (M := ModuleCat.of _ (ω.presheaf.stalk x))
          (hω.isDualizingRingModule_stalk x)
      have : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ ψ :=
        ⟨fun g₁ g₂ h => (inferInstance : Epi ψ).left_cancellation g₁ g₂ h⟩
      have hs : Function.Surjective
          (stalkLinearMap (SheafOfModules.unit X.ringCatSheaf) ω ψ x) :=
        Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi (O := X.ringCatSheaf) ψ x
      obtain ⟨z, hz⟩ := exists_ne (0 : ω.presheaf.stalk x)
      obtain ⟨y, rfl⟩ := hs z
      obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)) y
      apply hz
      refine (stalkLinearMap_germ (SheafOfModules.unit X.ringCatSheaf) ω ψ U x hxU r).trans ?_
      change ω.presheaf.germ U x hxU (Scheme.Modules.Hom.app ψ U r) = 0
      rw [hgerm x U hxU r, h0, smul_zero]
    refine Stacks.RegularSequence.mono_of_injective_app ψ fun U => ?_
    refine (injective_iff_map_eq_zero (Scheme.Modules.Hom.app ψ U).hom).2 fun r hr => ?_
    refine TopCat.Presheaf.section_ext X.sheaf U r 0 fun x hx => ?_
    change X.presheaf.germ U x hx r = X.presheaf.germ U x hx 0
    let := Stacks.ModuleStalkSpecialization.stalkModule ω x
    have := hω.isTorsionFree_stalk x
    have h0 : X.presheaf.germ U x hx r • ω.presheaf.germ ⊤ x trivial t = 0 := by
      rw [← hgerm x U hx r]
      simp [hr]
    rw [map_zero]
    exact (smul_eq_zero_iff_left (hσ x)).1 h0
  exact isIso_of_mono_of_epi ψ

/-- **A Gorenstein local ring is a dualizing module over itself** ([Stacks, Remark 0B4R] for the
terminology): `A` is finite over itself and `A[0]` is a dualizing complex. -/
theorem isDualizingRingModule_self_of_isGorensteinLocalRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (h : Dualizing.IsGorensteinLocalRing A) :
    IsDualizingRingModule A (ModuleCat.of A A) :=
  ⟨inferInstanceAs (Module.Finite A A), 0, h⟩

end Stacks.Duality

namespace AlgebraicGeometry.RationalSingularitySituation

/-- **The blowup of a Gorenstein rational surface singularity has trivial dualizing complex.**
Let `A` be as in Situation [Stacks, Tag 0B4W], Gorenstein and not regular, and let
`f : X ⟶ Spec(A)` be the blowup in the maximal ideal. For any dualizing module `ω_X` of `X`
normalized relative to `ω_A = A` (`DualizingNormalization`: `f^!(A) ≅ ω_X` in degree zero), the
canonical map `𝒪_X = f^*Ã ⟶ ω_X` is surjective by [Stacks, Tag 0B64] (3), hence an
isomorphism (`Stacks.Duality.isIso_of_epi_of_isDualizingModule`, the blowup being normal), so
`f^!(A) ≅ 𝒪_X` in degree zero. -/
theorem nonempty_relativeDualizingComplex_blowUp_iso_unit (S : RationalSingularitySituation.{u})
    (hgor : letI : IsNoetherianRing S.A := S.nagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing S.A)
    (hnot : ¬ IsRegularLocalRing S.A) (ωX : (BlowUpDualizing.blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        BlowUpDualizing.isLocallyNoetherian_blowUpScheme S.A
      letI : IsNoetherianRing S.A := S.nagata.isNoetherianRing
      (rationalSingularitySituationBlowUp S).DualizingNormalization (ModuleCat.of S.A S.A) ωX) :
    letI : IsNoetherianRing S.A := S.nagata.isNoetherianRing
    Nonempty (((rationalSingularitySituationBlowUp S).relativeDualizingComplex
        (ModuleCat.of S.A S.A)).obj ≅
      (DerivedCategory.singleFunctor (rationalSingularitySituationBlowUp S).X.Modules 0).obj
        (SheafOfModules.unit (rationalSingularitySituationBlowUp S).X.ringCatSheaf)) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    BlowUpDualizing.isLocallyNoetherian_blowUpScheme S.A
  let : IsNoetherianRing S.A := S.nagata.isNoetherianRing
  let T := rationalSingularitySituationBlowUp S
  have hωA := Stacks.Duality.isDualizingRingModule_self_of_isGorensteinLocalRing S.A hgor
  have hepi := BlowUpDualizing.epi_normalizedPullbackMap S hnot _ hωA ωX N
  let e : @Iso T.X.Modules _ (SheafOfModules.unit T.X.ringCatSheaf)
      ((Scheme.Modules.pullback T.f).obj (tilde (ModuleCat.of S.A S.A))) :=
    (Scheme.Modules.pullbackUnitIso T.f).symm ≪≫
      (Scheme.Modules.pullback T.f).mapIso (tildeSelf (R := CommRingCat.of S.A)).symm
  let ψ : SheafOfModules.unit T.X.ringCatSheaf ⟶ ωX :=
    e.hom ≫ T.normalizedPullbackMap hωA N.normalizedIso
  have : Epi ψ := @epi_comp _ _ _ _ _ e.hom (@IsIso.epi_of_iso _ _ _ _ e.hom (Iso.isIso_hom e))
    _ hepi
  have : ∀ x : T.X, IsDomain (T.X.presheaf.stalk x) := fun x => inferInstance
  have := Stacks.Duality.isIso_of_epi_of_isDualizingModule N.isDualizing ψ
  exact ⟨N.normalizedIso ≪≫ (DerivedCategory.singleFunctor T.X.Modules 0).mapIso (asIso ψ).symm⟩

/-- **The blowup of a Gorenstein rational surface singularity has trivial dualizing complex**,
unconditionally: `f^!(A) ≅ 𝒪_X` in degree zero for the blowup `f` of `Spec(A)` in the maximal
ideal, `A` Gorenstein and not regular in Situation [Stacks, Tag 0B4W]. The normalized dualizing
module exists by [Stacks, Tag 0AA3] for the blowup (`dualizingNormalizationBlowUp`). -/
theorem nonempty_relativeDualizingComplex_blowUp_iso_unit_of_isGorenstein
    (S : RationalSingularitySituation.{u})
    (hgor : letI : IsNoetherianRing S.A := S.nagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing S.A)
    (hnot : ¬ IsRegularLocalRing S.A) :
    letI : IsNoetherianRing S.A := S.nagata.isNoetherianRing
    Nonempty (((rationalSingularitySituationBlowUp S).relativeDualizingComplex
        (ModuleCat.of S.A S.A)).obj ≅
      (DerivedCategory.singleFunctor (rationalSingularitySituationBlowUp S).X.Modules 0).obj
        (SheafOfModules.unit (rationalSingularitySituationBlowUp S).X.ringCatSheaf)) :=
  let : IsNoetherianRing S.A := S.nagata.isNoetherianRing
  nonempty_relativeDualizingComplex_blowUp_iso_unit S hgor hnot _
    (dualizingNormalizationBlowUp S
      (Stacks.Duality.isDualizingRingModule_self_of_isGorensteinLocalRing S.A hgor))

end AlgebraicGeometry.RationalSingularitySituation
