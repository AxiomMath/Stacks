module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedFibreGradedTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections

/-!
# Global sections on the closed fibre

For the base change `p : h_U ⟶ X` of a closed immersion `ι : P ⟶ T` along `f : X ⟶ h_T`, with
fibre ideal `I` (`AlgebraicGeometry.Space.fibreIdeal`), the inverse image of global sections
`Γ(X, ℱ) ⟶ Γ(h_U, p^*ℱ)` factors as `Γ(X, ℱ) ⟶ Γ(X, ℱ/Iℱ) ≅ Γ(h_U, p^*ℱ)` (Stacks 04CJ).

## Main results

* `AlgebraicGeometry.Space.surjective_globalSections_map_of_epi_rightDerived_zero`: a morphism
  that is an epimorphism on `H⁰` is surjective on global sections.
* `AlgebraicGeometry.Space.surjective_globalSectionsPullbackMap_of_surjective_quotient`: if
  `Γ(X, ℱ) ⟶ Γ(X, ℱ/Iℱ)` is surjective, so is `Γ(X, ℱ) ⟶ Γ(h_U, p^*ℱ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

/-- A morphism of modules that is an epimorphism on `H⁰` is surjective on global sections. -/
theorem surjective_globalSections_map_of_epi_rightDerived_zero {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : have := hasInjectiveResolutions_modules B S hS X.1 X.2
      Epi (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map φ)) :
    Function.Surjective ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).map φ).hom := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  have e := Γ.rightDerivedZeroIsoSelf
  have hn : Γ.map φ = e.inv.app M ≫ (Γ.rightDerived 0).map φ ≫ e.hom.app N := by
    rw [← e.inv.naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]
  have : Epi (Γ.map φ) := by
    rw [hn]
    have := h
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P T U : BigFppfOver B S hS} (ι : P ⟶ T)
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (f : X ⟶ representedAlgebraicSpace B S hS T) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ P)
  (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map ι))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
include hsq in
/-- If `Γ(X, ℱ) ⟶ Γ(X, ℱ/Iℱ)` is surjective, `I` being the fibre ideal, so is the inverse image of
global sections `Γ(X, ℱ) ⟶ Γ(h_U, p^*ℱ)`. -/
theorem surjective_globalSectionsPullbackMap_of_surjective_quotient
    (G : Modules.{u, u} B S hS X.1 X.2)
    (h : Function.Surjective ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).map
        (cokernel.π (idealPowSubmodule (fibreIdeal ι hι f) 1 G).ι)).hom) :
    Function.Surjective (globalSectionsPullbackMap B S hS
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) G).hom := by
  let P' : representedAlgebraicSpace B S hS U ⟶ X := ObjectProperty.homMk p
  have hpc : IsClosedImmersion B S hS P'.hom := isClosedImmersion_of_fibreSquare ι hι f p q hsq
  have hk : kerIdealSmul B S hS P' G = idealPowSubmodule (fibreIdeal ι hι f) 1 G :=
    congrArg (fun I ↦ idealPowSubmodule I 1 G)
      (kerIdeal_structureSharp_eq_fibreIdeal ι hι f p q hsq)
  have key : ∀ A C : G.Submodule, A = C → A.ι ≫ cokernel.π C.ι = 0 := by
    rintro A C rfl
    exact cokernel.condition _
  let πK : G ⟶ kerIdealSmulQuotient B S hS P' G := cokernel.π _
  have hcK : (idealPowSubmodule (fibreIdeal ι hι f) 1 G).ι ≫ πK = 0 := key _ _ hk.symm
  let πM := cokernel.π (idealPowSubmodule (fibreIdeal ι hι f) 1 G).ι
  have hcM : (kerIdealSmul B S hS P' G).ι ≫ πM = 0 := key _ _ hk
  let ψ := cokernel.desc _ πK hcK
  let χ : kerIdealSmulQuotient B S hS P' G ⟶ _ := cokernel.desc _ πM hcM
  have hψ : πM ≫ ψ = πK := cokernel.π_desc _ _ _
  have hχ : πK ≫ χ = πM := cokernel.π_desc _ _ _
  have : IsIso ψ := ⟨χ, by
      rw [← cancel_epi πM, ← Category.assoc, hψ, hχ, Category.comp_id],
    by rw [← cancel_epi πK, ← Category.assoc, hχ, hψ, Category.comp_id]⟩
  let e := kerIdealSmulQuotientUnitIso B S hS P' hpc G
  have hu : πK ≫ e.hom = (modulePullbackAdjunction B S hS P').unit.app G :=
    cokernel_π_comp_kerIdealSmulQuotientUnitIso_hom B S hS P' hpc G
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  have hfac : globalSectionsPullbackMap B S hS P' G =
      Γ.map πM ≫ Γ.map (ψ ≫ e.hom) ≫
        (globalSectionsPushforwardIsoSite B S hS P').hom.app
          ((modulePullback B S hS P').obj G) := by
    unfold globalSectionsPullbackMap
    rw [← hu, ← hψ, Category.assoc, Functor.map_comp, Category.assoc]
  rw [hfac]
  have hb₁ : Function.Bijective (Γ.map (ψ ≫ e.hom)).hom := ConcreteCategory.bijective_of_isIso _
  have hb₂ : Function.Bijective ((globalSectionsPushforwardIsoSite B S hS P').hom.app
      ((modulePullback B S hS P').obj G)).hom := ConcreteCategory.bijective_of_isIso _
  exact hb₂.2.comp (hb₁.2.comp h)

end AlgebraicGeometry.Space

end
