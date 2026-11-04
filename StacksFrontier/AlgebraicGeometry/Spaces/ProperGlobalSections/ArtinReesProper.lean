module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.YonedaArtinRees

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)


variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- **Artin-Rees for the structure module of a reduced algebraic space proper over a Noetherian
ring.** The structure module embeds into the direct image of the structure module of a Chow
cover, whose global sections are finite, and Artin-Rees holds there by
`AlgebraicGeometry.Space.hasSectionsArtinRees_unit_yoneda`. -/
theorem hasSectionsArtinRees_unit_of_isReduced [IsNoetherianRing A]
    (Z : AlgebraicSpaces B (Spec (.of A)) hA)
    (hZp : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from Z.1))
    (hred : HasEtaleLocalProperty B (Spec (.of A)) hA Z.1 (fun T : Scheme.{u} => IsReduced T))
    (I : Ideal A) :
    HasSectionsArtinRees A Z (baseIdealSheaf A Z I) I (SheafOfModules.unit _) := by
  obtain ⟨V, ρ, hρS, hVP⟩ := exists_isProper_chowChart B A hA Z _ hZp
  let ρ' : yonedaSpace B (Spec (.of A)) hA V ⟶ Z := ObjectProperty.homMk ρ
  have hρ : yoneda.relativelyRepresentable ρ'.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B (Spec (.of A)) hA Z.2 ρ
  let := isContinuous_smallBaseChange B (Spec (.of A)) hA ρ' hρ
  let φ₀ : (SheafOfModules.unit _ : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) ⟶
      (smallBaseChangeModulePushforward.{u, u} B (Spec (.of A)) hA ρ' hρ).obj
        (SheafOfModules.unit _) :=
    SheafOfModules.unitToPushforwardObjUnit (smallBaseChangeSharp B (Spec (.of A)) hA ρ' hρ)
  have hmono' : Mono φ₀ := mono_unitToPushforwardObjUnit_smallBaseChangeSharp ρ' hρ hρS hred
  let φ : SheafOfModules.unit _ ⟶ (modulePushforward B (Spec (.of A)) hA ρ').obj
      (SheafOfModules.unit _) :=
    φ₀ ≫ ((modulePushforwardChartIso B (Spec (.of A)) hA ρ' hρ).app _).inv
  have hinv : Mono ((modulePushforwardChartIso B (Spec (.of A)) hA ρ' hρ).app
      (SheafOfModules.unit _)).inv :=
    ⟨fun g h hgh => by
      have := congrArg (· ≫ ((modulePushforwardChartIso B (Spec (.of A)) hA ρ' hρ).app
        (SheafOfModules.unit _)).hom) hgh
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using this⟩
  have : Mono φ := @mono_comp _ _ _ _ _ φ₀ hmono' _ hinv
  let := siteObjSectionsAlgebra A V
  have hfin : Module.Finite A ((sectionsOverBase A B hA Z.1 Z.2).obj
      ((modulePushforward B (Spec (.of A)) hA ρ').obj (SheafOfModules.unit _))) := by
    have := module_finite_siteObjFunctions B A hA V hVP
    exact Module.Finite.equiv ((sectionsOverBasePushforwardIso A ρ' _).toLinearEquiv.trans
      (unitSectionsYonedaLinearEquiv A V)).symm
  exact HasSectionsArtinRees.of_mono A Z _ φ hfin
    (HasSectionsArtinRees.modulePushforward A ρ' hρ I _
      (hasSectionsArtinRees_unit_yoneda A V hVP I))

/-- **Artin-Rees for the global sections of coherent modules on a proper algebraic space over a
Noetherian ring.**  For every coherent `M` on `X` and every `m` there is `n` such that a global
section of `M` dying in `M / (I · 𝒪_X)ⁿ M` lies in `Iᵐ Γ(X, M)`.  Equivalently, the topology on
`Γ(X, M)` defined by the kernels of the reductions is the `I`-adic one, which makes
`Γ(X, M)^∧ ⟶ limₙ Γ(X, M / Iⁿ M)` injective.

The proof is the dévissage of [Stacks, Tag 07US]: the property is closed under extensions by
`AlgebraicGeometry.Space.HasSectionsArtinRees.of_shortExact` ([Stacks, Tag 07UL] and Artin-Rees
for finite modules), and for `i_* 𝓙`, with `𝓙` a sheaf of ideals on a reduced closed subspace
`i : Z ⟶ X`, it passes to `𝓙 ⊆ 𝒪_Z` and then to the direct image along `i`, where
`AlgebraicGeometry.Space.hasSectionsArtinRees_unit_of_isReduced` applies. -/
theorem hasSectionsArtinRees_of_isProper [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    (I : Ideal A) (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : IsCoherent B (Spec (.of A)) hA X.1 X.2 M) :
    HasSectionsArtinRees A X (baseIdealSheaf A X I) I M := by
  have hN := isNoetherian_of_isProper_toBase A X hX
  refine property_of_ideal_pushforward_and_extensions B _ hA X hN
    (fun M => HasSectionsArtinRees A X (baseIdealSheaf A X I) I M) (Or.inr fun N hN0 => ?_)
    (fun E hE h₁ h₂ h₃ R₁ R₃ => ?_) (fun Z hZ hred J => ?_) M hM
  · intro m
    refine ⟨0, fun s _ => ?_⟩
    have : Subsingleton ((sectionsOverBase A B hA X.1 X.2).obj N) :=
      ModuleCat.subsingleton_of_isZero ((sectionsOverBase A B hA X.1 X.2).map_isZero hN0)
    rw [Subsingleton.elim s 0]
    exact Submodule.zero_mem _
  · exact HasSectionsArtinRees.of_shortExact A X _ hN (isQuasicoherentOnSite_baseIdealSheaf A X I)
      (fun U a ha => chartBaseRingHom_mem_baseIdealSheaf A X ha U) E hE h₁ h₂
      (moduleFinite_sectionsOverBase_of_isProper A X hX _ h₃) R₁ R₃
  · let Zs := closedSubfunctorSpace B _ hA hZ
    let i := closedSubfunctorι B _ hA hZ
    have hZp := isProper_toBase_closedSubfunctorSpace A hX hZ
    refine HasSectionsArtinRees.modulePushforward A i hZ.2.1 I _ ?_
    exact @HasSectionsArtinRees.of_mono A _ B hA Zs (baseIdealSheaf A Zs I) _ I _ _ J.1.ι
      (inferInstanceAs (Mono J.1.ι))
      (moduleFinite_sectionsOverBase_unit_of_isReduced A Zs hZp hred.1)
      (hasSectionsArtinRees_unit_of_isReduced A Zs hZp hred.1 I)

end AlgebraicGeometry.Space
