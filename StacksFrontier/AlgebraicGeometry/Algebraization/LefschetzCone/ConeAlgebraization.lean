module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeModel
public import StacksFrontier.AlgebraicGeometry.Algebraization.GradedPresentationAlgebraization

/-!
# Algebraizing a coherent formal module on `P` through the punctured cone

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L` for which the canonical morphism
`X ⟶ Proj A`, `A = Γ_*(X, L)`, is an isomorphism and `A` is Noetherian, let `s` be a global
section of `L`, `f ∈ A₁` its image and `𝓘` the ideal of the zero scheme of `s`. Let `(ℱₙ)` be an
object of `Coh(X, 𝓘)` whose graded modules of twisted sections `Tₙ = Γ_*(X, L, ℱₙ)` are finite.

The sheaves on the punctured cone `U` of the quotients `Tₙ / fⁿ⁺¹ Tₙ` form an object `(ℱ_U,ₙ)` of
`Coh(U, f𝒪_U)` (`Stacks.LefschetzCone.isFiniteModuleModel_truncatedSystem`). If it extends
canonically to `Spec A`, then `(ℱₙ)` is the completion of a coherent `𝒪_X`-module: the graded
algebraization of Stacks 0EL4 produces a finite graded `A`-module `N`, and `Φ : M ↦ M̃|_X` carries
the adic quotients of `N` to the completion of `Ñ|_X` and the system `(Tₙ / fⁿ⁺¹ Tₙ)` to `(ℱₙ)`.

This is the part of the proof of Stacks 0EL5 after the canonical extension (Stacks 0EJI) has been
established.

## Main definitions

* `Stacks.LefschetzCone.twistedSectionsSystem`: the system `(Γ_*(X, L, ℱₙ))`.
* `Stacks.LefschetzCone.coneSystem`: the object `(ℱ_U,ₙ)` of `Coh(U, f𝒪_U)`.

## Main results

* `Stacks.LefschetzCone.isCompletionOfCoherent_of_canonicallyExtends`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization Pointwise

universe u

namespace Stacks.LefschetzCone

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)] (s : Γ(L, ⊤))

/-- An inverse system of coherent modules, as quasi-coherent modules. -/
abbrev quasicoherentSystem (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n, (F.obj n).IsCoherent) :
    ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X :=
  ObjectProperty.lift _ F fun n => by
    have := hF n
    exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (F.obj n)).1

/-- **The system `(Γ_*(X, L, ℱₙ))`** of graded modules of twisted sections. -/
abbrev twistedSectionsSystem (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n, (F.obj n).IsCoherent) :
    ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L) :=
  quasicoherentSystem F hF ⋙ ObjectProperty.ι _ ⋙
    Stacks.SectionRingProjQuasicoherent.gradedTwistedSectionsFunctor L

/-- `Φ(Γ_*(X, L, ℱₙ)) ≅ ℱₙ`, as inverse systems. -/
def twistedSectionsSystemIso (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n, (F.obj n).IsCoherent) :
    twistedSectionsSystem L F hF ⋙ restrictedTildeFunctor L hL ≅ F :=
  Functor.isoWhiskerLeft _ (show sheafFunctor L hL ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ≅
        restrictedTildeFunctor L hL from
      ObjectProperty.liftCompιIso _ _ (isQuasicoherent_restrictedTilde L hL)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      sheafFunctorTwistedSectionsIso L hL (quasicoherentSystem F hF) ≪≫
        ObjectProperty.liftCompιIso _ _ _

/-- `Φ(N) ⟶ Φ(N / fᵏN)` is an isomorphism when `𝓘ᵏ Φ(N) = 0`. -/
theorem isIso_map_powQuotientπ (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ)
    (h : Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
      (restrictedTilde L hL N) = ⊥) :
    IsIso ((restrictedTildeFunctor L hL).map (powQuotientπ L s N k)) := by
  have h1 : (restrictedTildeFunctor L hL).map (powQuotientπ L s N k) =
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
        (restrictedTilde L hL N)).ι ≫ (powQuotientIso L hL s N k).inv :=
    (Iso.eq_comp_inv _).2 (map_powQuotientπ_powQuotientIso_hom L hL s N k)
  have h2 := Stacks.Algebraization.isIso_cokernel_π_of_idealPowerMultiple_eq_bot _ _ _ h
  rw [h1]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Iso.isIso_inv _)

/-- `Φ(Tₙ / fⁿ⁺¹ Tₙ) ≅ Φ(Tₙ)` as inverse systems, when `(Φ(Tₙ))` is a coherent adic system along
the zero scheme of `s`. -/
def truncatedSystemSheafIso (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) :
    truncatedSystem L s T ⋙ restrictedTildeFunctor L hL ≅ T ⋙ restrictedTildeFunctor L hL :=
  (NatIso.ofComponents (F := T ⋙ restrictedTildeFunctor L hL)
    (G := truncatedSystem L s T ⋙ restrictedTildeFunctor L hL) (fun n => @asIso _ _ _ _
    ((restrictedTildeFunctor L hL).map (powQuotientπ L s (T.obj n) (n.unop + 1)))
    (isIso_map_powQuotientπ L hL s (T.obj n) (n.unop + 1) (hT.idealPowerMultiple_eq_bot n.unop)))
    (fun {n m} f => ((restrictedTildeFunctor L hL).map_comp _ _).symm.trans
      ((congrArg (restrictedTildeFunctor L hL).map
        (show T.map f ≫ powQuotientπ L s (T.obj m) (m.unop + 1) =
          powQuotientπ L s (T.obj n) (n.unop + 1) ≫ (truncatedSystem L s T).map f from
          GradedModuleCat.hom_ext (LinearMap.ext fun _ => rfl))).trans
        ((restrictedTildeFunctor L hL).map_comp _ _)))).symm

variable [IsNoetherianRing (sectionRing L)] [IsLocallyNoetherian X]

omit [IsNoetherianRing (sectionRing L)] [IsLocallyNoetherian X] in
/-- The terms of a coherent adic system are coherent, indexed by `ℕᵒᵖ`. -/
theorem isCoherent_obj (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s)) (n : ℕᵒᵖ) :
    (F.obj.obj n).IsCoherent :=
  F.property.isCoherent n.unop

omit [IsNoetherianRing (sectionRing L)] in
/-- `(Γ_*(X, L, ℱₙ))` has sheaves forming a coherent adic system along the zero scheme. -/
theorem isCoherentAdicSystem_twistedSectionsSystem
    (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s)) :
    Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (twistedSectionsSystem L F.obj (isCoherent_obj L s F) ⋙ restrictedTildeFunctor L hL) :=
  Stacks.Coherent.isCoherentAdicSystem_of_iso _
    (twistedSectionsSystemIso L hL F.obj (isCoherent_obj L s F)).symm F.property

/-- **The object `(ℱ_U,ₙ)` of `Coh(U, f𝒪_U)`** on the punctured cone attached to an object of
`Coh(X, 𝓘)` with finite modules of twisted sections: the sheaves of `Γ_*(X, L, ℱₙ) / fⁿ⁺¹`. -/
def coneSystem (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L)
      (Stacks.TwistedSections.twistModule (F.obj.obj (op n)) L)) :
    Stacks.Coherent.CoherentAdicSystems
      (Stacks.Algebraization.idealOnOpen (coneSituation L s)) :=
  Stacks.Algebraization.coherentAdicSystemOfFiniteModuleModel (coneSituation L s)
    (truncatedSystem L s (twistedSectionsSystem L F.obj (isCoherent_obj L s F)) ⋙
      GradedModuleCat.toModuleCat (grading L))
    (isFiniteModuleModel_truncatedSystem L s hL _
      (isCoherentAdicSystem_twistedSectionsSystem L hL s F) hfin)

/-- **Algebraization through the punctured cone.** An object of `Coh(X, 𝓘)` with finite modules
of twisted sections whose system `(ℱ_U,ₙ)` on the punctured cone extends canonically to `Spec A`
is the completion of a coherent `𝒪_X`-module. -/
public theorem isCompletionOfCoherent_of_canonicallyExtends
    (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L)
      (Stacks.TwistedSections.twistModule (F.obj.obj (op n)) L))
    (hext : Stacks.Algebraization.CanonicallyExtends (coneSituation L s)
      (coneSystem L hL s F hfin)) :
    Stacks.Algebraization.IsCompletionOfCoherent (zeroScheme X L s) F := by
  set T := twistedSectionsSystem L F.obj (isCoherent_obj L s F) with hTdef
  have hT := isCoherentAdicSystem_twistedSectionsSystem L hL s F
  have hpres : Nonempty ((coneSystem L hL s F hfin).obj ≅
      truncatedSystem L s T ⋙ GradedModuleCat.toModuleCat (grading L) ⋙
        tilde.functor (.of (coneSituation L s).A) ⋙
          Scheme.Modules.restrictFunctor (coneSituation L s).U.ι) :=
    ⟨(Iso.refl _ : (coneSystem L hL s F hfin).obj ≅
        (truncatedSystem L s T ⋙ GradedModuleCat.toModuleCat (grading L)) ⋙
          (tilde.functor (.of (coneSituation L s).A) ⋙
            Scheme.Modules.pullback (coneSituation L s).U.ι)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (Scheme.Modules.restrictFunctorIsoPullback (coneSituation L s).U.ι).symm))⟩
  have hΦN : ∀ N : GradedModuleCat.{u, u, u} (grading L),
      Module.Finite (coneSituation L s).A N.carrier →
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        Nonempty ((GradedModuleCat.adicQuotients (grading L) N (coneSituation L s).I
            (isHomogeneous_span_sectionElt L s) ⋙ sheafFunctor L hL) ⋙ ObjectProperty.ι _ ≅
          ((Stacks.Algebraization.completionFunctor X (zeroScheme X L s)).obj G).obj) := by
    intro N hN
    have : Module.Finite (sectionRing L) N.carrier := hN
    exact ⟨⟨restrictedTilde L hL N, isCoherent_restrictedTilde L hL N⟩,
      ⟨adicQuotientsIsoCompletion L hL s N (isCoherent_restrictedTilde L hL N)⟩⟩
  have hΦM : Nonempty ((truncatedSystem L s T ⋙ sheafFunctor L hL) ⋙ ObjectProperty.ι _ ≅
      F.obj) :=
    ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (show sheafFunctor L hL ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ≅
            restrictedTildeFunctor L hL from
        ObjectProperty.liftCompιIso _ _ (isQuasicoherent_restrictedTilde L hL)) ≪≫
      truncatedSystemSheafIso L hL s T hT ≪≫ twistedSectionsSystemIso L hL F.obj _⟩
  exact Stacks.Algebraization.isCompletionOfCoherent_of_gradedPresentation (coneSituation L s)
    (𝒜 := grading L) rfl (isHomogeneous_span_sectionElt L s) (truncatedSystem L s T)
    (coneSystem L hL s F hfin) hpres hext (zeroScheme X L s) F (sheafFunctor L hL)
    (isInvertedBy_sheafFunctor L hL) hΦN hΦM

end Monoidal

end Stacks.LefschetzCone

end
